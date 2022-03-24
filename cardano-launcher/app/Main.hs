{-# LANGUAGE CPP        #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}


module Main where

import           Cardano.Prelude hiding (option)
import qualified Prelude

-- Yes, we should use these seldomly but here it seems quite acceptable.
import           Data.IORef (newIORef, readIORef, writeIORef)
import           Data.Text.Lazy.Builder (fromString, fromText)

import           Distribution.System as OS
import           System.Environment (setEnv)
import           System.Exit (exitWith)
import           System.IO.Silently (hSilence)
import           System.Process (proc, waitForProcess, withCreateProcess)

import           Formatting (bprint, build, formatToString)
import           Formatting.Buildable (Buildable (..))

import           Options.Applicative (Parser, ParserInfo, auto, execParser,
                                      fullDesc, header, help, helper, info,
                                      long, metavar, option, optional, progDesc)

import           Cardano.BM.Setup (withTrace)
import qualified Cardano.BM.Trace as Trace
import           Cardano.BM.Tracing

import           Cardano.Shell.Application (ApplicationError (ApplicationAlreadyRunningException),
                                            checkIfApplicationIsRunning)
import           Cardano.Shell.CLI (LauncherOptionPath, getDefaultConfigPath,
                                    getLauncherOptions, launcherArgsParser)
import           Cardano.Shell.Configuration (DaedalusBin (..),
                                              LauncherOptions (..), getDPath,
                                              getUpdaterData,
                                              setWorkingDirectory)
import           Cardano.Shell.Launcher (LoggingDependencies (..), TLSError,
                                         TLSPath (..), WalletRunner (..),
                                         generateTlsCertificates, runLauncher,
                                         walletRunnerProcess)
import           Cardano.Shell.Update.Lib (UpdaterData (..),
                                           runDefaultUpdateProcess)
import           Cardano.X509.Configuration (TLSConfiguration)
import           Control.Exception.Safe (throwM)
import           Control.Exception.Safe as E

import           System.FilePath ((</>))
import           System.IO (hClose)

--------------------------------------------------------------------------------
-- Main
--------------------------------------------------------------------------------

-- | Main function.
main :: IO ()
main = silence $ do

    defaultConfigPath   <- getDefaultConfigPath

    -- The execution of the launcher CLI
    launcherCLI         <- execParser $ cliLauncherCLIParserInfo defaultConfigPath

    putTextLn . show $ launcherCLI

    -- Here we convert the CLI exit codes into "real" exit codes
    let walletTestExitCodes     = map convertCLIExitCodeToReal (fromMaybe [] $ walletExitCodes launcherCLI)
    let updaterTestExitCodes    = map convertCLIExitCodeToReal (fromMaybe [] $ updaterExitCodes launcherCLI)

    -- We create the vars required for syncing access to the exit code list
    walletTestExitCodesMVar     <- newIORef walletTestExitCodes
    updaterTestExitCodesMVar    <- newIORef updaterTestExitCodes

    -- This function either stubs out the wallet exit code or
    -- returns the "real" function.
    let walletExectionFunction =
            WalletRunner $ \daedalusBin walletArguments -> do
                -- Check if we have any exit codes remaining.
                stubExitCodes       <- readIORef walletTestExitCodesMVar
                let currentStubExitCode = head stubExitCodes

                case currentStubExitCode of
                    Just stubExitCode   -> do
                        -- If we have some exit codes remaining then return first and remove it.
                        writeIORef walletTestExitCodesMVar (Prelude.tail stubExitCodes)
                        pure stubExitCode
                    Nothing             ->
                        -- Otherwise run the real deal, the real function.
                        runWalletSystemProcess walletRunnerProcess daedalusBin walletArguments

    -- This function either stubs out the updater exit code or
    -- returns the "real" function.
    let updaterExecutionFunction =
            \filePath arguments -> do
                -- Check if we have any exit codes remaining.
                stubExitCodes       <- readIORef updaterTestExitCodesMVar
                let currentStubExitCode = head stubExitCodes

                case currentStubExitCode of
                    Just stubExitCode   -> do
                        -- If we have some exit codes remaining then return first and remove it.
                        writeIORef updaterTestExitCodesMVar (Prelude.tail stubExitCodes)
                        pure stubExitCode
                    Nothing             ->
                        -- Otherwise run the real deal, the real function.
                        runDefaultUpdateProcess filePath arguments


    logConfig           <- defaultConfigStdout

    -- A safer way to close the tracing.
    withTrace logConfig "launcher" $ \baseTrace -> do

        Trace.logNotice baseTrace "Starting cardano-launcher"

        let loggingDependencies :: LoggingDependencies
            loggingDependencies = LoggingDependencies
                { logInfo       = Trace.logInfo baseTrace
                , logError      = Trace.logError baseTrace
                , logNotice     = Trace.logNotice baseTrace
                }

        setEnv "LC_ALL" "en_GB.UTF-8"
        setEnv "LANG"   "en_GB.UTF-8"

        (launcherOptions, mURL) <- do
            eLauncherOptions <- getLauncherOptions loggingDependencies (launcherConfigPath launcherCLI)
            case eLauncherOptions of
                Left err -> do
                    logErrorMessage baseTrace $
                        "Error occured while parsing configuration file: " <> show err
                    throwM $ LauncherOptionsError (show err)
                Right lo -> pure lo

        let stateDir :: FilePath
            stateDir = loStateDir launcherOptions

        let lockFile = stateDir </> "daedalus_lockfile"
        Trace.logNotice baseTrace $ "Locking file so that multiple applications won't run at same time"
        -- Check if it's locked or not.
        --
        -- XXX: In a special case, when `cardano-launcher` is given a
        -- `mURL` (web+cardano://…) on the command line, we want to
        -- allow the second instance. Then, Daedalus will notify its
        -- first instance to handle this particular URL. This needs to
        -- happen only on Linux and Windows, since macOS has its own
        -- mechanism to notify already running applications to open
        -- URLs, which Electron implements. In such a case, we also
        -- skip TLS setup.
        --
        -- Otherwise, will throw an exception if the application is
        -- already running.
        (isSecondWindowsInstanceWithURL, lockHandle) <- E.try (checkIfApplicationIsRunning lockFile) >>= \case
            Right hndl -> pure (False, Just hndl)
            Left exception@ApplicationAlreadyRunningException ->
                if isJust mURL && (OS.buildOS == OS.Windows || OS.buildOS == OS.Linux) then
                    pure (True, Nothing)
                else
                    throwM exception

        let workingDir = loWorkingDirectory launcherOptions


        -- Every platform will run a script before running the launcher that creates a
        -- working directory, so workingDir should always exist.
        unlessM (setWorkingDirectory workingDir) $ do
            logErrorMessage baseTrace $ "Working directory does not exist: " <> toS workingDir
            throwM . WorkingDirectoryDoesNotExist $ workingDir

        -- Configuration from the launcher options.
        let mTlsConfig :: Maybe TLSConfiguration
            mTlsConfig = if isSecondWindowsInstanceWithURL then Nothing else loTlsConfig launcherOptions

        let daedalusBin :: DaedalusBin
            daedalusBin = getDPath launcherOptions

        let updaterData :: UpdaterData
            updaterData = getUpdaterData launcherOptions


        -- where to generate the certificates
        let mTlsPath :: Maybe TLSPath
            mTlsPath = TLSPath <$> loTlsPath launcherOptions

        -- If the path doesn't exist, then TLS has been disabled!
        case (mTlsPath, mTlsConfig) of
            (Just tlsPath, Just tlsConfig) -> do
                -- | If we need to, we first check if there are certificates so we don't have
                -- to generate them. Since the function is called `generate...`, that's what
                -- it does, it generates the certificates.
                eTLSGeneration <- generateTlsCertificates
                    loggingDependencies
                    tlsConfig
                    tlsPath

                case eTLSGeneration of
                    Left generationError -> do
                        logErrorMessage baseTrace $
                            "Error occured while generating TLS certificates: " <> show generationError
                        throwM $ FailedToGenerateTLS generationError
                    Right _              -> return ()
            _ -> pure () -- TLS generation has been disabled

        -- Finally, run the launcher once everything is set up!
        exitCode <- runLauncher
                        loggingDependencies
                        walletExectionFunction
                        daedalusBin
                        updaterExecutionFunction
                        updaterData
                        stateDir
                        mURL

        -- release the lock on the lock file
        mapM_ hClose lockHandle

        -- Exit the program with exit code.
        exitWith exitCode

--------------------------------------------------------------------------------
-- CLI
--------------------------------------------------------------------------------

-- | The exit code tests.
-- With this we can specify the behaviour of the stubbed wallet or update system.
-- This is a single exit code, but the stubs can contain lists which then execute
-- in the order in which they were defined.
-- Example:
-- $> Prelude.read "[CLIExitCodeFailure 5,CLIExitCodeSuccess]" :: [CLIExitCode]
data CLIExitCode
    = CLIExitCodeSuccess
    | CLIExitCodeFailure Int
    deriving (Eq, Show, Read)

-- | Conversion from the CLI type to an actual @ExitCode@.
convertCLIExitCodeToReal :: CLIExitCode -> ExitCode
convertCLIExitCodeToReal CLIExitCodeSuccess            = ExitSuccess
convertCLIExitCodeToReal (CLIExitCodeFailure exitCode) = ExitFailure exitCode

-- | The launcher CLI options.
data LauncherCLI = LauncherCLI
    { launcherConfigPath :: !LauncherOptionPath
    , walletExitCodes    :: Maybe [CLIExitCode]
    , updaterExitCodes   :: Maybe [CLIExitCode]
    } deriving (Eq, Show)

-- | The top-level CLI parser with description.
cliLauncherCLIParserInfo :: FilePath -> ParserInfo LauncherCLI
cliLauncherCLIParserInfo launcherConfigDefaultPath =
    info (parseLauncherCLI launcherConfigDefaultPath <**> helper)
        ( fullDesc
        <> progDesc "Tool for launching Daedalus"
        <> header "cardano-launcher"
        )

-- | The CLI parser for all the launcher CLI arguments.
parseLauncherCLI :: FilePath -> Parser LauncherCLI
parseLauncherCLI launcherConfigDefaultPath =
    LauncherCLI
        <$> launcherArgsParser launcherConfigDefaultPath
        <*> walletExitCodeCLI
        <*> updaterExitCodeCLI
  where
    -- | CLI for the wallet stub exit codes.
    walletExitCodeCLI :: Parser (Maybe [CLIExitCode])
    walletExitCodeCLI =
        optional $ option auto
            (  long "wallet-exit-codes"
            <> metavar "LIST"
            <> help "Exits codes you want to stub in order of execution."
            )

    -- | CLI for the updater stub exit codes.
    updaterExitCodeCLI :: Parser (Maybe [CLIExitCode])
    updaterExitCodeCLI =
        optional $ option auto
            (  long "updater-exit-codes"
            <> metavar "LIST"
            <> help "Exits codes you want to stub in order of execution."
            )


--------------------------------------------------------------------------------
-- Exceptions
--------------------------------------------------------------------------------

data LauncherExceptions
    = LauncherOptionsError Text
    | WorkingDirectoryDoesNotExist FilePath
    | FailedToGenerateTLS TLSError

instance Buildable LauncherExceptions where
    build = \case
        LauncherOptionsError err -> bprint
               "Error occured during loading configuration file:\n"
            <> fromText err
        WorkingDirectoryDoesNotExist path -> bprint
               "Failed to set working directory because it does not exist: "
            <> fromString path
        FailedToGenerateTLS tlsError -> bprint
               "Failed to generate tls certificate due to error:\n"
            <> fromString (show tlsError)

instance Show LauncherExceptions where
    show = formatToString Formatting.build

instance Exception LauncherExceptions

silence :: IO a -> IO a
silence runAction = case OS.buildOS of
    OS.Windows -> hSilence [stdout, stderr] runAction
    _          -> runAction

-- | Log error message
-- |
-- | On darwin, it will use osascript to emit a error dialog to notify user about
-- | it
-- | https://scriptingosx.com/2018/08/user-interaction-from-bash-scripts/
logErrorMessage :: MonadIO m => Trace m Text -> Text -> m ()
logErrorMessage tracer msg = do
    Trace.logError tracer msg
#ifdef darwin_HOST_OS
    liftIO $ displayErrorDarwin msg
#endif

displayErrorDarwin :: Text -> IO ()
displayErrorDarwin errorMessage = do
    let displayProcess = proc "osascript" ["-e", toS mkErrorMessage]
    void $ withCreateProcess displayProcess (\ _ _ _ ph -> waitForProcess ph)
  where
    mkErrorMessage :: Text
    mkErrorMessage = mconcat
          [ "display dialog "
          , show (errorMessage :: Text)
          , " buttons {\"Ok\"} "
          , "default button 1 with title "
          , show ("Cardano Launcher Error" :: Text)
          ]
