{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE MultiParamTypeClasses      #-}

module Cardano.Shell.Launcher
    ( WalletMode (..)
    , WalletRunner (..)
    , walletRunnerProcess
    , LoggingDependencies (..)
    -- * Functions
    , runLauncher
    , runWalletProcess
    , saveSafeMode
    , readSafeMode
    -- * Critical exports (testing)
    , DaedalusExitCode (..)
    , handleDaedalusExitCode
    , UpdateRunner (..)
    , RestartRunner (..)
    -- * Generating TLS certificates
    , generateTlsCertificates
    , TLSPath(..)
    , TLSError(..)
    -- * Typeclass
    , Isomorphism (..)
    ) where

import           Cardano.Prelude hiding (onException)

import           Prelude (Show (..))
import           Data.Aeson (genericParseJSON, genericToJSON, defaultOptions)
import           Data.Yaml as Y
import qualified System.Process as Process
import           Turtle (system)

import           Cardano.Shell.Configuration (WalletArguments (..),
                                              DaedalusBin (..))
import           Cardano.Shell.Launcher.Types (LoggingDependencies (..))
import           Cardano.Shell.Update.Lib (RemoveArchiveAfterInstall (..),
                                           RunUpdateFunc, UpdaterData (..),
                                           runUpdater)
import           Cardano.X509.Configuration (DirConfiguration (..), certChecks,
                                             certFilename, certOutDir,
                                             TLSConfiguration,
                                             fromConfiguration, genCertificate)
import           Data.X509.Extra (genRSA256KeyPair, validateCertificate,
                                  writeCertificate, writeCredentials)
import           Data.X509.Validation (FailedReason)
import           System.Directory (createDirectoryIfMissing)
import           System.FilePath ((</>))
import           System.Environment (lookupEnv)
import qualified Data.Text as T

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | This is here so we don't mess up the order. It's VERY important.
-- The type that runs the update.
newtype UpdateRunner = UpdateRunner { runUpdate :: IO ExitCode }

-- | There is no way we can show this value.
instance Show UpdateRunner where
    show _ = "<UpdateRunner>"

-- | This type is responsible for launching and re-launching the wallet
-- inside the launcher process.
-- Do we want to restart it in @WalletModeSafe@ or not?
newtype RestartRunner = RestartRunner { runRestart :: WalletMode -> IO ExitCode }

-- | There is no way we can show this value.
instance Show RestartRunner where
    show _ = "<RestartRunner>"

-- | The wallet mode that it's supposed to use.
-- Here we are making the @WalletMode@ explicit.
data WalletMode
    = WalletModeNormal
    | WalletModeSafe
    deriving (Eq, Show)

instance FromJSON WalletMode where
  parseJSON (String "safe") = pure WalletModeSafe
  parseJSON (String "normal") = pure WalletModeNormal
  parseJSON _ = pure WalletModeNormal

instance ToJSON WalletMode where
  toJSON WalletModeNormal = String "normal"
  toJSON WalletModeSafe = String "safe"

data SafeModeConfig = SafeModeConfig
  { smcSafeMode :: WalletMode
  } deriving (Generic, Show)

instance FromJSON SafeModeConfig where
  parseJSON = genericParseJSON defaultOptions

instance ToJSON SafeModeConfig where
  toJSON = genericToJSON defaultOptions

-- | All the important exit codes. Since we cover "other" cases as well, this is a total mapping.
-- That is good.
-- TODO(KS): We could extend this to try to encode some interesting properties about it.
data DaedalusExitCode
    = RunUpdate
    -- ^ Daedalus is ready to run the update system.
    | RestartInGPUSafeMode
    -- ^ Daedalus asks launcher to relaunch Daedalus with GPU safe mode.
    | RestartInGPUNormalMode
    -- ^ Daedalus asks launcher to relaunch Daedalus with normal mode (turn off GPU safe mode).
    | ExitCodeFailure Int
    -- ^ Daedalus wants launcher to exit as well. Unexpected exit code.
    | ExitCodeSuccess
    -- ^ Daedalus "happy path" where it could shut down with success.
    deriving (Eq, Show, Generic)

-- | A simplified typeclass. Maybe we could fetch it from somewhere?
-- This will work for this case.
--
-- from . to == to . from == id
class Isomorphism a b where
    isoFrom     :: a -> b
    isoTo       :: b -> a

-- | A simple instance for converting there and back.
-- The main reason we have it is so we can decouple the implementation.
-- It's a very convenient way to define what exit code means what.
-- Not all that type safe, though, but at least it's defined in one place.
instance Isomorphism DaedalusExitCode ExitCode where

    isoFrom =   \case
        RunUpdate               -> ExitFailure 20
        RestartInGPUSafeMode    -> ExitFailure 21
        RestartInGPUNormalMode  -> ExitFailure 22

        ExitCodeSuccess         -> ExitSuccess
        ExitCodeFailure ef      -> ExitFailure ef

    isoTo   =   \case
        ExitFailure 20          -> RunUpdate
        ExitFailure 21          -> RestartInGPUSafeMode
        ExitFailure 22          -> RestartInGPUNormalMode

        ExitSuccess             -> ExitCodeSuccess
        ExitFailure ef          -> ExitCodeFailure ef


--------------------------------------------------------------------------------
-- Functions
--------------------------------------------------------------------------------

readSafeMode :: FilePath -> IO WalletMode
readSafeMode stateDir = do
  let safeModeConfigFile = getSafeModeConfigPath stateDir
  decoded <- liftIO $ Y.decodeFileEither safeModeConfigFile
  case decoded of
    Right value -> pure $ smcSafeMode value
    Left _      -> pure WalletModeNormal

saveSafeMode :: FilePath -> WalletMode -> IO ()
saveSafeMode stateDir mode = do
  let safeModeConfigFile = getSafeModeConfigPath stateDir
  Y.encodeFile safeModeConfigFile $ SafeModeConfig mode

getSafeModeConfigPath :: FilePath -> FilePath
getSafeModeConfigPath stateDir = stateDir </> "safemode.yaml"

-- | Here we handle the exit codes.
-- It's a simple mapping from exit code to actions that the launcher takes.
--
-- This is much simpler to test, no?
handleDaedalusExitCode
    :: UpdateRunner
    -> RestartRunner
    -> DaedalusExitCode
    -> IO DaedalusExitCode
handleDaedalusExitCode runUpdater' restartWallet = isoTo <<$>> \case
    RunUpdate               -> runUpdate runUpdater' >> runRestart restartWallet WalletModeNormal
    -- Run the actual update, THEN restart launcher.
    -- Do we maybe need to handle the update ExitCode as well?
    RestartInGPUSafeMode    -> runRestart restartWallet WalletModeSafe
    -- Enable safe mode (GPU safe mode).
    RestartInGPUNormalMode  -> runRestart restartWallet WalletModeNormal
    -- Disable safe mode (GPU safe mode).
    ExitCodeSuccess         -> return ExitSuccess
    -- All is well, exit "mucho bien".
    ExitCodeFailure ef      -> return $ ExitFailure ef
    -- Some other unexpected error popped up.

-- | Wallet runner type.
-- I give you the path to the wallet, it's arguments and you execute it
-- and return me the @ExitCode@.
newtype WalletRunner = WalletRunner
    { runWalletSystemProcess :: DaedalusBin -> WalletArguments -> IO ExitCode
    }

-- | Launching the wallet.
-- For now, this is really light since we don't know whether we will reuse the
-- older configuration and if so, which parts of it.
-- We passed in the bare minimum and if we require anything else, we will add it.
runWalletProcess
    :: LoggingDependencies
    -> WalletMode
    -> DaedalusBin
    -> WalletRunner
    -> RunUpdateFunc
    -> UpdaterData
    -> FilePath
    -> IO ExitCode
runWalletProcess
    logDep
    walletMode
    daedalusBin
    walletRunner
    runUpdateFunc
    updaterData
    stateDir = do

    -- Parametrized by @WalletMode@ so we can change it on restart depending
    -- on the Daedalus exit code.
    let restart :: WalletMode -> IO ExitCode
        restart =  \walletMode' -> do
              saveSafeMode stateDir walletMode'
              runWalletProcess
                        logDep
                        walletMode'
                        daedalusBin
                        walletRunner
                        runUpdateFunc
                        updaterData
                        stateDir

    electronExtraArgv <- do
      lookupEnv "ELECTRON_EXTRA_ARGV" >>= \case
        Nothing -> pure []
        Just xs -> pure . T.splitOn "\n" . T.pack $ xs

    -- Additional arguments we need to pass if it's a SAFE mode.
    let walletSafeModeArgs :: WalletArguments
        walletSafeModeArgs = WalletArguments ([ "--safe-mode" ] ++ electronExtraArgv)

    -- Daedalus safe mode.
    let walletArgs :: WalletArguments
        walletArgs =    if walletMode == WalletModeSafe
                            then walletSafeModeArgs
                            else WalletArguments electronExtraArgv

    logNotice logDep $ "Starting the wallet with arguments: " <> Cardano.Prelude.show walletArgs

    -- create the wallet process
    walletExitStatus <- runWalletSystemProcess walletRunner daedalusBin walletArgs

    logNotice logDep $ "Wallet exited with exitcode: " <> Cardano.Prelude.show walletExitStatus

    -- Let us map the interesting commands into a very simple "language".
    let exitCode :: DaedalusExitCode
        exitCode = isoTo walletExitStatus

    let msg = case exitCode of
            RunUpdate ->
                "Running the update system"
            RestartInGPUNormalMode ->
                "Restart Daedalus in normal mode"
            RestartInGPUSafeMode ->
                "Restart Daedalus in GPU safe mode"
            ExitCodeSuccess ->
                "Daedalus exited with ExitSuccess, will shutdown cardano-launcher"
            ExitCodeFailure af -> mconcat
                [ "Daedalus exited with ExitFailure "
                , Cardano.Prelude.show af
                , ", will shutdown cardano-launcher"
                ]

    logNotice logDep $ msg

    -- Here we can interpret what that simple "language" means. This allows us to "cut"
    -- through the function and separate it. When we decouple it, we can test parts in isolation.
    -- We separate the description of the computation, from the computation itself.
    -- There are other ways of doing this, of course.
    isoFrom <$> handleDaedalusExitCode
        (UpdateRunner $ runUpdater logDep RemoveArchiveAfterInstall runUpdateFunc updaterData)
        (RestartRunner restart)
        exitCode


-- | Create the wallet runner proces which will actually run the wallet.
walletRunnerProcess :: WalletRunner
walletRunnerProcess = WalletRunner $ \daedalusBin walletArgs ->
    system (createProc Process.Inherit daedalusBin walletArgs) mempty
  where
    -- | The creation of the process.
    createProc
        :: Process.StdStream
        -> DaedalusBin
        -> WalletArguments
        -> Process.CreateProcess
    createProc stdStream (DaedalusBin commandPath) (WalletArguments commandArguments) =
        (Process.proc (toS commandPath) (map toS commandArguments))
            { Process.std_in    = Process.CreatePipe
            , Process.std_out   = stdStream
            , Process.std_err   = stdStream
            }

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

newtype TLSPath = TLSPath { getTLSFilePath :: FilePath }
    deriving (Eq, Show)

--------------------------------------------------------------------------------
-- Functions
--------------------------------------------------------------------------------

-- | The function that runs the launcher once everything is set up!
runLauncher
    :: LoggingDependencies
    -> WalletRunner
    -> DaedalusBin
    -> RunUpdateFunc
    -> UpdaterData
    -> FilePath
    -> IO ExitCode
runLauncher loggingDependencies walletRunner daedalusBin runUpdateFunc updaterData stateDir = do
        safeMode <- readSafeMode stateDir

        -- In the case the user wants to avoid installing the update now, we
        -- run the update (if there is one) when we have it downloaded.
        void $ runUpdater
            loggingDependencies
            RemoveArchiveAfterInstall
            runUpdateFunc
            updaterData

        -- You still want to run the wallet even if the update fails
        runWalletProcess
            loggingDependencies
            safeMode
            daedalusBin
            walletRunner
            runUpdateFunc
            updaterData
            stateDir

-- | Generation of the TLS certificates.
-- This just covers the generation of the TLS certificates and nothing else.
generateTlsCertificates
    :: LoggingDependencies
    -> TLSConfiguration
    -> TLSPath
    -> IO (Either TLSError ())
generateTlsCertificates externalDependencies' tlsConfig (TLSPath tlsPath) = runExceptT $ do

    let tlsServer = tlsPath </> "server"
    let tlsClient = tlsPath </> "client"

    -- Create the directories.
    liftIO $ do
        logInfo externalDependencies' $ "Generating the certificates!"
        createDirectoryIfMissing True tlsPath
        createDirectoryIfMissing True tlsServer
        createDirectoryIfMissing True tlsClient

        -- Generate the certificates.
    generateCertificates tlsServer tlsClient
  where
    -- The generation of the certificates. More or less copied from
    -- `cardano-sl`.
    generateCertificates :: FilePath -> FilePath -> ExceptT TLSError IO ()
    generateCertificates tlsServer' tlsClient = do
        let outDirectories :: DirConfiguration -- ^ Output directories configuration
            outDirectories = DirConfiguration
                { outDirServer  = tlsServer'
                , outDirClients = tlsClient
                , outDirCA      = Nothing
                }

        -- From configuration
        (caDesc, descs) <-
            liftIO $ fromConfiguration tlsConfig outDirectories genRSA256KeyPair <$> genRSA256KeyPair

        let caName      = certFilename caDesc

        let serverHost  = "localhost"
        let serverPort  = ""

        -- Generation of the certificate
        (caKey, caCert) <- liftIO $ genCertificate caDesc

        case certOutDir caDesc of
            Nothing  -> return ()
            Just dir -> liftIO $ writeCredentials (dir </> caName) (caKey, caCert)

        forM_ descs $ \desc -> do
            (key, cert) <- liftIO $ genCertificate desc
            failedReasons <- liftIO $ validateCertificate
                caCert
                (certChecks desc)
                (serverHost, serverPort)
                cert
            when (not . null $ failedReasons) $ throwError (CannotGenerateTLS failedReasons)
            liftIO $ do
                writeCredentials (certOutDir desc </> certFilename desc) (key, cert)
                writeCertificate (certOutDir desc </> caName) caCert

-- | Error that can be thrown when generating TSL certificates
data TLSError =
      CertConfigNotFound FilePath
    -- ^ FilePath to configuration file is invalid
    | CannotGenerateTLS [FailedReason]
    -- ^ Generation of TLS certificates failed dues to following reasons
    | InvalidKey Text
    -- ^ Given key was invalid therefore @decodeConfigFile@ threw exception
    | TLSDirectoryNotFound FilePath
    -- ^ TLS path does not exist
    deriving (Eq)

instance Show TLSError where
    show = \case
        CannotGenerateTLS reasons ->
            "Couldn't generate TLS certificates due to: " <> Prelude.show reasons

        CertConfigNotFound filepath ->
            "Cert configuration file was not found on: " <> Prelude.show filepath

        InvalidKey key ->
            "Cert configuration key value was invalid: " <> Prelude.show key

        TLSDirectoryNotFound path ->
            "Given TLS path does not exist: " <> Prelude.show path

