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
    , runWalletProcess
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
import qualified System.Process as Process
import           Turtle (system)

import           Cardano.Shell.Configuration (ConfigurationOptions (..),
                                              WalletArguments (..),
                                              WalletPath (..))
import           Cardano.Shell.Types (LoggingDependencies (..))
import           Cardano.Shell.Update.Lib (UpdaterData (..),
                                           runDefaultUpdateProcess, runUpdater)
import           Cardano.X509.Configuration (ConfigurationKey (..),
                                             DirConfiguration (..), certChecks,
                                             certFilename, certOutDir,
                                             decodeConfigFile,
                                             fromConfiguration, genCertificate)
import           Control.Exception.Safe (onException)
import           Data.X509.Extra (genRSA256KeyPair, validateCertificate,
                                  writeCertificate, writeCredentials)
import           Data.X509.Validation (FailedReason)
import           System.Directory (createDirectoryIfMissing, doesFileExist)
import           System.FilePath ((</>))

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
    { runWalletSystemProcess :: WalletPath -> WalletArguments -> IO ExitCode
    }

-- | Launching the wallet.
-- For now, this is really light since we don't know whether we will reuse the
-- older configuration and if so, which parts of it.
-- We passed in the bare minimum and if we require anything else, we will add it.
runWalletProcess
    :: LoggingDependencies
    -> WalletMode
    -> WalletPath
    -> WalletArguments
    -> WalletRunner
    -> UpdaterData
    -> IO ExitCode
runWalletProcess logDep walletMode walletPath walletArguments walletRunner updaterData = do

    -- Parametrized by @WalletMode@ so we can change it on restart depending
    -- on the Daedalus exit code.
    let restart :: WalletMode -> IO ExitCode
        restart =  \walletMode' -> runWalletProcess
                        logDep
                        walletMode'
                        walletPath
                        walletArguments
                        walletRunner
                        updaterData

    -- Additional arguments we need to pass if it's a SAFE mode.
    let walletSafeModeArgs :: WalletArguments
        walletSafeModeArgs = WalletArguments [ "--safe-mode", "--disable-gpu", "--disable-d3d11" ]

    -- Daedalus safe mode.
    let walletArgs :: WalletArguments
        walletArgs =    if walletMode == WalletModeSafe
                            then walletArguments <> walletSafeModeArgs
                            else walletArguments

    logNotice logDep $ "Starting the wallet"

    -- create the wallet process
    walletExitStatus <- runWalletSystemProcess walletRunner walletPath walletArgs

    -- Let us map the interesting commands into a very simple "language".
    let exitCode :: DaedalusExitCode
        exitCode = isoTo walletExitStatus

    -- Here we can interpret what that simple "language" means. This allows us to "cut"
    -- through the function and separate it. When we decouple it, we can test parts in isolation.
    -- We separate the description of the computation, from the computation itself.
    -- There are other ways of doing this, of course.
    isoFrom <$> handleDaedalusExitCode
        (UpdateRunner $ runUpdater runDefaultUpdateProcess logDep updaterData)
        (RestartRunner restart)
        exitCode


-- | Create the wallet runner proces which will actually run the wallet.
walletRunnerProcess :: WalletRunner
walletRunnerProcess = WalletRunner $ \walletPath walletArgs ->
    system (createProc Process.Inherit walletPath walletArgs) mempty
  where
    -- | The creation of the process.
    createProc
        :: Process.StdStream
        -> WalletPath
        -> WalletArguments
        -> Process.CreateProcess
    createProc stdStream (WalletPath commandPath) (WalletArguments commandArguments) =
        (Process.proc (toS commandPath) (map toS commandArguments))
            { Process.std_in    = Process.CreatePipe
            , Process.std_out   = stdStream
            , Process.std_err   = stdStream
            }

--------------------------------------------------------------------------------
--
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- Not used?
-- newtype X509ToolPath = X509ToolPath { getX509ToolPath :: FilePath }
--     deriving (Eq, Show)

newtype TLSPath = TLSPath { getTLSFilePath :: FilePath }
    deriving (Eq, Show)

--------------------------------------------------------------------------------
-- Functions
--------------------------------------------------------------------------------

-- | Generation of the TLS certificates.
-- This just covers the generation of the TLS certificates and nothing else.
generateTlsCertificates :: LoggingDependencies -> ConfigurationOptions -> TLSPath -> IO (Either TLSError ())
generateTlsCertificates externalDependencies' configurationOptions (TLSPath tlsPath) = runExceptT $ do
    doesCertConfigExist <- liftIO $ doesFileExist (cfoFilePath configurationOptions)
    unless doesCertConfigExist $ throwError . CertConfigNotFound . cfoFilePath $ configurationOptions

    let tlsServer = tlsPath </> "server"
    let tlsClient = tlsPath </> "client"

    -- Create the directories.
    liftIO $ do
        logInfo externalDependencies' $ "Generating the certificates!"
        createDirectoryIfMissing True tlsServer
        createDirectoryIfMissing True tlsClient

        -- Generate the certificates.
    generateCertificates tlsServer tlsClient
  where
    -- | The generation of the certificates. More or less copied from
    -- `cardano-sl`.
    generateCertificates :: FilePath -> FilePath -> ExceptT TLSError IO ()
    generateCertificates tlsServer' tlsClient = do

        let configFile = cfoFilePath configurationOptions
        -- | Configuration key within the config file
        let configKey :: ConfigurationKey
            configKey = ConfigurationKey . textToFilePath . cfoKey $ configurationOptions

        let outDirectories :: DirConfiguration -- ^ Output directories configuration
            outDirectories = DirConfiguration
                { outDirServer  = tlsServer'
                , outDirClients = tlsClient
                , outDirCA      = Nothing -- TODO(KS): AFAIK, we don't output the CA.
                }

        -- | TLS configuration
        tlsConfig <- decodeConfigFile configKey configFile `onException`
            (throwError . InvalidKey . cfoKey $ configurationOptions)

        -- | From configuraiton
        (caDesc, descs) <-
            liftIO $ fromConfiguration tlsConfig outDirectories genRSA256KeyPair <$> genRSA256KeyPair

        let caName      = certFilename caDesc

        let serverHost  = "localhost"
        let serverPort  = ""

        -- | Generation of the certificate
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
    -- | Utility function.
    textToFilePath :: Text -> FilePath
    textToFilePath = strConv Strict

-- | Error that can be thrown when generating TSL certificates
data TLSError =
      CertConfigNotFound FilePath
    -- ^ FilePath to configuration file is invalid
    | CannotGenerateTLS [FailedReason]
    -- ^ Generation of TLS certificates failed dues to following reasons
    | InvalidKey Text
    -- ^ Given key was invalid therefore @decodeConfigFile@ threw exception

instance Show TLSError where
    show = \case
        CannotGenerateTLS reasons -> "Couldn't generate TLS certificates due to: " <> Prelude.show reasons
        CertConfigNotFound filepath -> "Cert configuration file was not found on: " <> Prelude.show filepath
        InvalidKey key -> "Cert configuration key value was invalid: " <> Prelude.show key
