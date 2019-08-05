{-# LANGUAGE LambdaCase      #-}
{-# LANGUAGE RankNTypes      #-}
{-# LANGUAGE RecordWildCards #-}

module Main where

import           Cardano.Prelude
import qualified Prelude

import           System.Directory (createDirectoryIfMissing, doesFileExist)
import           System.FilePath ((</>))

import qualified System.Process as Process
import           Turtle (system)

import           Formatting (bprint, build, formatToString)
import           Formatting.Buildable (Buildable (..))

import           Control.Exception.Safe (throwM)
import           Cardano.Shell.Update.Lib (UpdaterData(..), runUpdater)
import           Cardano.X509.Configuration (ConfigurationKey (..),
                                             DirConfiguration (..), certChecks,
                                             certFilename, certOutDir,
                                             decodeConfigFile,
                                             fromConfiguration, genCertificate)
import           Data.X509.Extra (failIfReasons, genRSA256KeyPair,
                                  validateCertificate, writeCertificate,
                                  writeCredentials)

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Launcher configuration
data LauncherConfig = LauncherConfig
    { lcfgFilePath          :: !Text -- We really need @FilePath@ here.
    , lcfgKey               :: !Text
    , lcfgSystemStart       :: !(Maybe Integer)
    , lcfgSeed              :: !(Maybe Integer)
    } deriving (Eq, Show)

newtype WalletArguments = WalletArguments
    { getWalletArguments    :: [Text]
    } deriving (Eq, Show)

newtype WalletPath = WalletPath
    { getWalletPath         :: Text
    } deriving (Eq, Show)

--------------------------------------------------------------------------------
-- Main
--------------------------------------------------------------------------------

main :: IO ExitCode
main = do

    let launcherConfig :: LauncherConfig
        launcherConfig = LauncherConfig
            { lcfgFilePath    = "./configuration/cert-configuration.yaml"
            , lcfgKey         = "dev"
            , lcfgSystemStart = Nothing
            , lcfgSeed        = Nothing
            }

    -- Really no clue what to put there and how will the wallet work.
    let walletPath :: WalletPath
        walletPath = WalletPath "stack"

    let walletArgs :: WalletArguments
        walletArgs = WalletArguments ["exec", "cardano-shell-exe"]

    -- | Yes, this is something we probably need to replace with actual loggging.
    let externalDependencies :: ExternalDependencies
        externalDependencies = ExternalDependencies
            { logInfo       = putTextLn
            , logError      = putTextLn
            , logNotice     = putTextLn
            }

    -- | If we need to, we first check if there are certificates so we don't have
    -- to generate them. Since the function is called `generate...`, that's what
    -- it does, it generates the certificates.
    generateTlsCertificates
        externalDependencies
        launcherConfig
        (TLSPath "./configuration/") -- where to generate the certificates

    update (runWallet externalDependencies walletPath walletArgs)
  where
    update :: IO ExitCode -> IO ExitCode
    update runWalletFunc = do
        updaterExists <- doesFileExist (udPath testUpdaterData)
        if updaterExists
            then do       
                updaterExitCode <- runUpdater testUpdaterData
                case updaterExitCode of
                    ExitSuccess -> do
                    -- With the exit code
                        exitCode <- runWalletFunc
                        case exitCode of
                            -- This will run the updater and relaunch the wallet
                            ExitFailure 20 -> update runWalletFunc
                            _              -> return $ exitCode
                    _ -> return updaterExitCode
            else runWalletFunc

-- | Launching the wallet.
-- For now, this is really light since we don't know whether we will reuse the
-- older configuration and if so, which parts of it.
-- We passed in the bare minimum and if we require anything else, we will add it.
runWallet
    :: ExternalDependencies
    -> WalletPath
    -> WalletArguments
    -> IO ExitCode
runWallet ed@ExternalDependencies{..} walletPath walletArguments = do
    logNotice "Starting the wallet"

    -- create the wallet process
    walletExitStatus <- system (createProc Process.Inherit walletPath walletArguments) mempty

    case walletExitStatus of
        ExitFailure 21 -> do
            logNotice "The wallet has exited with code 21"
            --logInfo "Switching Configuration to safe mode"
            --saveSafeMode lo True
            runWallet ed walletPath walletArguments

        ExitFailure 22 -> do
            logNotice "The wallet has exited with code 22"
            --logInfo "Switching Configuration to normal mode"
            --saveSafeMode lo False
            runWallet ed walletPath walletArguments

        -- Otherwise, return the exit status.
        _ -> pure walletExitStatus
  where
    -- | The creation of the process.
    createProc
        :: Process.StdStream
        -> WalletPath
        -> WalletArguments
        -> Process.CreateProcess
    createProc stdStream (WalletPath commandPath) (WalletArguments commandArguments) =
        (Process.proc (strConv Lenient commandPath) (map (strConv Lenient) commandArguments))
            { Process.std_in    = Process.CreatePipe
            , Process.std_out   = stdStream
            , Process.std_err   = stdStream
            }

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

data ExternalDependencies = ExternalDependencies
    { logInfo   :: Text -> IO ()
    , logError  :: Text -> IO ()
    , logNotice :: Text -> IO ()
    }

newtype X509ToolPath = X509ToolPath { getX509ToolPath :: FilePath }
    deriving (Eq, Show)

newtype TLSPath = TLSPath { getTLSFilePath :: FilePath }
    deriving (Eq, Show)

--------------------------------------------------------------------------------
-- Exceptions
--------------------------------------------------------------------------------

data LauncherExceptions
    = CannotGenerateTLS
    deriving (Eq)

instance Buildable LauncherExceptions where
    build = \case
        CannotGenerateTLS -> bprint "Couldn't generate TLS certificates; \
            \ Daedalus wallet won't work without TLS. Please check your configuration \
            \ and make sure you aren't already running an instance of Daedalus wallet."

instance Show LauncherExceptions where
    show = formatToString Formatting.build

instance Exception LauncherExceptions

--------------------------------------------------------------------------------
-- Functions
--------------------------------------------------------------------------------

-- | Utility function.
textToFilePath :: Text -> FilePath
textToFilePath = strConv Strict

-- | Generation of the TLS certificates.
-- This just covers the generation of the TLS certificates and nothing else.
generateTlsCertificates :: ExternalDependencies -> LauncherConfig -> TLSPath -> IO ()
generateTlsCertificates externalDependencies launcherConfig (TLSPath tlsPath) = do

    let tlsServer = tlsPath </> "server"
    let tlsClient = tlsPath </> "client"

    logInfo externalDependencies $ "Generating the certificates!"

    -- Create the directories.
    createDirectoryIfMissing True tlsServer
    createDirectoryIfMissing True tlsClient

    -- Generate the certificates.
    generateCertificates launcherConfig tlsServer tlsClient
        `onException` throwM CannotGenerateTLS
        -- ^ unfortunate since we gobble up the real cause,
        -- but we want the client to have a nice message

  where
    -- | The generation of the certificates. More or less copied from
    -- `cardano-sl`.
    generateCertificates :: LauncherConfig -> FilePath -> FilePath -> IO ()
    generateCertificates launcherConfig' tlsServer' tlsClient = do

        let cfgFilePath = lcfgFilePath launcherConfig'
        let cfgKey      = lcfgKey launcherConfig'

        let outDirectories :: DirConfiguration -- ^ Output directories configuration
            outDirectories = DirConfiguration
                { outDirServer  = tlsServer'
                , outDirClients = tlsClient
                , outDirCA      = Nothing -- TODO(KS): AFAIK, we don't output the CA.
                }

        -- | Configuration key within the config file
        let configKey :: ConfigurationKey
            configKey = ConfigurationKey . textToFilePath $ cfgKey

        let configFile :: FilePath
            configFile = textToFilePath cfgFilePath

        -- | TLS configuration
        tlsConfig <- decodeConfigFile configKey configFile

        -- | From configuraiton
        (caDesc, descs) <-
            fromConfiguration tlsConfig outDirectories genRSA256KeyPair <$> genRSA256KeyPair

        let caName      = certFilename caDesc

        let serverHost  = "localhost"
        let serverPort  = ""

        -- | Generation of the certificate
        (caKey, caCert) <- genCertificate caDesc

        case certOutDir caDesc of
            Nothing  -> return ()
            Just dir -> writeCredentials (dir </> caName) (caKey, caCert)

        forM_ descs $ \desc -> do
            (key, cert) <- genCertificate desc
            failIfReasons =<< validateCertificate
                caCert
                (certChecks desc)
                (serverHost, serverPort)
                cert
            writeCredentials (certOutDir desc </> certFilename desc) (key, cert)
            writeCertificate (certOutDir desc </> caName) caCert

testUpdaterData :: UpdaterData
testUpdaterData =
    UpdaterData
        "./test/testUpdater.sh"
        []
        ""
