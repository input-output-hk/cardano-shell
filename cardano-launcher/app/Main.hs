{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}

module Main where

import           Cardano.Prelude
import qualified Prelude

import           System.Directory (createDirectoryIfMissing)
import           System.Exit (exitWith)
import           System.FilePath ((</>))

import           Formatting (bprint, build, formatToString)
import           Formatting.Buildable (Buildable (..))

import           Cardano.Shell.Launcher (ExternalDependencies (..),
                                         LauncherConfig (..),
                                         WalletArguments (..), WalletMode (..),
                                         WalletPath (..), runWallet)
import           Cardano.Shell.Update.Lib (UpdaterData (..), runUpdater)
import           Cardano.X509.Configuration (ConfigurationKey (..),
                                             DirConfiguration (..), certChecks,
                                             certFilename, certOutDir,
                                             decodeConfigFile,
                                             fromConfiguration, genCertificate)
import           Control.Exception.Safe (throwM)
import           Data.X509.Extra (failIfReasons, genRSA256KeyPair,
                                  validateCertificate, writeCertificate,
                                  writeCredentials)

--------------------------------------------------------------------------------
-- Main
--------------------------------------------------------------------------------

-- | Yes, this is something we probably need to replace with actual loggging.
-- If we want. Otherwise, we can print out to console out just for launcher configs.
externalDependencies :: ExternalDependencies
externalDependencies = ExternalDependencies
    { logInfo            = putTextLn
    , logError           = putTextLn
    , logNotice          = putTextLn
    }

-- | Main function.
main :: IO ()
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
        walletPath = WalletPath "./test/testDaedalusFrontend.sh"

    let walletArgs :: WalletArguments
        walletArgs = WalletArguments ["./launcher-config.yaml"]

    -- | This is a mock for updater, need to replace with actual data
    let updaterData :: UpdaterData
        updaterData = UpdaterData
            { udPath = "./test/testUpdater.sh"
            , udArgs = ["main"]
            , udArchivePath = ""
            }

    -- | If we need to, we first check if there are certificates so we don't have
    -- to generate them. Since the function is called `generate...`, that's what
    -- it does, it generates the certificates.
    generateTlsCertificates
        externalDependencies
        launcherConfig
        (TLSPath "./configuration/") -- where to generate the certificates

    void $ runUpdater updaterData -- On windows, process dies here
    -- You still want to run the wallet even if the update fails
    exitCode <- runWallet externalDependencies WalletModeNormal walletPath walletArgs updaterData
    exitWith exitCode

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

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
generateTlsCertificates externalDependencies' launcherConfig (TLSPath tlsPath) = do

    let tlsServer = tlsPath </> "server"
    let tlsClient = tlsPath </> "client"

    logInfo externalDependencies' $ "Generating the certificates!"

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
