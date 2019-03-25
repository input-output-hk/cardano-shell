{-# LANGUAGE LambdaCase #-}

module Main where

import           Cardano.Prelude
import qualified Prelude

import           System.Directory (createDirectoryIfMissing, doesFileExist)
import           System.FilePath ((</>))

import           Formatting (build, bprint, formatToString)
import           Formatting.Buildable (Buildable (..))

import           Control.Exception.Safe (throwM)

import           Cardano.Shell.Configuration.Types (LauncherConfig (..))

import           Cardano.X509.Configuration (ConfigurationKey (..),
                                             DirConfiguration (..), certChecks,
                                             certFilename, certOutDir,
                                             decodeConfigFile,
                                             fromConfiguration, genCertificate)
import           Data.X509.Extra (failIfReasons, genRSA256KeyPair,
                                  validateCertificate, writeCertificate,
                                  writeCredentials)

--------------------------------------------------------------------------------
-- Main
--------------------------------------------------------------------------------

main :: IO ()
main = do

    let launcherConfig :: LauncherConfig
        launcherConfig = LauncherConfig
            { lcfgFilePath    = "./configuration/"
            , lcfgKey         = "develop"
            , lcfgSystemStart = Nothing
            , lcfgSeed        = Nothing
            }

    generateTlsCertificates launcherConfig (TLSPath "./configuration/")

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
        CannotGenerateTLS -> bprint "Couldn't generate TLS certificates; Daedalus wallet won't work without TLS. Please check your configuration and make sure you aren't already running an instance of Daedalus wallet."

instance Show LauncherExceptions where
    show = formatToString Formatting.build

instance Exception LauncherExceptions

--------------------------------------------------------------------------------
-- Functions
--------------------------------------------------------------------------------

--data ExternalDependencies = ExternalDependencies
logInfo :: Text -> IO ()
logInfo = putTextLn

logError :: Text -> IO ()
logError = putTextLn

-- | Utility function.
textToFilePath :: Text -> FilePath
textToFilePath = strConv Strict

-- | Generation of the TLS certificates.
-- This just covers the generation of the TLS certificates and nothing else.
generateTlsCertificates :: LauncherConfig -> TLSPath -> IO ()
generateTlsCertificates (LauncherConfig cfgFilePath cfgKey _ _) (TLSPath tlsPath) = do --TODO(KS): Fix positional params

    alreadyExists <- liftIO . doesFileExist $ tlsPath

    let tlsServer = tlsPath </> "server"
    let tlsClient = tlsPath </> "client"

    -- If there is no existing file
    unless alreadyExists $ do
        logInfo "Testing"

        createDirectoryIfMissing True tlsServer
        createDirectoryIfMissing True tlsClient
        --phvar <- newEmptyMVar
        --system' phvar process mempty ECertGen
        generateCertificates tlsServer tlsClient
            `onException` throwM CannotGenerateTLS

  where
    generateCertificates :: FilePath -> FilePath -> IO ()
    generateCertificates tlsServer' tlsClient = do
        let outDirectories :: DirConfiguration -- ^ Output directories configuration
            outDirectories = DirConfiguration
                { outDirServer  = tlsServer'
                , outDirClients = tlsClient
                , outDirCA      = Just . textToFilePath $ cfgFilePath -- TODO(KS): Maybe?!!
                }

        -- | Configuration key within the config file
        let configKey :: ConfigurationKey
            configKey = ConfigurationKey . textToFilePath $ cfgKey

        let configFile :: FilePath
            configFile = tlsPath

        tlsConfig <-
            decodeConfigFile configKey configFile

        (caDesc, descs) <-
            fromConfiguration tlsConfig outDirectories genRSA256KeyPair <$> genRSA256KeyPair

        let caName =
                certFilename caDesc

        let serverHost = "localhost"
        let serverPort = ""

        (caKey, caCert) <-
            genCertificate caDesc

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


