{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}

module Main where

import           Cardano.Prelude
import qualified Prelude

import           System.Directory (createDirectoryIfMissing)
import           System.Environment (setEnv)
import           System.Exit (exitWith)
import           System.FilePath ((</>))

import           Formatting (bprint, build, formatToString)
import           Formatting.Buildable (Buildable (..))

import           Cardano.BM.Setup (setupTrace_, shutdown)
import qualified Cardano.BM.Trace as Trace
import           Cardano.BM.Tracing

import           Cardano.Shell.CLI (getLauncherOptions)
import           Cardano.Shell.Configuration (ConfigurationOptions (..),
                                              LauncherOptions (..),
                                              WalletArguments (..),
                                              WalletPath (..), getUpdaterData,
                                              getWPath, getWargs,
                                              setWorkingDirectory)
import           Cardano.Shell.Launcher (LoggingDependencies (..),
                                         WalletMode (..), runWalletProcess,
                                         walletRunnerProcess)
import           Cardano.Shell.Update.Lib (UpdaterData (..),
                                           runDefaultUpdateProcess, runUpdater)
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

-- | Main function.
main :: IO ()
main = do

    setEnv "LC_ALL" "en_GB.UTF-8"
    setEnv "LANG"   "en_GB.UTF-8"

    launcherOptions <- do
        eLauncherOptions <- getLauncherOptions
        case eLauncherOptions of
            Left err -> throwM $ LauncherOptionsError (show err)
            Right lo -> pure lo

    let workingDir = loWorkingDirectory launcherOptions

    -- Every platform will run a script before running the launcher that creates a
    -- working directory, so workingDir should always exist.
    unlessM (setWorkingDirectory workingDir)
        $ throwM . WorkingDirectoryDoesNotExist $ workingDir

    -- Really no clue what to put there and how will the wallet work.
    -- These will be refactored in the future
    let configurationOptions :: ConfigurationOptions
        configurationOptions = loConfiguration launcherOptions

    let walletPath :: WalletPath
        walletPath = getWPath launcherOptions

    let walletArgs :: WalletArguments
        walletArgs = getWargs launcherOptions

    let updaterData :: UpdaterData
        updaterData = getUpdaterData launcherOptions

    -- where to generate the certificates
    let tlsPath :: TLSPath
        tlsPath = TLSPath $ loTlsPath launcherOptions

    logConfig       <- defaultConfigStdout
    (baseTrace, sb) <- setupTrace_ logConfig "launcher"

    let loggingDependencies :: LoggingDependencies
        loggingDependencies = LoggingDependencies
            { logInfo       = Trace.logInfo baseTrace
            , logError      = Trace.logError baseTrace
            , logNotice     = Trace.logNotice baseTrace
            }

    -- | If we need to, we first check if there are certificates so we don't have
    -- to generate them. Since the function is called `generate...`, that's what
    -- it does, it generates the certificates.
    generateTlsCertificates
        loggingDependencies
        configurationOptions
        tlsPath

    -- In the case the user wants to avoid installing the update now, we
    -- run the update (if there is one) when we have it downloaded.
    void $ runUpdater runDefaultUpdateProcess loggingDependencies updaterData

    -- You still want to run the wallet even if the update fails
    exitCode <- runWalletProcess
                    loggingDependencies
                    WalletModeNormal
                    walletPath
                    walletArgs
                    walletRunnerProcess
                    updaterData

    -- Shut down the logging layer.
    shutdown sb

    -- Exit the program with exit code.
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
    | LauncherOptionsError Text
    | WorkingDirectoryDoesNotExist FilePath
    deriving (Eq)

instance Buildable LauncherExceptions where
    build = \case
        CannotGenerateTLS -> bprint "Couldn't generate TLS certificates; \
            \ Daedalus wallet won't work without TLS. Please check your configuration \
            \ and make sure you aren't already running an instance of Daedalus wallet."
        LauncherOptionsError err -> bprint
               "Error occured during loading configuration file:\n"
            <> Formatting.Buildable.build err
        WorkingDirectoryDoesNotExist path -> bprint
               "Failed to set working directory because it does not exist: "
            <> Formatting.Buildable.build path

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
generateTlsCertificates :: LoggingDependencies -> ConfigurationOptions -> TLSPath -> IO ()
generateTlsCertificates externalDependencies' configurationOptions (TLSPath tlsPath) = do

    let tlsServer = tlsPath </> "server"
    let tlsClient = tlsPath </> "client"

    logInfo externalDependencies' $ "Generating the certificates!"

    -- Create the directories.
    createDirectoryIfMissing True tlsServer
    createDirectoryIfMissing True tlsClient

    -- Generate the certificates.
    generateCertificates tlsServer tlsClient
        `onException` throwM CannotGenerateTLS
        -- ^ unfortunate since we gobble up the real cause,
        -- but we want the client to have a nice message

  where
    -- | The generation of the certificates. More or less copied from
    -- `cardano-sl`.
    generateCertificates :: FilePath -> FilePath -> IO ()
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
