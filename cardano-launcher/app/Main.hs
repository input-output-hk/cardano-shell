{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}

module Main where

import           Cardano.Prelude
import qualified Prelude

import           Distribution.System (OS (Windows), buildOS)
import           System.Environment (setEnv)
import           System.Exit (exitWith)
import           System.IO.Silently (hSilence)

import           Formatting (bprint, build, formatToString)
import           Formatting.Buildable (Buildable (..))

import           Cardano.BM.Setup (withTrace)
import qualified Cardano.BM.Trace as Trace
import           Cardano.BM.Tracing

import           Cardano.Shell.CLI (getLauncherOptions)
import           Cardano.Shell.Configuration (ConfigurationOptions (..),
                                              LauncherOptions (..),
                                              WalletArguments (..),
                                              WalletPath (..), getUpdaterData,
                                              getWPath, getWargs,
                                              setWorkingDirectory)
import           Cardano.Shell.Launcher (LoggingDependencies (..), TLSError,
                                         TLSPath (..), WalletMode (..),
                                         generateTlsCertificates,
                                         runWalletProcess, walletRunnerProcess)
import           Cardano.Shell.Update.Lib (RemoveArchiveAfterInstall (..),
                                           UpdaterData (..),
                                           runDefaultUpdateProcess, runUpdater)
import           Control.Exception.Safe (throwM)
import           Data.Text.Lazy.Builder (fromString, fromText)

--------------------------------------------------------------------------------
-- Main
--------------------------------------------------------------------------------

-- | Main function.
main :: IO ()
main = silence $ do

    logConfig       <- defaultConfigStdout

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

        launcherOptions <- do
            eLauncherOptions <- getLauncherOptions loggingDependencies
            case eLauncherOptions of
                Left err -> do
                    Trace.logError baseTrace $
                        "Error occured while parsing configuration file: " <> show err
                    throwM $ LauncherOptionsError (show err)
                Right lo -> pure lo

        let workingDir = loWorkingDirectory launcherOptions

        -- Every platform will run a script before running the launcher that creates a
        -- working directory, so workingDir should always exist.
        unlessM (setWorkingDirectory workingDir) $ do
            Trace.logError baseTrace $ "Working directory does not exist: " <> toS workingDir
            throwM . WorkingDirectoryDoesNotExist $ workingDir

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
        let mTlsPath :: Maybe TLSPath
            mTlsPath = TLSPath <$> loTlsPath launcherOptions


        case mTlsPath of
            Just tlsPath -> do
                -- | If we need to, we first check if there are certificates so we don't have
                -- to generate them. Since the function is called `generate...`, that's what
                -- it does, it generates the certificates.
                eTLSGeneration <- generateTlsCertificates
                    loggingDependencies
                    configurationOptions
                    tlsPath

                case eTLSGeneration of
                    Left generationError -> do
                        Trace.logError baseTrace $
                            "Error occured while generating TLS certificates: " <> show generationError
                        throwM $ FailedToGenerateTLS generationError
                    Right _              -> return ()
            Nothing -> pure () -- TLS generation has been disabled

        -- In the case the user wants to avoid installing the update now, we
        -- run the update (if there is one) when we have it downloaded.
        void $ runUpdater
            RemoveArchiveAfterInstall
            runDefaultUpdateProcess
            loggingDependencies
            updaterData

        -- You still want to run the wallet even if the update fails
        exitCode <- runWalletProcess
                        loggingDependencies
                        WalletModeNormal
                        walletPath
                        walletArgs
                        walletRunnerProcess
                        updaterData

        Trace.logNotice baseTrace $
            "Shutting down cardano-launcher with exitcode: " <> show exitCode

        -- Exit the program with exit code.
        exitWith exitCode

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
silence action = case buildOS of
    Windows -> hSilence [stdout, stderr] action
    _       -> action
