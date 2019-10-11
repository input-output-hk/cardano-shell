{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}

module Main where

import           Cardano.Prelude
import qualified Prelude

import           System.Environment (setEnv)
import           System.Exit (exitWith)

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
import           Cardano.Shell.Launcher (LoggingDependencies (..), TLSError,
                                         TLSPath (..), WalletMode (..),
                                         generateTlsCertificates,
                                         runWalletProcess, walletRunnerProcess)
import           Cardano.Shell.Update.Lib (UpdaterData (..),
                                           runDefaultUpdateProcess, runUpdater)
import           Control.Exception.Safe (throwM)
import           Data.Text.Lazy.Builder (fromString, fromText)

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
    eTLSGeneration <- generateTlsCertificates
        loggingDependencies
        configurationOptions
        tlsPath

    case eTLSGeneration of
        Left generationError -> throwM $ FailedToGenerateTLS generationError
        Right _              -> return ()

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
-- Exceptions
--------------------------------------------------------------------------------

data LauncherExceptions
    = CannotGenerateTLS
    | LauncherOptionsError Text
    | WorkingDirectoryDoesNotExist FilePath
    | FailedToGenerateTLS TLSError

instance Buildable LauncherExceptions where
    build = \case
        CannotGenerateTLS -> bprint "Couldn't generate TLS certificates; \
            \ Daedalus wallet won't work without TLS. Please check your configuration \
            \ and make sure you aren't already running an instance of Daedalus wallet."
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
