{-| Update module
-}

{-# LANGUAGE CPP                 #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Cardano.Shell.Update.Lib
    ( UpdaterData (..)
    , RunCmdFunc
    , runUpdater
    , runDefaultUpdateProcess
    -- * Intepretable language
    , UpdaterExists (..)
    , UpdaterCommand (..)
    , executeUpdater
    , isUpdaterRunOnWin
    , isUpdaterRunOnUnix
    , updaterExistsToBool
    -- * OS specific type/function
    , UpdateOSPlatform (..)
    , osToUpdateOSPlatform
    ) where

import           Cardano.Prelude

import           Distribution.System (OS (..), buildOS)
import           Prelude (String)

import           System.Directory (doesFileExist, removeFile)
import           System.Process (proc, waitForProcess, withCreateProcess)

#ifdef mingw32_HOST_OS
import           System.Environment (getExecutablePath)
import           System.Win32.Process (getCurrentProcessId)
#endif

import           Test.QuickCheck (Arbitrary (..), oneof)

import           Cardano.Shell.Types (LoggingDependencies (..))


-- We need to add the check if the archive exists first!
-- /usr/bin/open -FW  /../daedalus.pkg -- MAC
-- /bin/update-runner /../installer.sh -- LINUX
--                    ABS. PATH
-- Installer.bat      Installer.exe
-- WE GENERATE THIS!

-- | Runner path, what we use to run the update/installer,
-- arguments for the runner, and the actual update path for the installer.
data UpdaterData = UpdaterData
    { udRunnerPath      :: !FilePath
    -- ^ Path of the updater/installer runner. Examples:
    -- - /usr/bin/open
    -- - /bin/update-runner
    -- - Installer.bat (that we generate)
    , udArgs            :: ![Text]
    -- ^ Arguments for the updater/installer.
    , udUpdatePath     :: !FilePath
    -- ^ The update path of the update file. Examples:
    -- - /../daedalus.pkg
    -- - /../installer.sh
    -- - Installer.exe (Found in the working directory)
    }

-- | On what platform are we running the update?
data UpdateOSPlatform
    = WinOS
    | UnixOS
    deriving (Eq, Show)

-- | Conversion of the build OS to our definition.
osToUpdateOSPlatform :: OS -> UpdateOSPlatform
osToUpdateOSPlatform Windows    = WinOS
osToUpdateOSPlatform _          = UnixOS

-- | The way we should run the process normally.
runDefaultUpdateProcess :: FilePath -> [String] -> IO ExitCode
runDefaultUpdateProcess path args =
    withCreateProcess (proc path args)
        $ \_in _out _err ph -> waitForProcess ph

-- The function for executing the update.
type RunCmdFunc = FilePath -> [String] -> IO ExitCode

-- | A flag for the existence of the updater file.
data UpdaterExists
    = UpdaterExists
    | UpdaterDoesntExist
    deriving (Eq, Show)

instance Arbitrary UpdaterExists where
    arbitrary = oneof [pure UpdaterExists, pure UpdaterDoesntExist]

-- | A simple isomorphic conversion from a more rich/descriptive type.
updaterExistsToBool :: UpdaterExists -> Bool
updaterExistsToBool UpdaterExists       = True
updaterExistsToBool UpdaterDoesntExist  = False

-- | A simple isomorphic conversion to a more rich/descriptive type.
boolToUpdaterExists :: Bool -> UpdaterExists
boolToUpdaterExists True    = UpdaterExists
boolToUpdaterExists False   = UpdaterDoesntExist

-- | The small language we use to distinct between execution.
data UpdaterCommand
    = WindowsRunUpdate !FilePath ![Text]
    | UnixRunUpdate !FilePath ![Text]
    | UpdaterFileMissing
    deriving (Eq, Show)

isUpdaterRunOnWin :: UpdaterCommand -> Bool
isUpdaterRunOnWin (WindowsRunUpdate _ _)    = True
isUpdaterRunOnWin _                         = False

isUpdaterRunOnUnix :: UpdaterCommand -> Bool
isUpdaterRunOnUnix (UnixRunUpdate _ _)  = True
isUpdaterRunOnUnix _                    = False

-- | Interpret the small language into the "real" semantics.
evaluateUpdaterCmdExitCode :: RunCmdFunc -> UpdaterCommand -> IO ExitCode
evaluateUpdaterCmdExitCode runCommand = \case
    -- The update needs to be run on Windows.
    WindowsRunUpdate runnerPath args -> do
#ifdef mingw32_HOST_OS
        writeWindowsUpdaterRunner runnerPath
#endif
        runCommand runnerPath (map toS args)
    -- The update needs to be run on *nix.
    UnixRunUpdate runnerPath args -> do
        runCommand runnerPath (map toS args)
    -- The update file is missing.
    UpdaterFileMissing      -> return $ ExitFailure 1

-- | Interpret the small language into the logging semantics.
evaluateUpdaterCmdLogging :: LoggingDependencies -> UpdaterCommand -> IO ()
evaluateUpdaterCmdLogging loggingDep = \case
    WindowsRunUpdate _ _    -> logInfo loggingDep $ "Running WIN update."
    UnixRunUpdate _ _       -> logInfo loggingDep $ "Running UNIX update."
    UpdaterFileMissing      -> logError loggingDep $ "The updater file is missing!"

-- | Run the update system
--
-- For UNIX system:
--
-- Check that @udPath@ exists, then run the command @udPath udArgs udArchivePath@
--
-- For Windows:
--
-- Check that @udPath@ exists, but instead of running the command directly, you
-- first have to generate a @.bat@ file which will act as a script.
-- After it being generated, you run that script.
runUpdater :: RunCmdFunc -> LoggingDependencies -> UpdaterData -> IO ExitCode
runUpdater runCommand loggingDep updaterData = do

    let runnerPath  = udRunnerPath updaterData
    let updatePath  = udUpdatePath updaterData

    updateRunnerExist <- boolToUpdaterExists <$> doesFileExist runnerPath

    logInfo loggingDep $ "Does file exist: " <> show updateRunnerExist

    let currentBuildOS :: UpdateOSPlatform
        currentBuildOS = osToUpdateOSPlatform buildOS

    let updaterCommand :: UpdaterCommand
        updaterCommand = executeUpdater currentBuildOS updateRunnerExist updaterData

    -- Log out the results.
    evaluateUpdaterCmdLogging loggingDep updaterCommand

    -- Actually execute the commands.
    exitCode <- evaluateUpdaterCmdExitCode runCommand updaterCommand


    -- The handling of the final exit code of the updater.
    case exitCode of
        -- If the update is a success, them remove the installer file.
        ExitSuccess -> do
            whenM (doesFileExist updatePath) $ removeFile updatePath
            return $ ExitSuccess
        -- Otherwise, return an error.
        _           -> return $ exitCode

-- | Pure execution of @UpdaterCommand@.
executeUpdater :: UpdateOSPlatform -> UpdaterExists -> UpdaterData -> UpdaterCommand
executeUpdater buildOS' updaterExist updaterData = do

    let runnerPath = udRunnerPath updaterData
    let args       = map toS $ udArgs updaterData
    let updatePath = udUpdatePath updaterData

    if updaterExist == UpdaterExists
        then
            case buildOS' of
                WinOS   -> WindowsRunUpdate runnerPath (toS updatePath:args)
                UnixOS  -> UnixRunUpdate    runnerPath (toS updatePath:args)
        else UpdaterFileMissing

-- | Create @.bat@ file on given @FilePath@
--
-- https://github.com/input-output-hk/cardano-sl/blob/develop/tools/src/launcher/Main.hs#L585
--
-- The installer cant write to cardano-launcher.exe while it is running
-- so you must fully stop launcher before you can start the installer.
-- Because of this, we need a @.bat@ file which will run the update procedure and
-- re-launch the launcher.
-- Only Windows has this problem.
#ifdef mingw32_HOST_OS
writeWindowsUpdaterRunner :: FilePath -> IO ()
writeWindowsUpdaterRunner runnerPath = do
    exePath         <- getExecutablePath -- (TODO): Check that it returns absolute path!
    launcherArgs    <- getArgs

    selfPid         <- getCurrentProcessId
    writeFile (toS runnerPath) $ T.unlines
    -- What info can this file supply if it fails?
    -- How can you make this scream if it fails
    -- Checksum of the updater exe?
    -- Only then run it
        [ "TaskKill /PID "<> show selfPid <>" /F"
        -- Run updater
        , "%*"
        -- Delete updater
        , "del %1"
        -- Run launcher again
        , "start \"cardano launcher\" /b " <> (quote $ toS exePath) <> " "
            <> (T.unwords $ map (quote . toS) launcherArgs)
        -- Delete the bat file
        , "(goto) 2>nul & del \"%~f0\""
        ]
  where
    quote :: Text -> Text
    quote str = "\"" <> str <> "\""
    -- str = a"b
    -- possible inject attack
#endif

