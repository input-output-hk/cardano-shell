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

import qualified Data.Text as T
import           Distribution.System (OS (..), buildOS)
import           Prelude (String)

import           System.Directory (doesFileExist, removeFile)
import           System.Environment (getExecutablePath)
import           System.Process (proc, waitForProcess, withCreateProcess)

#ifdef mingw32_HOST_OS
import           System.Win32.Process (getCurrentProcessId)
#endif

import           Test.QuickCheck (Arbitrary (..), oneof)

import           Cardano.Shell.Types (LoggingDependencies (..))

-- | Updater path, args, windows runner path, archive path
data UpdaterData = UpdaterData
    { udPath          :: !FilePath
    -- ^ Path of the updater/installer.
    , udArgs          :: ![Text]
    -- ^ Arguments for the updater/installer.
    , udWindowsRunner :: !(Maybe FilePath)
    -- ^ Windows runner path for the updater/installer.
    , udArchivePath   :: !FilePath
    -- ^ We might add checksum value for updater to ensure that
    -- we're launching the right updater.
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
        writeWindowsUpdaterRunner runnerPath
        runCommand runnerPath (map toS args)
    -- The update needs to be run on *nix.
    UnixRunUpdate path args -> do
        runCommand path (map toS args)
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

    let path       = udPath updaterData
    let archive    = udArchivePath updaterData

    updaterExist <- boolToUpdaterExists <$> doesFileExist path

    logInfo loggingDep $ "Does file exist: " <> show updaterExist

    let currentBuildOS :: UpdateOSPlatform
        currentBuildOS = osToUpdateOSPlatform buildOS

    let updaterCommand :: UpdaterCommand
        updaterCommand = executeUpdater currentBuildOS updaterExist updaterData

    -- Log out the results.
    evaluateUpdaterCmdLogging loggingDep updaterCommand

    -- Actually execute the commands.
    exitCode <- evaluateUpdaterCmdExitCode runCommand updaterCommand


    -- The handling of the final exit code of the updater.
    case exitCode of
        -- If the update is a success, them remove the archive file.
        ExitSuccess -> do
            whenM (doesFileExist archive) $ removeFile archive
            return $ ExitSuccess
        -- Otherwise, return an error.
        _           -> return $ exitCode

-- | Pure execution of @UpdaterCommand@.
executeUpdater :: UpdateOSPlatform -> UpdaterExists -> UpdaterData -> UpdaterCommand
executeUpdater buildOS' updaterExist updaterData = do

    let path       = udPath updaterData
    let args       = map toS $ udArgs updaterData
    let archive    = udArchivePath updaterData
    let runnerPath = fromMaybe mempty (udWindowsRunner updaterData)

    if updaterExist == UpdaterExists
        then
            case buildOS' of
                WinOS   -> WindowsRunUpdate runnerPath (toS path:args)
                UnixOS  -> UnixRunUpdate path (toS archive:args)
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
writeWindowsUpdaterRunner :: FilePath -> IO ()
writeWindowsUpdaterRunner runnerPath = do
    exePath         <- getExecutablePath -- (TODO): Check that it returns absolute path!
    launcherArgs    <- getArgs
#ifdef mingw32_HOST_OS
    selfPid         <- getCurrentProcessId
#else
    let (selfPid :: Integer) = 0 -- This will never be run on non-Windows
#endif
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
