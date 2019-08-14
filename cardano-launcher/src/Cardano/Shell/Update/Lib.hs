{-| Update module
-}

{-# LANGUAGE CPP                 #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Cardano.Shell.Update.Lib
    ( UpdaterData(..)
    , RunCmdFunc
    , runUpdater
    , runUpdater'
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

-- | Updater path, args, windows runner path, archive path
data UpdaterData = UpdaterData
    { udPath          :: !FilePath
    , udArgs          :: ![Text]
    , udWindowsRunner :: !(Maybe FilePath)
    , udArchivePath   :: !FilePath
-- ^We might add checksum value for updater to ensure that we're launching the right updater
    }

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
runUpdater :: UpdaterData -> IO ExitCode
runUpdater = runUpdater' runCmd
  where
    runCmd :: FilePath -> [String] -> FilePath -> IO ExitCode
    runCmd path args archive =
        withCreateProcess (proc path (args <> [archive]))
            $ \_in _out _err ph -> waitForProcess ph

type RunCmdFunc
    = FilePath
    -> [String]
    -> FilePath
    -> IO ExitCode

-- | @runUpdater@ but can inject any runCommand function.
-- This is used for testing.
runUpdater' :: RunCmdFunc -> UpdaterData -> IO ExitCode
runUpdater' runCommand ud = do
    let path = udPath ud
    let args = map toS $ udArgs ud
    let archive = (udArchivePath ud)

    updaterExist <- doesFileExist path

    if updaterExist
        then do
            exitCode <- case buildOS of
                Windows -> do
                    writeWindowsUpdaterRunner archive
                    runCommand archive args archive -- Process dies here
                _ -> runCommand path args archive
            case exitCode of --- On windows, the function will never reach here
                ExitSuccess -> do
                    whenM (doesFileExist archive) $ removeFile archive
                    return $ ExitSuccess
                _ -> return $ exitCode
        else return $ ExitFailure 1

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
    exePath <- getExecutablePath -- (TODO): Check that it returns absolute path!
    launcherArgs <- getArgs
#ifdef mingw32_HOST_OS
    selfPid <- getCurrentProcessId
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
