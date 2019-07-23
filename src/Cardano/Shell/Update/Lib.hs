{-| Update module
-}

{-# LANGUAGE CPP                 #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Cardano.Shell.Update.Lib
    ( UpdaterData(..)
    , updaterData
    , runUpdater
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
    { udPath        :: !FilePath
    , udArgs        :: ![Text]
    , udWindowsPath :: Maybe FilePath
    , udArchivePath :: Maybe FilePath
    }

-- Windows: https://github.com/input-output-hk/daedalus/blob/develop/installers/dhall/win64.dhall#L32-L35
-- MacOS: https://github.com/input-output-hk/daedalus/blob/develop/installers/dhall/macos64.dhall#L31-L34
-- Linux: https://github.com/input-output-hk/daedalus/blob/develop/installers/dhall/linux64.dhall#L29-L32
updaterData :: UpdaterData
updaterData = case buildOS of
    Windows -> UpdaterData
        "Installer.exe"
        []
        (Just "Installer.bat")
        Nothing
    OSX     -> UpdaterData
        "/usr/bin/open"
        ["-FW"]
        Nothing
        (Just "\\${HOME}/Library/Application Support/Daedalus/installer.pkg")
    _       -> UpdaterData
        "/bin/update-runner"
        []
        Nothing
        (Just "\\${XDG_DATA_HOME}/Daedalus/installer.sh")

data UpdateError
    = UpdateFailed Int
    | UpdaterDoesNotExist
    deriving Show

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
runUpdater :: UpdaterData -> IO (Either UpdateError ())
runUpdater ud = do
    let path = udPath ud
    let args = map toS $ udArgs ud
    let mWindowPath = udWindowsPath ud
    let archive = maybe mempty (\arch -> toS arch) (udArchivePath ud)
    updaterExists <- doesFileExist path
    if updaterExists
        then do
            exitCode <- case mWindowPath of
                Nothing -> runCmd path args archive
                Just windowsPath -> do
                    writeWindowsUpdaterRunner windowsPath
                    runCmd windowsPath args archive
            case exitCode of
                ExitSuccess -> do
                    whenJust (udArchivePath ud) $ \updateArchivePath -> do
                        removeFile updateArchivePath
                    return . Right $ ()
                ExitFailure code -> return . Left $ UpdateFailed code
        else
            return . Left $ UpdaterDoesNotExist
  where
    runCmd :: FilePath -> [String] -> FilePath -> IO ExitCode
    runCmd path args archive =
        withCreateProcess (proc path (args <> [archive]))
            -- WIP
            $ \_in _out _err ph -> waitForProcess ph

    whenJust :: (Monad m) => Maybe a -> (a -> m ()) -> m ()
    whenJust (Just a) f = f a
    whenJust Nothing  _ = return ()

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
    exePath <- getExecutablePath
    launcherArgs <- getArgs
#ifdef mingw32_HOST_OS
    selfPid <- getCurrentProcessId
#else
    let (selfPid :: Integer) = 0 -- This will never be run on non-Windows
#endif
    writeFile (toS runnerPath) $ T.unlines
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
