{-| Update module
-}

{-# LANGUAGE LambdaCase #-}

module Cardano.Shell.Update.Lib
    ( UpdaterData(..)
    , updaterData
    , runUpdater
    ) where

import           Cardano.Prelude

import           Distribution.System (OS (..), buildOS)
import           System.Directory (doesFileExist)
import           System.Process (proc, withCreateProcess)

                                                            
-- | Updater path, args, windows runner path, archive path
data UpdaterData = UpdaterData
    { udPath        :: !FilePath
    , udArgs        :: ![Text]
    , udWindowsPath :: Maybe FilePath
    , udArchivePath :: Maybe FilePath
    }

updaterData :: UpdaterData
updaterData = case buildOS of
    Windows -> UpdaterData "WindowsPath" ["Windows", "Args"] (Just "Window path") Nothing
    OSX     -> UpdaterData "MacPath" [] Nothing (Just "ArchivePath")
    _       -> UpdaterData "LinuxPath" [] Nothing (Just "LinuxPath")

-- | Run the update system
runUpdater :: UpdaterData -> IO ()
runUpdater ud = do
    let path = udPath ud
    let args = map toS $ udArgs ud
    let mWindowPath = udWindowsPath ud
    let archive = maybe [] (\arch -> [toS arch]) (udArchivePath ud)
    whenM (doesFileExist path) $ do
        case mWindowPath of
            Nothing -> runUnixUpdater path args archive
            -- WIP
            Just windowsPath -> runWindowUpdater windowsPath args archive
  where
    runUnixUpdater path args archive = 
        withCreateProcess (proc path (args <> archive))
            $ \_in _out _err _ -> return ()

    -- WIP
    runWindowUpdater path args archive =
        withCreateProcess (proc path (args <> archive))
            $ \_in _out _err _ -> return ()