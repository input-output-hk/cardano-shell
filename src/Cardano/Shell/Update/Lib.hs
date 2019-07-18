{-| Update module
-}

{-# LANGUAGE LambdaCase #-}

module Cardano.Shell.Update.Lib
    ( runUpdater
    ) where

import           Cardano.Prelude

import           Distribution.System (OS (..), buildOS)
import           Prelude (String)
import           System.Process (proc, withCreateProcess)

import           Cardano.Shell.Configuration.Lib (mkLauncher)
import qualified Cardano.Shell.Configuration.Types as Config (Cluster (..),
                                                              Launcher (..),
                                                              OS (..))

-- | Run the update system
runUpdater :: Config.Cluster -> IO ()
runUpdater cluster = do
    launcherConfig <- mkLauncher (toConfigOS buildOS) cluster
    withCreateProcess (proc (toS $ Config.lUpdaterPath launcherConfig) (cmd launcherConfig))
        $ \_in _out _err _ -> return ()
  where
    cmd :: Config.Launcher -> [String]
    cmd launcherConfig =
        let archive = maybe [] (\arch -> [toS arch]) (Config.lUpdateArchive launcherConfig)
        in (map toS $ Config.lUpdaterArgs launcherConfig) <> archive

    toConfigOS :: OS -> Config.OS
    toConfigOS = \case
        Windows -> Config.Win64
        OSX     -> Config.Macos64
        _       -> Config.Linux64
