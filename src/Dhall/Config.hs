module Dhall.Config where

import           Cardano.Prelude
import qualified Dhall as D

import Dhall.Types

mkLauncher :: OS -> Cluster -> IO Launcher
mkLauncher os cluster = D.input D.auto dhallPath
  where 
    dhallPath = mkPath "launcher"
            <> " " <> mkPath (renderCluster cluster) 
            <> " " <> "(" <> mkPath (renderOS os) <> " " <> mkPath (renderCluster cluster) <> ")"

mkTopology :: Cluster -> IO Topology
mkTopology cluster = D.input D.auto $ mkPath "topology" <> " " <> mkPath (renderCluster cluster)

mkOSConfig :: OS -> Cluster -> IO OSConfig
mkOSConfig os cluster = D.input D.auto $ mkPath (renderOS os) <> " " <> mkPath (renderCluster cluster)

-- BUGGED!! Returns nothing without throwing a warning
mkInstallerConfig :: OS -> Cluster -> IO InstallerConfig
mkInstallerConfig os cluster = D.input D.auto $
    mkPath "installer" <> " " <> mkPath (renderCluster cluster) 
            <> " (" <> mkPath (renderOS os) <> " " <> mkPath (renderCluster cluster)<> ")"

mkPath :: Text -> Text
mkPath fileName = "./dhall/" <> fileName <> ".dhall"