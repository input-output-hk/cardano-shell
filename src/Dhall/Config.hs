module Dhall.Config where

import           Cardano.Prelude

import qualified Dhall           as D

import           Dhall.Types     (Cluster (..), InstallerConfig, Launcher,
                                  OS (..), OSConfig, Topology, renderCluster,
                                  renderOS)

mkLauncher :: OS -> Cluster -> IO Launcher
mkLauncher os cluster = D.input D.auto launcherPath
  where
    launcherPath = mkPath "launcher"
        <> " " <> mkPath (renderCluster cluster)
        <> " " <> "(" <> mkPath (renderOS os) <> " " <> mkPath (renderCluster cluster) <> ")"

mkTopology :: Cluster -> IO Topology
mkTopology cluster = D.input D.auto topologyPath
  where
    topologyPath = mkPath "topology" <> " " <> mkPath (renderCluster cluster)

mkOSConfig :: OS -> Cluster -> IO OSConfig
mkOSConfig os cluster = D.input D.auto osConfigPath
  where
    osConfigPath = mkPath (renderOS os) <> " " <> mkPath (renderCluster cluster)

mkInstallerConfig :: OS -> Cluster -> IO InstallerConfig
mkInstallerConfig os cluster = D.input D.auto installerConfigPath
  where
    installerConfigPath = mkPath "installer"
        <> " " <> mkPath (renderCluster cluster)
        <> " (" <> mkPath (renderOS os) <> " " <> mkPath (renderCluster cluster) <> ")"

mkPath :: Text -> Text
mkPath fileName = "./dhall/" <> fileName <> ".dhall"
