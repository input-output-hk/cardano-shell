module Configuration.Lib
    ( mkLauncher
    , mkTopology
    , mkOSConfig
    , mkInstallerConfig
    -- * Experimental
    , mkNewLauncher
    ) where

import           Cardano.Prelude

import qualified Dhall               as D

import           Configuration.Types (Cluster (..), InstallerConfig, Launcher,
                                      NewLauncher, OS (..), OSConfig,
                                      TopologyConfig, renderCluster, renderOS)

-- | Generate 'Launcher' configuration with given 'OS' and 'Cluster'
mkLauncher :: OS -> Cluster -> IO Launcher
mkLauncher os cluster = D.input D.auto launcherPath
  where
    launcherPath = toPath "launcher"
        <> " " <> toPath (renderCluster cluster)
        <> " " <> "(" <> toPath (renderOS os) <> " " <> toPath (renderCluster cluster) <> ")"

-- | Generate 'TopologyConfig' with given 'Cluster'
mkTopology :: Cluster -> IO TopologyConfig
mkTopology cluster = D.input D.auto topologyPath
  where
    topologyPath = toPath "topology" <> " " <> toPath (renderCluster cluster)

-- | Generate 'OSConfig' with given 'OS' and 'Cluster'
mkOSConfig :: OS -> Cluster -> IO OSConfig
mkOSConfig os cluster = D.input D.auto osConfigPath
  where
    osConfigPath = toPath (renderOS os) <> " " <> toPath (renderCluster cluster)

-- | Generate 'InstallerConfig' with given 'OS' and 'Cluster'
mkInstallerConfig :: OS -> Cluster -> IO InstallerConfig
mkInstallerConfig os cluster = D.input D.auto installerConfigPath
  where
    installerConfigPath = toPath "installer"
        <> " " <> toPath (renderCluster cluster)
        <> " (" <> toPath (renderOS os) <> " " <> toPath (renderCluster cluster) <> ")"

-- NewLauncher (Experimental)
mkNewLauncher :: OS -> Cluster -> IO NewLauncher
mkNewLauncher os cluster = D.input D.auto launcherPath
  where
    launcherPath = toPath "newLauncher"
        <> " " <> toPath (renderCluster cluster)
        <> " " <> "(" <> toPath (renderOS os) <> " " <> toPath (renderCluster cluster) <> ")"

-- | Given an FileName, return 'FilePath' to dhall file
toPath :: Text -> Text
toPath fileName = "./dhall/" <> fileName <> ".dhall"