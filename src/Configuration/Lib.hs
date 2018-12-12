module Configuration.Lib
    ( mkLauncher
    , mkTopology
    , mkOSConfig
    , mkInstallerConfig
    ) where

import           Cardano.Prelude

import           Dhall               (auto, input)

import           Configuration.Types (Cluster (..), InstallerConfig, Launcher,
                                      Launcher, OS (..), OSConfig,
                                      TopologyConfig, renderCluster, renderOS)

-- | Generate 'TopologyConfig' with given 'Cluster'
mkTopology :: Cluster -> IO TopologyConfig
mkTopology cluster = input auto topologyPath
  where
    topologyPath = toPath "topology" <> " " <> toPath (renderCluster cluster)

-- | Generate 'OSConfig' with given 'OS' and 'Cluster'
mkOSConfig :: OS -> Cluster -> IO OSConfig
mkOSConfig os cluster = input auto osConfigPath
  where
    osConfigPath = toPath (renderOS os) <> " " <> toPath (renderCluster cluster)

-- | Generate 'InstallerConfig' with given 'OS' and 'Cluster'
mkInstallerConfig :: OS -> Cluster -> IO InstallerConfig
mkInstallerConfig os cluster = input auto installerConfigPath
  where
    installerConfigPath = toPath "installer"
        <> " " <> toPath (renderCluster cluster)
        <> " (" <> toPath (renderOS os) <> " " <> toPath (renderCluster cluster) <> ")"

-- | Generate 'Launcher' config with given 'OS' and 'Cluster'
mkLauncher :: OS -> Cluster -> IO Launcher
mkLauncher os cluster = input auto launcherPath
  where
    launcherPath = toPath "launcher"
        <> " " <> toPath (renderCluster cluster)
        <> " " <> "(" <> toPath (renderOS os) <> " " <> toPath (renderCluster cluster) <> ")"

-- | Given an FileName, return 'FilePath' to dhall file
toPath :: Text -> Text
toPath fileName = "./dhall/" <> fileName <> ".dhall"
