module Cardano.Shell.Configuration.Lib
    ( mkLauncher
    , mkTopology
    , mkOSConfig
    , mkInstallerConfig
    -- Configurations for features
    , mkBlockchainConfig
    , mkLoggingConfig
    , mkNetworkConfig
    , mkWalletConfig
    ) where

import           Cardano.Prelude

import           Dhall (auto, input)

import           Cardano.Shell.Configuration.Types (BlockchainConfig,
                                                    Cluster (..),
                                                    InstallerConfig, Launcher,
                                                    Launcher, LoggingConfig,
                                                    NetworkConfig, OS (..),
                                                    OSConfig, TopologyConfig,
                                                    WalletConfig, renderCluster,
                                                    renderOS)

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

--------------------------------------------------------------------------------
-- Features
--------------------------------------------------------------------------------

mkBlockchainConfig :: OS -> Cluster -> IO BlockchainConfig
mkBlockchainConfig os cluster = input auto blockchainPath
  where
    blockchainPath = toFeaturePath "blockchain"
        <> "(" <> osPath os <> " " <> clusterPath cluster <> ")"

mkLoggingConfig :: OS -> Cluster -> IO LoggingConfig
mkLoggingConfig os cluster = input auto loggingPath
  where
    loggingPath = toFeaturePath "logging"
        <> "(" <> osPath os <> " " <> clusterPath cluster <> ")"
        <> "(" <> toPath "launcher" <> " " <> clusterPath cluster <> " " <>
        "(" <> osPath os <> " " <> clusterPath cluster <> ")" <>")"

mkNetworkConfig :: OS -> Cluster -> IO NetworkConfig
mkNetworkConfig os cluster = input auto networkPath
  where
    networkPath = toFeaturePath "network" <> " "
        <> toPath (renderCluster cluster)
        <> "(" <> osPath os <> " " <> clusterPath cluster <> ") "
        <> "(" <> toPath "launcher" <> " " <> clusterPath cluster <> " " <>
        "(" <> osPath os <> " " <> clusterPath cluster <> ")" <>")"

mkWalletConfig :: OS -> Cluster -> IO WalletConfig
mkWalletConfig os cluster = input auto walletPath
  where
    walletPath = toFeaturePath "wallet" <> " "
        <> clusterPath cluster
        <> "(" <> osPath os <> " " <> clusterPath cluster <> ") "
        <> "(" <> toPath "launcher" <> " " <> clusterPath cluster <> " " <>
        "(" <> osPath os <> " " <> clusterPath cluster <> ")" <>") "
        <> "(" <> toPath "topology" <> " " <> clusterPath cluster <> ")"

--------------------------------------------------------------------------------
-- Helper function
--------------------------------------------------------------------------------

-- | Render given text into dhall file path
toFeaturePath :: Text -> Text
toFeaturePath fileName = "./dhall/features/" <> fileName <> ".dhall"

-- | Given an FileName, return 'FilePath' to dhall file
toPath :: Text -> Text
toPath fileName = "./dhall/" <> fileName <> ".dhall"

-- | Return given 'Cluster' dhall filepath
clusterPath :: Cluster -> Text
clusterPath cluster = toPath $ renderCluster cluster

-- | Return givne 'OS' dhall filepath
osPath :: OS -> Text
osPath os = toPath $ renderOS os