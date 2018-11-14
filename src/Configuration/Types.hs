{-# LANGUAGE OverloadedStrings #-}

module Configuration.Types
    ( Cluster(..)
    , ClusterConfig(..)
    , Host(..)
    , InstallerConfig (..)
    , Launcher(..)
    , LauncherConfig(..)
    , NodeArgs(..)
    , OS(..)
    , OSConfig(..)
    , Pass(..)
    , TopologyConfig(..)
    , WalletConfig(..)
    , renderOS
    , renderCluster
    ) where

import           Cardano.Prelude

import           Dhall           (Interpret (..))
import qualified Dhall           as D
-- Importing as qualified since Dhall exports functions such as 'maybe', 'bool', 'list'
-- which conflicts with some of the prelude functions

-- | Operating system
data OS
    = Linux64
    | Macos64
    | Win64
    deriving (Bounded, Enum, Eq, Read, Show)
  
-- | Cluster
data Cluster
    = Mainnet
    | Staging
    | Testnet
    | Demo
    deriving (Bounded, Enum, Eq, Read, Show)

-- | Convert 'OS' into 'Text'
renderOS :: OS -> Text
renderOS Linux64  = "linux64"
renderOS Macos64  = "macos64"
renderOS Win64    = "win64"

-- | Convert 'Cluster' into 'Text'
renderCluster :: Cluster -> Text
renderCluster Mainnet = "mainnet"
renderCluster Testnet = "testnet"
renderCluster Staging = "staging"
renderCluster Demo    = "demo"

-- | Cluster configuration
data ClusterConfig = ClusterConfig {
      ccfgName                   :: !Text
    , ccfgKeyPrefix              :: !Text
    , ccfgRelays                 :: !Text
    , ccfgUpdateServer           :: !Text
    , ccfgReportServer           :: !Text
    , ccfgInstallDirectorySuffix :: !Text
    , ccfgMacPackageSuffix       :: !Text
    , ccfgWalletPort             :: !Natural
    } deriving (Eq, Show)

-- Defining each 'Intrepret' instance. 
-- There is an simplier way to defining these instances but it's causing infinite loops
instance Interpret ClusterConfig where
    autoWith _ = clusterConfig

-- Unfortunatly, there's no monad instance for 'Dhall.Type', perhaps use ApplicativeDo?
clusterConfig :: D.Type ClusterConfig
clusterConfig =
    D.record
       ( ClusterConfig
            <$> D.field "name" D.strictText
            <*> D.field "keyPrefix" D.strictText
            <*> D.field "relays" D.strictText
            <*> D.field "updateServer" D.strictText
            <*> D.field "reportServer" D.strictText
            <*> D.field "installDirectorySuffix" D.strictText
            <*> D.field "macPackageSuffix" D.strictText
            <*> D.field "walletPort" D.natural
       )

-- | OS configuration
data OSConfig = OSConfig {
      osName              :: !Text
    , osConfigurationYaml :: !Text
    , osInstallDirectory  :: !Text
    , osMacPackageName    :: !Text
    , osX509ToolPath      :: !Text
    , osNodeArgs          :: !NodeArgs
    , osPass              :: !Pass
    } deriving (Eq, Show)

osConfig :: D.Type OSConfig
osConfig = D.record
    ( OSConfig
        <$> D.field "name" D.strictText
        <*> D.field "configurationYaml" D.strictText
        <*> D.field "installDirectory" D.strictText
        <*> D.field "macPackageName" D.strictText
        <*> D.field "x509ToolPath" D.strictText
        <*> D.field "nodeArgs" nodeArgs
        <*> D.field "pass" Configuration.Types.pass
    )

instance Interpret OSConfig where
    autoWith _ = osConfig

-- | Node arguments
data NodeArgs = NodeArgs {
      naKeyfile          :: !Text
    , naLogsPrefix       :: !Text
    , naTopology         :: !Text
    , naUpdateLatestPath :: !Text
    , naWalletDBPath     :: !Text
    , naTlsPath          :: !Text
    } deriving (Eq, Show)

nodeArgs :: D.Type NodeArgs
nodeArgs = D.record
    ( NodeArgs
        <$> D.field "keyfile" D.strictText
        <*> D.field "logsPrefix" D.strictText
        <*> D.field "topology" D.strictText
        <*> D.field "updateLatestPath" D.strictText
        <*> D.field "walletDBPath" D.strictText
        <*> D.field "tlsPath" D.strictText
    )

instance Interpret NodeArgs where
    autoWith _ = nodeArgs

-- | Paths
data Pass = Pass {
      pStatePath           :: !Text
    , pNodePath            :: !Text
    , pNodeDbPath          :: !Text
    , pNodeLogConfig       :: !Text
    , pNodeLogPath         :: !(Maybe Text)
    , pWalletPath          :: !Text
    , pWalletLogging       :: !Bool
    , pWorkingDir          :: !Text
    , pFrontendOnlyMode    :: !Bool
    , pUpdaterPath         :: !Text
    , pUpdaterArgs         :: ![Text]
    , pUpdateArchive       :: !(Maybe Text)
    , pUpdateWindowsRunner :: !(Maybe Text)
    , pLauncherLogsPrefix  :: !Text
    } deriving (Eq, Show)

pass :: D.Type Pass
pass = D.record
    ( Pass
        <$> D.field "statePath" D.strictText
        <*> D.field "nodePath" D.strictText
        <*> D.field "nodeDbPath" D.strictText
        <*> D.field "nodeLogConfig" D.strictText
        <*> D.field "nodeLogPath" (D.maybe D.strictText)
        <*> D.field "walletPath" D.strictText
        <*> D.field "walletLogging" D.bool
        <*> D.field "workingDir" D.strictText
        <*> D.field "frontendOnlyMode" D.bool
        <*> D.field "updaterPath" D.strictText
        <*> D.field "updaterArgs" (D.list D.strictText)
        <*> D.field "updateArchive" (D.maybe D.strictText)
        <*> D.field "updateWindowsRunner" (D.maybe D.strictText)
        <*> D.field "launcherLogsPrefix" D.strictText
    )

instance Interpret Pass where
    autoWith _ = Configuration.Types.pass

-- | Launcher configuration
data Launcher = Launcher {
      lConfig         :: !LauncherConfig
    , lNodeTimeoutSec :: !Natural
    , lReportServer   :: !Text
    , lWalletArgs     :: ![Text]
    , lLogsPrefix     :: !Text
    , lTlsPath        :: !Text
    , lX509ToolPath   :: !Text
    , lNodeArgs       :: ![Text]
    , lPass           :: !Pass
    } deriving (Eq, Show)

launcher :: D.Type Launcher
launcher = D.record
    ( Launcher
        <$> D.field "configuration" launcherConfig
        <*> D.field "nodeTimeoutSec" D.natural
        <*> D.field "reportServer" D.strictText
        <*> D.field "walletArgs" (D.list D.strictText)
        <*> D.field "logsPrefix" D.strictText
        <*> D.field "tlsPath" D.strictText
        <*> D.field "x509ToolPath" D.strictText
        <*> D.field "nodeArgs" (D.list D.strictText)
        <*> D.field "pass" Configuration.Types.pass
    )

instance Interpret Launcher where
    autoWith _ = launcher

-- | Launcher configuration
data LauncherConfig = LauncherConfig {
      lcfgFilePath    :: !Text
    , lcfgKey         :: !Text
    , lcfgSystemStart :: !(Maybe Natural)
    , lcfgSeed        :: !(Maybe Natural)
    } deriving (Eq, Show)

launcherConfig :: D.Type LauncherConfig
launcherConfig = D.record
    ( LauncherConfig
        <$> D.field "filePath" D.strictText
        <*> D.field "key" D.strictText
        <*> D.field "systemStart" (D.maybe D.natural)
        <*> D.field "seed" (D.maybe D.natural)
    )

instance Interpret LauncherConfig where
    autoWith _ = launcherConfig

-- | Topology configuration
newtype TopologyConfig = TopologyConfig {
      getWalletConfig :: WalletConfig
    } deriving (Eq, Show)

topology :: D.Type TopologyConfig
topology = D.record
    (TopologyConfig <$> D.field "wallet" walletConfig)

instance Interpret TopologyConfig where
    autoWith _ = topology

-- | Wallet configuration
data WalletConfig = WalletConfig {
      wcfgRelays    :: ![[Host]]
    , wcfgValency   :: !Natural
    , wcfgFallbacks :: !Natural
    } deriving (Eq, Show)

walletConfig :: D.Type WalletConfig
walletConfig = D.record
    ( WalletConfig
        <$> D.field "relays" (D.list $ D.list host)
        <*> D.field "valency" D.natural
        <*> D.field "fallbacks" D.natural
    )

instance Interpret WalletConfig where
    autoWith _ = walletConfig

-- | Host
newtype Host = Host {
    getHost :: Text
    } deriving (Eq, Show)

host :: D.Type Host
host = D.record
    ( Host <$> D.field "host" D.strictText)

instance Interpret Host where
    autoWith _ = host

-- | Installer configuration
data InstallerConfig = InstallerConfig {
      icfgInstallDirectory :: !Text
    , icfgMacPackageName   :: !Text
    , icfgWalletPort       :: !Natural
    } deriving (Eq, Show)

installerConfig :: D.Type InstallerConfig
installerConfig = D.record
    ( InstallerConfig
        <$> D.field "installDirectory" D.strictText
        <*> D.field "macPackageName" D.strictText
        <*> D.field "walletPort" D.natural
    )

instance Interpret InstallerConfig where
    autoWith _ = installerConfig