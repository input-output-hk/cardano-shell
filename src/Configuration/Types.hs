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
data ClusterConfig = ClusterConfig
    { ccfgName                   :: !Text
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
    autoWith _ = D.record
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
data OSConfig = OSConfig
    { osName              :: !Text
    , osConfigurationYaml :: !Text
    , osInstallDirectory  :: !Text
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
        <*> D.field "x509ToolPath" D.strictText
        <*> D.field "nodeArgs" D.auto
        <*> D.field "pass" D.auto
    )

instance Interpret OSConfig where
    autoWith _ = osConfig

-- | Node arguments
data NodeArgs = NodeArgs
    { naKeyfile          :: !Text
    , naLogsPrefix       :: !Text
    , naTopology         :: !Text
    , naUpdateLatestPath :: !Text
    , naWalletDBPath     :: !Text
    , naTlsPath          :: !Text
    } deriving (Eq, Show)

instance Interpret NodeArgs where
    autoWith _ = D.record
        ( NodeArgs
            <$> D.field "keyfile" D.strictText
            <*> D.field "logsPrefix" D.strictText
            <*> D.field "topology" D.strictText
            <*> D.field "updateLatestPath" D.strictText
            <*> D.field "walletDBPath" D.strictText
            <*> D.field "tlsPath" D.strictText
        )

-- | Paths
data Pass = Pass
    { pStatePath           :: !Text
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

instance Interpret Pass where
    autoWith _ = D.record
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

-- | Launcher configuration
data LauncherConfig = LauncherConfig
    { lcfgFilePath    :: !Text
    , lcfgKey         :: !Text
    , lcfgSystemStart :: !(Maybe Natural)
    , lcfgSeed        :: !(Maybe Natural)
    } deriving (Eq, Show)

instance Interpret LauncherConfig where
    autoWith _ = D.record
        ( LauncherConfig
            <$> D.field "filePath" D.strictText
            <*> D.field "key" D.strictText
            <*> D.field "systemStart" (D.maybe D.natural)
            <*> D.field "seed" (D.maybe D.natural)
        )

-- | Topology configuration
newtype TopologyConfig = TopologyConfig {
      getWalletConfig :: WalletConfig
    } deriving (Eq, Show)

instance Interpret TopologyConfig where
    autoWith _ = D.record
        (TopologyConfig <$> D.field "wallet" D.auto)

-- | Wallet configuration
data WalletConfig = WalletConfig
    { wcfgRelays    :: ![[Host]]
    , wcfgValency   :: !Natural
    , wcfgFallbacks :: !Natural
    } deriving (Eq, Show)

instance Interpret WalletConfig where
    autoWith _ = D.record
        ( WalletConfig
            <$> D.field "relays" (D.list $ D.list D.auto)
            <*> D.field "valency" D.natural
            <*> D.field "fallbacks" D.natural
        )

-- | Host
newtype Host = Host {
    getHost :: Text
    } deriving (Eq, Show)

instance Interpret Host where
    autoWith _ = D.record
        (Host <$> D.field "host" D.strictText)

-- | Installer configuration
data InstallerConfig = InstallerConfig
    { icfgInstallDirectory :: !Text
    , icfgMacPackageName   :: !Text
    , icfgWalletPort       :: !Natural
    } deriving (Eq, Show)

instance Interpret InstallerConfig where
    autoWith _ = D.record
        ( InstallerConfig
            <$> D.field "installDirectory" D.strictText
            <*> D.field "macPackageName" D.strictText
            <*> D.field "walletPort" D.natural
        )

-- | Launcher configuration
data Launcher = Launcher
    { lConfig            :: !LauncherConfig
    , lNodeDbPath        :: !Text
    , lNodeLogConfig     :: !Text
    , lUpdaterPath       :: !Text
    , lUpdaterArgs       :: ![Text]
    , lUpdateArchive     :: !(Maybe Text)
    , lReportServer      :: !Text
    , lLogsPrefix        :: !Text
    , lTlsca             :: !Text
    , lTlscert           :: !Text
    , lTlsKey            :: !Text
    , lNoClientAuth      :: !Bool
    , lLogConsoleOff     :: !Bool
    , lUpdateServer      :: !Text
    , lKeyFile           :: !Text
    , lTopology          :: !Text
    , lWalletDbPath      :: !Text
    , lUpdateLatestPath  :: !Text
    , lWalletAddress     :: !Text
    , lupdateWithPackage :: !Bool
    } deriving (Eq, Show)

instance Interpret Launcher where
    autoWith _ = D.record
        ( Launcher
            <$> D.field "configuration" D.auto
            <*> D.field "nodeDbPath" D.strictText
            <*> D.field "nodeLogConfig" D.strictText
            <*> D.field "updaterPath" D.strictText
            <*> D.field "updaterArgs" (D.list D.strictText)
            <*> D.field "updateArchive" (D.maybe D.strictText)
            <*> D.field "reportServer" D.strictText
            <*> D.field "logsPrefix" D.strictText
            <*> D.field "tlsca" D.strictText
            <*> D.field "tlscert" D.strictText
            <*> D.field "tlsKey" D.strictText
            <*> D.field "noClientAuth" D.bool
            <*> D.field "logConsoleOff" D.bool
            <*> D.field "updateServer" D.strictText
            <*> D.field "keyFile" D.strictText
            <*> D.field "topology" D.strictText
            <*> D.field "walletDbPath" D.strictText
            <*> D.field "updateLatestPath" D.strictText
            <*> D.field "walletAddress" D.strictText
            <*> D.field "updateWithPackage" D.bool
        )