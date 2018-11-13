{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE OverloadedStrings #-}

module Dhall.Types
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
    , Topology(..)
    , WalletConfig(..)
    , renderOS
    , renderCluster
    ) where

import           Cardano.Prelude
import           Dhall           (Interpret (..))
import qualified Dhall           as D
-- Importing as qualified since Dhall exports functions such as 'maybe', 'bool', 'bool'

data OS
    = MacOS
    | Windows
    | Linux

data Cluster
    = Mainnet
    | Testnet
    | Staging
    | Demo

renderOS :: OS -> Text
renderOS MacOS   = "macos64"
renderOS Windows = "win64"
renderOS Linux   = "linux64"

renderCluster :: Cluster -> Text
renderCluster Mainnet = "mainnet"
renderCluster Testnet = "testnet"
renderCluster Staging = "staging"
renderCluster Demo    = "demo"


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

instance Interpret ClusterConfig where
    autoWith _ = clusterConfig

-- > Unfortunatly, there's no monad instance for 'Dhall.Type', perhaps use ApplicativeDo?
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

data OSConfig = OSConfig {
      osName              :: !Text
    , osConfigurationYaml :: !Text
    , osInstallDirectory  :: !Text
    , osMacPackageName    :: !Text
    , osX509ToolPath      :: !Text
    , osNodeArgs          :: !NodeArgs
    , osPass              :: !Pass
    } deriving (Eq, Show)

instance Interpret OSConfig where
    autoWith _ = osConfig

osConfig :: D.Type OSConfig
osConfig = D.record
    ( OSConfig
        <$> D.field "name" D.strictText
        <*> D.field "configurationYaml" D.strictText
        <*> D.field "installDirectory" D.strictText
        <*> D.field "macPackageName" D.strictText
        <*> D.field "x509ToolPath" D.strictText
        <*> D.field "nodeArgs" nodeArgs
        <*> D.field "pass" Dhall.Types.pass
    )

data NodeArgs = NodeArgs {
      naKeyfile          :: Text
    , naLogsPrefix       :: Text
    , naTopology         :: Text
    , naUpdateLatestPath :: Text
    , naWalletDBPath     :: Text
    , naTlsPath          :: Text
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

instance Interpret Pass where
    autoWith _ = Dhall.Types.pass

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
        <*> D.field "pass" Dhall.Types.pass
    )

instance Interpret Launcher where
    autoWith _ = launcher

data LauncherConfig = LauncherConfig {
      lcfgFilePath    :: !Text
    , lcfgKey         :: !Text
    , lcfgSystemStart :: Maybe Natural
    , lcfgSeed        :: Maybe Natural
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

newtype Topology = Topology WalletConfig
    deriving (Eq, Show)

topology :: D.Type Topology
topology = D.record
    (Topology <$> D.field "wallet" walletConfig)

instance Interpret Topology where
    autoWith _ = topology

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

newtype Host = Host { getHost :: Text}
    deriving (Eq, Show)

host :: D.Type Host
host = D.record
    ( Host <$> D.field "host" D.strictText)

instance Interpret Host where
    autoWith _ = host

data InstallerConfig = InstallerConfig {
      icfgInstallDirectory :: !Text
    , icfgMacPackageName   :: !Text
    , icfgWalletPort       :: !Natural   
    }

instance Interpret InstallerConfig where
    autoWith _ = installerConfig

installerConfig :: D.Type InstallerConfig
installerConfig = D.record
    ( InstallerConfig
        <$> D.field "installDirectory" D.strictText
        <*> D.field "macPackageName" D.strictText
        <*> D.field "walletPort" D.natural
    )