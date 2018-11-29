{-# LANGUAGE DeriveGeneric     #-}
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

import           Cardano.Prelude hiding (evalState)

import           Control.Monad.Trans.State.Strict (evalState)
import           Data.Functor.Contravariant (contramap)
import qualified Data.Text as T
import           Dhall (Inject (..), Interpret (..), InterpretOptions (..),
                        auto, defaultInterpretOptions, field, genericAutoWith,
                        genericInjectWith, record, strictText)
import           GHC.Generics (from, to)

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
renderOS Linux64 = "linux64"
renderOS Macos64 = "macos64"
renderOS Win64   = "win64"

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
    } deriving (Eq, Generic, Show)

-- Defining each 'Intrepret' instance.
instance Interpret ClusterConfig where
    autoWith _ = fmap GHC.Generics.to (evalState (genericAutoWith options) 1)
      where
        options = defaultInterpretOptions {fieldModifier = lowerHead . T.drop 4}

instance Inject ClusterConfig where
    injectWith _ = contramap GHC.Generics.from (evalState (genericInjectWith options) 1)
      where
        options = defaultInterpretOptions {fieldModifier = lowerHead . T.drop 4}

-- | OS configuration
data OSConfig = OSConfig
    { osName              :: !Text
    , osConfigurationYaml :: !Text
    , osInstallDirectory  :: !Text
    , osX509ToolPath      :: !Text
    , osNodeArgs          :: !NodeArgs
    , osPass              :: !Pass
    } deriving (Eq, Generic, Show)

instance Interpret OSConfig where
    autoWith _ = fmap GHC.Generics.to (evalState (genericAutoWith options) 1)
      where
        options = defaultInterpretOptions {fieldModifier = lowerHead . T.drop 2}

instance Inject OSConfig where
    injectWith _ = contramap GHC.Generics.from (evalState (genericInjectWith options) 1)
      where
        options = defaultInterpretOptions {fieldModifier = lowerHead . T.drop 2}

-- | Node arguments
data NodeArgs = NodeArgs
    { naKeyfile          :: !Text
    , naLogsPrefix       :: !Text
    , naTopology         :: !Text
    , naUpdateLatestPath :: !Text
    , naWalletDBPath     :: !Text
    , naTlsPath          :: !Text
    } deriving (Eq, Generic, Show)

instance Interpret NodeArgs where
    autoWith _ = fmap GHC.Generics.to (evalState (genericAutoWith options) 1)
      where
        options = defaultInterpretOptions {fieldModifier = lowerHead . T.drop 2}

instance Inject NodeArgs where
    injectWith _ = contramap GHC.Generics.from (evalState (genericInjectWith options) 1)
      where
        options = defaultInterpretOptions {fieldModifier = lowerHead . T.drop 2}

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
    } deriving (Eq, Generic, Show)

instance Interpret Pass where
    autoWith _ = fmap GHC.Generics.to (evalState (genericAutoWith options) 1)
      where
        options = defaultInterpretOptions {fieldModifier = lowerHead . T.drop 1}

instance Inject Pass where
    injectWith _ = contramap GHC.Generics.from (evalState (genericInjectWith options) 1)
      where
        options = defaultInterpretOptions {fieldModifier = lowerHead . T.drop 1}

-- | Launcher configuration
data LauncherConfig = LauncherConfig
    { lcfgFilePath    :: !Text
    , lcfgKey         :: !Text
    , lcfgSystemStart :: !(Maybe Natural)
    , lcfgSeed        :: !(Maybe Natural)
    } deriving (Eq, Generic, Show)

instance Interpret LauncherConfig where
    autoWith _ = fmap GHC.Generics.to (evalState (genericAutoWith options) 1)
      where
        options = defaultInterpretOptions {fieldModifier = lowerHead . T.drop 4}

instance Inject LauncherConfig where
    injectWith _ = contramap GHC.Generics.from (evalState (genericInjectWith options) 1)
      where
        options = defaultInterpretOptions {fieldModifier = lowerHead . T.drop 4}

-- | Topology configuration
newtype TopologyConfig = TopologyConfig {
      getWalletConfig :: WalletConfig
    } deriving (Eq, Generic, Show)

instance Interpret TopologyConfig where
    autoWith _ = record
        (TopologyConfig <$> field "wallet" auto)

instance Inject TopologyConfig where
    injectWith _ = contramap GHC.Generics.from (evalState (genericInjectWith options) 1)
      where
        options = defaultInterpretOptions {fieldModifier = replaceWithWallet}
        replaceWithWallet :: Text -> Text
        replaceWithWallet "getWalletConfig" = "wallet"
        replaceWithWallet text              = text

-- | Wallet configuration
data WalletConfig = WalletConfig
    { wcfgRelays    :: ![[Host]]
    , wcfgValency   :: !Natural
    , wcfgFallbacks :: !Natural
    } deriving (Eq, Generic, Show)

instance Interpret WalletConfig where
    autoWith _ = fmap GHC.Generics.to (evalState (genericAutoWith options) 1)
      where
        options = defaultInterpretOptions {fieldModifier = lowerHead . T.drop 4}

instance Inject WalletConfig where
    injectWith _ = contramap GHC.Generics.from (evalState (genericInjectWith options) 1)
      where
        options = defaultInterpretOptions {fieldModifier = lowerHead . T.drop 4}

-- | Host
newtype Host = Host {
    getHost :: Text
    } deriving (Eq, Generic, Show)

instance Interpret Host where
    autoWith _ = record
        (Host <$> field "host" strictText)

instance Inject Host where
    injectWith _ = contramap GHC.Generics.from (evalState (genericInjectWith options) 1)
      where
        options = defaultInterpretOptions {fieldModifier = replaceWithHost}
        replaceWithHost :: Text -> Text
        replaceWithHost "getHost" = "host"
        replaceWithHost text      = text


-- | Installer configuration
data InstallerConfig = InstallerConfig
    { icfgInstallDirectory :: !Text
    , icfgWalletPort       :: !Natural
    } deriving (Eq, Generic, Show)

instance Interpret InstallerConfig where
    autoWith _ = fmap GHC.Generics.to (evalState (genericAutoWith options) 1)
      where
        options = defaultInterpretOptions {fieldModifier = lowerHead . T.drop 4}

instance Inject InstallerConfig where
    injectWith _ = contramap GHC.Generics.from (evalState (genericInjectWith options) 1)
      where
        options = defaultInterpretOptions {fieldModifier = lowerHead . T.drop 4}

-- | Launcher configuration
data Launcher = Launcher
    { lConfiguration     :: !LauncherConfig
    , lNodeDbPath        :: !Text
    , lNodeLogConfig     :: !Text
    , lUpdaterPath       :: !Text
    , lUpdaterArgs       :: ![Text]
    , lUpdateArchive     :: !(Maybe Text)
    , lReportServer      :: !Text
    , lX509ToolPath      :: !Text
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
    , lUpdateWithPackage :: !Bool
    } deriving (Eq, Generic, Show)

instance Interpret Launcher where
    autoWith opts = fmap GHC.Generics.to (evalState (genericAutoWith options) 1)
      where
        options = opts {fieldModifier = lowerHead . T.drop 1}

instance Inject Launcher where
    injectWith opts = contramap GHC.Generics.from (evalState (genericInjectWith options) 1)
      where
        options = opts {fieldModifier = lowerHead . T.drop 1}

lowerHead :: T.Text -> T.Text
lowerHead str = T.toLower (T.take 1 str) <> T.drop 1 str
