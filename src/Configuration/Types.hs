{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}

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
import           Dhall (GenericInject, GenericInterpret, Inject (..), InputType,
                        Interpret (..), InterpretOptions (..), Type, auto,
                        field, genericAutoWith, genericInjectWith, record,
                        strictText)
import           GHC.Generics (from, to)

import           Test.QuickCheck

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
    autoWith opt = interpretAutoWithOption $ opt {fieldModifier = lowerHead . T.drop 4}

instance Inject ClusterConfig where
    injectWith opt = injectAutoWithOption $ opt {fieldModifier = lowerHead . T.drop 4}


instance Arbitrary ClusterConfig where
    arbitrary = do
        ccfgName                   <- genSafeText
        ccfgKeyPrefix              <- genSafeText
        ccfgRelays                 <- genSafeText
        ccfgUpdateServer           <- genSafeText
        ccfgReportServer           <- genSafeText
        ccfgInstallDirectorySuffix <- genSafeText
        ccfgMacPackageSuffix       <- genSafeText
        ccfgWalletPort             <- arbitrary

        pure ClusterConfig {..}

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
    autoWith opt = interpretAutoWithOption $ opt {fieldModifier = lowerHead . T.drop 2}

instance Inject OSConfig where
    injectWith opt = injectAutoWithOption $ opt {fieldModifier = lowerHead . T.drop 2}

instance Arbitrary OSConfig where
    arbitrary = do
        osName              <- elements ["windows64", "macos64", "linux64"]
        osConfigurationYaml <- genSafeText
        osInstallDirectory  <- genSafeText
        osX509ToolPath      <- genSafeText
        osNodeArgs          <- arbitrary
        osPass              <- arbitrary

        pure OSConfig{..}

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
    autoWith opt = interpretAutoWithOption $ opt {fieldModifier = lowerHead . T.drop 2}

instance Inject NodeArgs where
    injectWith opt = injectAutoWithOption $ opt {fieldModifier = lowerHead . T.drop 2}

instance Arbitrary NodeArgs where
    arbitrary = do
        naKeyfile          <- genSafeText
        naLogsPrefix       <- genSafeText
        naTopology         <- genSafeText
        naUpdateLatestPath <- genSafeText
        naWalletDBPath     <- genSafeText
        naTlsPath          <- genSafeText

        pure NodeArgs{..}

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
    autoWith opt = interpretAutoWithOption $ opt {fieldModifier = lowerHead . T.drop 1}

instance Inject Pass where
    injectWith opt = injectAutoWithOption $ opt {fieldModifier = lowerHead . T.drop 1}

instance Arbitrary Pass where
    arbitrary = do
        pStatePath           <- genSafeText
        pNodePath            <- genSafeText
        pNodeDbPath          <- genSafeText
        pNodeLogConfig       <- genSafeText
        pNodeLogPath         <- maybeOf genSafeText
        pWalletPath          <- genSafeText
        pWalletLogging       <- arbitrary
        pWorkingDir          <- genSafeText
        pFrontendOnlyMode    <- arbitrary
        pUpdaterPath         <- genSafeText
        pUpdaterArgs         <- listOf genSafeText
        pUpdateArchive       <- maybeOf genSafeText
        pUpdateWindowsRunner <- maybeOf genSafeText
        pLauncherLogsPrefix  <- genSafeText

        pure Pass{..}
-- | Launcher configuration
data LauncherConfig = LauncherConfig
    { lcfgFilePath    :: !Text
    , lcfgKey         :: !Text
    , lcfgSystemStart :: !(Maybe Natural)
    , lcfgSeed        :: !(Maybe Natural)
    } deriving (Eq, Generic, Show)

instance Interpret LauncherConfig where
    autoWith opt = interpretAutoWithOption $ opt {fieldModifier = lowerHead . T.drop 4}

instance Inject LauncherConfig where
    injectWith opt = injectAutoWithOption $ opt {fieldModifier = lowerHead . T.drop 4}

instance Arbitrary LauncherConfig where
    arbitrary = do
        lcfgFilePath    <- genSafeText
        lcfgKey         <- genSafeText
        lcfgSystemStart <- arbitrary
        lcfgSeed        <- arbitrary

        pure LauncherConfig{..}

-- | Topology configuration
newtype TopologyConfig = TopologyConfig {
      getWalletConfig :: WalletConfig
    } deriving (Eq, Generic, Show)

instance Interpret TopologyConfig where
    autoWith _ = record
        (TopologyConfig <$> field "wallet" auto)

instance Inject TopologyConfig where
    injectWith opt = injectAutoWithOption $ options
      where
        options :: InterpretOptions
        options = opt {fieldModifier = replaceWithWallet}
        replaceWithWallet :: Text -> Text
        replaceWithWallet "getWalletConfig" = "wallet"
        replaceWithWallet text              = text

instance Arbitrary TopologyConfig where
    arbitrary = TopologyConfig <$> arbitrary

-- | Wallet configuration
data WalletConfig = WalletConfig
    { wcfgRelays    :: ![[Host]]
    , wcfgValency   :: !Natural
    , wcfgFallbacks :: !Natural
    } deriving (Eq, Generic, Show)

instance Interpret WalletConfig where
    autoWith opt = interpretAutoWithOption $ opt {fieldModifier = lowerHead . T.drop 4}

instance Inject WalletConfig where
    injectWith opt = injectAutoWithOption $ opt {fieldModifier = lowerHead . T.drop 4}

instance Arbitrary WalletConfig where
    arbitrary = do
        wcfgRelays    <- arbitrary
        wcfgValency   <- arbitrary
        wcfgFallbacks <- arbitrary

        pure WalletConfig{..}
-- | Host
newtype Host = Host {
    getHost :: Text
    } deriving (Eq, Generic, Show)

instance Interpret Host where
    autoWith _ = record
        (Host <$> field "host" strictText)

instance Inject Host where
    injectWith opt = injectAutoWithOption $ options
      where
        options = opt {fieldModifier = replaceWithHost}
        replaceWithHost :: Text -> Text
        replaceWithHost "getHost" = "host"
        replaceWithHost text      = text

instance Arbitrary Host where
    arbitrary = Host <$> genSafeText

-- | Installer configuration
data InstallerConfig = InstallerConfig
    { icfgInstallDirectory :: !Text
    , icfgWalletPort       :: !Natural
    } deriving (Eq, Generic, Show)

instance Interpret InstallerConfig where
    autoWith opt = interpretAutoWithOption $ opt {fieldModifier = lowerHead . T.drop 4}

instance Inject InstallerConfig where
    injectWith opt = injectAutoWithOption $ opt {fieldModifier = lowerHead . T.drop 4}

instance Arbitrary InstallerConfig where
    arbitrary = do
        icfgInstallDirectory <- genSafeText
        icfgWalletPort       <- arbitrary

        pure InstallerConfig{..}

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
    autoWith opt = interpretAutoWithOption $ opt {fieldModifier = lowerHead . T.drop 1}

instance Inject Launcher where
    injectWith opt = injectAutoWithOption $ opt {fieldModifier = lowerHead . T.drop 1}

instance Arbitrary Launcher where
    arbitrary = do
        lConfiguration     <- arbitrary
        lNodeDbPath        <- genSafeText
        lNodeLogConfig     <- genSafeText
        lUpdaterPath       <- genSafeText
        lUpdaterArgs       <- listOf genSafeText
        lUpdateArchive     <- maybeOf genSafeText 
        lReportServer      <- genSafeText
        lX509ToolPath      <- genSafeText
        lLogsPrefix        <- genSafeText
        lTlsca             <- genSafeText
        lTlscert           <- genSafeText
        lTlsKey            <- genSafeText
        lNoClientAuth      <- arbitrary
        lLogConsoleOff     <- arbitrary
        lUpdateServer      <- genSafeText
        lKeyFile           <- genSafeText
        lTopology          <- genSafeText
        lWalletDbPath      <- genSafeText
        lUpdateLatestPath  <- genSafeText
        lWalletAddress     <- genSafeText
        lUpdateWithPackage <- arbitrary

        pure Launcher{..}

-- | Lowercase given text's first letter
lowerHead :: T.Text -> T.Text
lowerHead str = T.toLower (T.take 1 str) <> T.drop 1 str

instance Arbitrary Natural where
    arbitrary = fromInteger <$> choose (0,1000000)

-- | Generate random ascii string
genSafeText :: Gen Text
genSafeText = mconcat <$> listOf genSafeChar
  where
    genSafeChar :: Gen Text
    genSafeChar = T.singleton <$> elements (['a'..'z'] <> ['0' .. '9'])

-- | Wrap given generator with 'Maybe'
maybeOf :: Gen a -> Gen (Maybe a)
maybeOf generator = do
    random <- generator
    elements [Nothing, Just random]

-- | Define type class instance of 'Interpret' with given 'InterpretOptions'
interpretAutoWithOption :: (Generic a, GenericInterpret (Rep a))
                        => InterpretOptions
                        -> Dhall.Type a
interpretAutoWithOption opt = fmap GHC.Generics.to (evalState (genericAutoWith opt) 1)

-- | Define type class instance of 'Inject' with given 'InterpretOptions'
injectAutoWithOption :: (Generic a, GenericInject (Rep a))
                     => InterpretOptions
                     -> InputType a
injectAutoWithOption opt = contramap GHC.Generics.from (evalState (genericInjectWith opt) 1)
