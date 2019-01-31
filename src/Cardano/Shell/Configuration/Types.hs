{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}

module Cardano.Shell.Configuration.Types
    ( Cluster(..)
    , ClusterConfig(..)
    , Host(..)
    , InstallerConfig (..)
    , Launcher(..)
    , LauncherConfig(..)
    , NodeArgs(..)
    , OS(..)
    , OSConfig(..)
    , Param(..)
    , TopologyConfig(..)
    , WalletTopologyConfig(..)
    , renderOS
    , renderCluster

    -- * Feature configs
    , LoggingConfig(..)
    , BlockchainConfig(..)
    , NetworkConfig(..)
    , WalletConfig(..)

    -- * Fields
    , ConfigurationYamlPath(..)
    , KeyFile(..)
    , StatePath(..)
    , NodePath(..)
    , NodeDbPath(..)
    , LogPrefix(..)
    , NodeLogConfig(..)
    , NodeLogPath(..)
    , WorkingDir(..)
    , LauncherLogsPrefix(..)
    , LogConsoleOff(..)
    , Topology(..)
    , X509ToolPath(..)
    , Valency(..)
    , Fallback(..)
    , TlsPath(..)
    , Tlsca(..)
    , Tlscert(..)
    , Tlskey(..)
    , WalletDbPath(..)
    , WalletPath(..)
    , WalletLogging(..)
    , WalletPort(..)
    , WalletAddress(..)
    , WalletRelays(..)
    , WalletFallback(..)
    , WalletValency(..)
    ) where

import           Cardano.Prelude hiding (evalState, maybe)

import           Control.Monad.Trans.State.Strict (evalState)
import           Data.Functor.Contravariant (contramap)
import qualified Data.Text as T
import           Dhall (GenericInject, Inject (..), InputType, Interpret (..),
                        InterpretOptions (..), auto, field, genericInjectWith,
                        record)
import           GHC.Generics (from)
import           Test.QuickCheck (Arbitrary (..), Gen, arbitraryASCIIChar,
                                  elements, listOf, listOf1)

-- | Operating system
data OS
    = Linux64
    | Macos64
    | Win64
    deriving (Bounded, Enum, Eq, Read, Show)

instance Arbitrary OS where
    arbitrary = elements [Linux64 .. Win64]

-- | Cluster
data Cluster
    = Mainnet
    | Staging
    | Testnet
    | Demo
    deriving (Bounded, Enum, Eq, Read, Show)

instance Arbitrary Cluster where
    arbitrary = elements [Mainnet .. Demo]

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
    , ccfgWalletPort             :: !Integer
    } deriving (Eq, Generic, Show)

-- Defining each 'Intrepret' instance.
instance Interpret ClusterConfig

instance Inject ClusterConfig


instance Arbitrary ClusterConfig where
    arbitrary = do
        name                   <- genSafeText
        keyPrefix              <- genSafeText
        relays                 <- genSafeText
        updateServer           <- genSafeText
        reportServer           <- genSafeText
        installDirectorySuffix <- genSafeText
        macPackageSuffix       <- genSafeText
        walletport             <- arbitrary

        pure $ ClusterConfig
            { ccfgName                   = name
            , ccfgKeyPrefix              = keyPrefix
            , ccfgRelays                 = relays
            , ccfgUpdateServer           = updateServer
            , ccfgReportServer           = reportServer
            , ccfgInstallDirectorySuffix = installDirectorySuffix
            , ccfgMacPackageSuffix       = macPackageSuffix
            , ccfgWalletPort             = walletport
            }

-- | OS configuration
data OSConfig = OSConfig
    { osName              :: !Text
    , osConfigurationYaml :: !Text
    , osInstallDirectory  :: !Text
    , osX509ToolPath      :: !Text
    , osNodeArgs          :: !NodeArgs
    , osPass              :: !Param
    } deriving (Eq, Generic, Show)

instance Interpret OSConfig

instance Inject OSConfig

instance Arbitrary OSConfig where
    arbitrary = do
        name              <- elements $ map renderOS [Linux64, Macos64, Win64]
        configurationYaml <- genSafeText
        installDirectory  <- genSafeText
        x509ToolPath      <- genSafeText
        nodeArgs          <- arbitrary
        paths             <- arbitrary

        pure $ OSConfig
            { osName              = name
            , osConfigurationYaml = configurationYaml
            , osInstallDirectory  = installDirectory
            , osX509ToolPath      = x509ToolPath
            , osNodeArgs          = nodeArgs
            , osPass              = paths
            }

-- | Node arguments
data NodeArgs = NodeArgs
    { naKeyfile          :: !Text
    , naLogsPrefix       :: !Text
    , naTopology         :: !Text
    , naUpdateLatestPath :: !Text
    , naWalletDBPath     :: !Text
    , naTlsPath          :: !Text
    } deriving (Eq, Generic, Show)

instance Interpret NodeArgs

instance Inject NodeArgs

instance Arbitrary NodeArgs where
    arbitrary = do
        keyfile          <- genSafeText
        logsPrefix       <- genSafeText
        topology         <- genSafeText
        updateLatestPath <- genSafeText
        walletDBPath     <- genSafeText
        tlsPath          <- genSafeText

        pure NodeArgs
            { naKeyfile          = keyfile
            , naLogsPrefix       = logsPrefix
            , naTopology         = topology
            , naUpdateLatestPath = updateLatestPath
            , naWalletDBPath     = walletDBPath
            , naTlsPath          = tlsPath
            }

-- | Params
data Param = Param
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

instance Interpret Param

instance Inject Param

instance Arbitrary Param where
    arbitrary = do
        statePath           <- genSafeText
        nodePath            <- genSafeText
        nodeDbPath          <- genSafeText
        nodeLogConfig       <- genSafeText
        nodeLogPath         <- maybeOf genSafeText
        walletpath          <- genSafeText
        walletlogging       <- arbitrary
        workingDir          <- genSafeText
        frontendOnlyMode    <- arbitrary
        updaterPath         <- genSafeText
        updaterArgs         <- listOf genSafeText
        updateArchive       <- maybeOf genSafeText
        updateWindowsRunner <- maybeOf genSafeText
        launcherLogsPrefix  <- genSafeText

        pure Param
            { pStatePath           = statePath
            , pNodePath            = nodePath
            , pNodeDbPath          = nodeDbPath
            , pNodeLogConfig       = nodeLogConfig
            , pNodeLogPath         = nodeLogPath
            , pWalletPath          = walletpath
            , pWalletLogging       = walletlogging
            , pWorkingDir          = workingDir
            , pFrontendOnlyMode    = frontendOnlyMode
            , pUpdaterPath         = updaterPath
            , pUpdaterArgs         = updaterArgs
            , pUpdateArchive       = updateArchive
            , pUpdateWindowsRunner = updateWindowsRunner
            , pLauncherLogsPrefix  = launcherLogsPrefix
            }

-- | Launcher configuration
data LauncherConfig = LauncherConfig
    { lcfgFilePath    :: !Text
    , lcfgKey         :: !Text
    , lcfgSystemStart :: !(Maybe Integer)
    , lcfgSeed        :: !(Maybe Integer)
    } deriving (Eq, Generic, Show)

instance Interpret LauncherConfig

instance Inject LauncherConfig

instance Arbitrary LauncherConfig where
    arbitrary = do
        filePath    <- genSafeText
        key         <- genSafeText
        systemStart <- arbitrary
        seed        <- arbitrary

        pure LauncherConfig
            { lcfgFilePath    = filePath
            , lcfgKey         = key
            , lcfgSystemStart = systemStart
            , lcfgSeed        = seed
            }

-- | Topology configuration
newtype TopologyConfig = TopologyConfig {
      getWalletTopologyConfig :: WalletTopologyConfig
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
        replaceWithWallet "getWalletTopologyConfig" = "wallet"
        replaceWithWallet text                      = text

instance Arbitrary TopologyConfig where
    arbitrary = TopologyConfig <$> arbitrary

-- | Wallet configuration
data WalletTopologyConfig = WalletTopologyConfig
    { wtcfgRelays    :: ![[Host]]
    , wtcfgValency   :: !Integer
    , wtcfgFallbacks :: !Integer
    } deriving (Eq, Generic, Show)

instance Interpret WalletTopologyConfig

instance Inject WalletTopologyConfig

instance Arbitrary WalletTopologyConfig where
    arbitrary = do
        relays    <- arbitrary
        valency   <- arbitrary
        fallbacks <- arbitrary

        pure WalletTopologyConfig
            { wtcfgRelays    = relays
            , wtcfgValency   = valency
            , wtcfgFallbacks = fallbacks
            }

-- | Host
newtype Host = Host {
    getHost :: Text
    } deriving (Eq, Generic, Show)

instance Interpret Host

instance Inject Host

instance Arbitrary Host where
    arbitrary = Host <$> genSafeText

-- | Installer configuration
newtype InstallerConfig = InstallerConfig
    { icfgInstallDirectory :: Text
    } deriving (Eq, Generic, Show)

instance Interpret InstallerConfig

instance Inject InstallerConfig

instance Arbitrary InstallerConfig where
    arbitrary = do
        installDirectory <- genSafeText

        pure InstallerConfig
            { icfgInstallDirectory = installDirectory
            }

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

instance Interpret Launcher
instance Inject Launcher

instance Arbitrary Launcher where
    arbitrary = do
        configuration     <- arbitrary
        nodeDbPath        <- genSafeText
        nodeLogConfig     <- genSafeText
        updaterPath       <- genSafeText
        updaterArgs       <- listOf genSafeText
        updateArchive     <- maybeOf genSafeText
        reportServer      <- genSafeText
        x509ToolPath      <- genSafeText
        logsPrefix        <- genSafeText
        tlsca             <- genSafeText
        tlscert           <- genSafeText
        tlsKey            <- genSafeText
        noClientAuth      <- arbitrary
        logConsoleOff     <- arbitrary
        updateServer      <- genSafeText
        keyFile           <- genSafeText
        topology          <- genSafeText
        walletdbPath      <- genSafeText
        updateLatestPath  <- genSafeText
        walletaddress     <- genSafeText
        updateWithPackage <- arbitrary

        pure Launcher
            { lConfiguration     = configuration
            , lNodeDbPath        = nodeDbPath
            , lNodeLogConfig     = nodeLogConfig
            , lUpdaterPath       = updaterPath
            , lUpdaterArgs       = updaterArgs
            , lUpdateArchive     = updateArchive
            , lReportServer      = reportServer
            , lX509ToolPath      = x509ToolPath
            , lLogsPrefix        = logsPrefix
            , lTlsca             = tlsca
            , lTlscert           = tlscert
            , lTlsKey            = tlsKey
            , lNoClientAuth      = noClientAuth
            , lLogConsoleOff     = logConsoleOff
            , lUpdateServer      = updateServer
            , lKeyFile           = keyFile
            , lTopology          = topology
            , lWalletDbPath      = walletdbPath
            , lUpdateLatestPath  = updateLatestPath
            , lWalletAddress     = walletaddress
            , lUpdateWithPackage = updateWithPackage
            }

--------------------------------------------------------------------------------
-- Newtypes
--------------------------------------------------------------------------------

newtype ConfigurationYamlPath = ConfigurationYamlPath {
    getConfigurationYamlPath :: Text
    } deriving (Eq, Show, Generic)

instance Interpret ConfigurationYamlPath
instance Inject ConfigurationYamlPath

instance Arbitrary ConfigurationYamlPath where
    arbitrary = ConfigurationYamlPath <$> genSafeText

newtype KeyFile = KeyFile {
    getKeyFile :: Text
    } deriving (Eq, Show, Generic)

instance Interpret KeyFile
instance Inject KeyFile

instance Arbitrary KeyFile where
    arbitrary = KeyFile <$> genSafeText

newtype StatePath = StatePath {
    getStatePath :: Text
    } deriving (Eq, Show, Generic)

instance Interpret StatePath
instance Inject StatePath

instance Arbitrary StatePath where
    arbitrary = StatePath <$> genSafeText

newtype NodePath = NodePath {
    getNodePath :: Text
    } deriving (Eq, Show, Generic)

instance Interpret NodePath
instance Inject NodePath

instance Arbitrary NodePath where
    arbitrary = NodePath <$> genSafeText

newtype NodeDbPath = NodeDbPath {
    getNodeDbPath :: Text
    } deriving (Eq, Show, Generic)

instance Interpret NodeDbPath
instance Inject NodeDbPath

instance Arbitrary NodeDbPath where
    arbitrary = NodeDbPath <$> genSafeText

newtype LogPrefix = LogPrefix {
    getLogPrefix :: Text
    } deriving (Eq, Show, Generic)

instance Interpret LogPrefix
instance Inject LogPrefix

instance Arbitrary LogPrefix where
    arbitrary = LogPrefix <$> genSafeText

newtype NodeLogConfig = NodeLogConfig {
    getNodeLogConfig :: Text
    } deriving (Eq, Show, Generic)

instance Interpret NodeLogConfig
instance Inject NodeLogConfig

instance Arbitrary NodeLogConfig where
    arbitrary = NodeLogConfig <$> genSafeText

newtype NodeLogPath = NodeLogPath {
    getNodeLogPath :: Maybe Text
    } deriving (Eq, Show, Generic)

instance Interpret NodeLogPath
instance Inject NodeLogPath

instance Arbitrary NodeLogPath where
    arbitrary = NodeLogPath <$> maybeOf genSafeText

newtype WorkingDir = WorkingDir {
    getWorkingDir :: Text
    } deriving (Eq, Show, Generic)

instance Interpret WorkingDir
instance Inject WorkingDir

instance Arbitrary WorkingDir where
    arbitrary = WorkingDir <$> genSafeText

newtype LauncherLogsPrefix = LauncherLogsPrefix {
    getLauncherLogsPrefix :: Text
    } deriving (Eq, Show, Generic)

instance Interpret LauncherLogsPrefix
instance Inject LauncherLogsPrefix

instance Arbitrary LauncherLogsPrefix where
    arbitrary = LauncherLogsPrefix <$> genSafeText

newtype LogConsoleOff = LogConsoleOff {
    getLogConsoleOff :: Bool
    } deriving (Eq, Show, Generic)

instance Interpret LogConsoleOff
instance Inject LogConsoleOff

instance Arbitrary LogConsoleOff where
    arbitrary = LogConsoleOff <$> arbitrary

newtype Topology = Topology {
    getTopology :: Text
    } deriving (Eq, Show, Generic)

instance Interpret Topology
instance Inject Topology

instance Arbitrary Topology where
    arbitrary = Topology <$> genSafeText

newtype X509ToolPath = X509ToolPath {
    getX509ToolPath :: Text
    } deriving (Eq, Show, Generic)

instance Interpret X509ToolPath
instance Inject X509ToolPath

instance Arbitrary X509ToolPath where
    arbitrary = X509ToolPath <$> genSafeText

newtype TlsPath = TlsPath {
    getTlsPath :: Text
    } deriving (Eq, Show, Generic)

instance Interpret TlsPath
instance Inject TlsPath

instance Arbitrary TlsPath where
    arbitrary = TlsPath <$> genSafeText

newtype Valency = Valency {
    getValency :: Integer
    } deriving (Eq, Show, Generic)

instance Interpret Valency
instance Inject Valency

instance Arbitrary Valency where
    arbitrary = Valency <$> arbitrary

newtype Fallback = Fallback {
    getFallback :: Integer
    } deriving (Eq, Show, Generic)

instance Interpret Fallback
instance Inject Fallback

instance Arbitrary Fallback where
    arbitrary = Fallback <$> arbitrary

newtype Tlsca = Tlsca {
    getTlsca :: Text
    } deriving (Eq, Show, Generic)

instance Interpret Tlsca
instance Inject Tlsca

instance Arbitrary Tlsca where
    arbitrary = Tlsca <$> genSafeText

newtype Tlscert = Tlscert {
    getTlscert :: Text
    } deriving (Eq, Show, Generic)

instance Interpret Tlscert
instance Inject Tlscert

instance Arbitrary Tlscert where
    arbitrary = Tlscert <$> genSafeText

newtype Tlskey = Tlskey {
    getTlskey :: Text
    } deriving (Eq, Show, Generic)

instance Interpret Tlskey
instance Inject Tlskey

instance Arbitrary Tlskey where
    arbitrary = Tlskey <$> genSafeText

newtype WalletDbPath = WalletDbPath {
    getDbPath :: Text
    } deriving (Eq, Show, Generic)

instance Interpret WalletDbPath
instance Inject WalletDbPath

instance Arbitrary WalletDbPath where
    arbitrary = WalletDbPath <$> genSafeText

newtype WalletPath = WalletPath {
    getWalletPath :: Text
    } deriving (Eq, Show, Generic)

instance Interpret WalletPath
instance Inject WalletPath

instance Arbitrary WalletPath where
    arbitrary = WalletPath <$> genSafeText

newtype WalletLogging = WalletLogging {
    getWalletLogging :: Bool
    } deriving (Eq, Show, Generic)

instance Interpret WalletLogging
instance Inject WalletLogging

instance Arbitrary WalletLogging where
    arbitrary = WalletLogging <$> arbitrary

newtype WalletPort = WalletPort {
    getWalletPort :: Integer
    } deriving (Eq, Show, Generic)

instance Interpret WalletPort
instance Inject WalletPort

instance Arbitrary WalletPort where
    arbitrary = WalletPort <$> arbitrary

newtype WalletAddress = WalletAddress {
    getWalletAddress :: Text
    } deriving (Eq, Show, Generic)

instance Interpret WalletAddress
instance Inject WalletAddress

instance Arbitrary WalletAddress where
    arbitrary = WalletAddress <$> genSafeText

newtype WalletRelays = WalletRelays {
    getWalletRelays :: [[Host]]
    } deriving (Eq, Show, Generic)

instance Interpret WalletRelays
instance Inject WalletRelays

instance Arbitrary WalletRelays where
    arbitrary = do
        someHost <- arbitrary
        return $ WalletRelays [[someHost]]

newtype WalletFallback = WalletFallback {
    getWalletFallback :: Integer
    } deriving (Eq, Show, Generic)

instance Interpret WalletFallback
instance Inject WalletFallback

instance Arbitrary WalletFallback where
    arbitrary = WalletFallback <$> arbitrary

newtype WalletValency = WalletValency {
    getWalletValency :: Integer
    } deriving (Eq, Show, Generic)

instance Interpret WalletValency
instance Inject WalletValency

instance Arbitrary WalletValency where
    arbitrary = WalletValency <$> arbitrary

--------------------------------------------------------------------------------
-- Modules/features
--------------------------------------------------------------------------------

-- | Configuration from Blockchain module
data BlockchainConfig = BlockchainConfig {
      blockchainConfigurationYaml :: !ConfigurationYamlPath
    , blockchainKeyFile           :: !KeyFile
    , blockchainStatePath         :: !StatePath
    , blockchainNodePath          :: !NodePath
    , blockchainNodeDbPath        :: !NodeDbPath
    } deriving (Eq, Generic, Show)

instance Interpret BlockchainConfig

instance Inject BlockchainConfig
instance Arbitrary BlockchainConfig where
    arbitrary = do
        yaml       <- arbitrary
        keyfile    <- arbitrary
        statePath  <- arbitrary
        nodepath   <- arbitrary
        nodedbpath <- arbitrary

        pure $ BlockchainConfig
            { blockchainConfigurationYaml = yaml
            , blockchainKeyFile           = keyfile
            , blockchainStatePath         = statePath
            , blockchainNodePath          = nodepath
            , blockchainNodeDbPath        = nodedbpath
            }

-- | Configuration for Logging module
data LoggingConfig = LoggingConfig {
      loggingConfigurationYaml  :: !ConfigurationYamlPath
    , loggingLogPrefix          :: !LogPrefix
    , loggingNodeLogConfig      :: !NodeLogConfig
    , loggingNodeLogPath        :: !NodeLogPath
    , loggingWorkingDir         :: !WorkingDir
    , loggingLauncherLogsPrefix :: !LauncherLogsPrefix
    , loggingLogConsoleOff      :: !LogConsoleOff
    } deriving (Eq, Generic, Show)

instance Interpret LoggingConfig
instance Inject LoggingConfig

instance Arbitrary LoggingConfig where
    arbitrary = do
        yaml          <- arbitrary
        prefix        <- arbitrary
        logConfig     <- arbitrary
        logPath       <- arbitrary
        workingDir    <- arbitrary
        logsPrefix    <- arbitrary
        logconsoleOff <- arbitrary

        pure $ LoggingConfig
            { loggingConfigurationYaml  = yaml
            , loggingLogPrefix          = prefix
            , loggingNodeLogConfig      = logConfig
            , loggingNodeLogPath        = logPath
            , loggingWorkingDir         = workingDir
            , loggingLauncherLogsPrefix = logsPrefix
            , loggingLogConsoleOff      = logconsoleOff
            }

-- | Configuration for Network module
data NetworkConfig = NetworkConfig
    { networkConfigurationYaml :: !ConfigurationYamlPath
    , networkTopology          :: !Topology
    , networkX509ToolPath      :: !X509ToolPath
    , networkHost              :: !Host
    , networkTlsPath           :: !TlsPath
    , networkTlsca             :: !Tlsca
    , networkTlscert           :: !Tlscert
    , networkTlskey            :: !Tlskey
    } deriving (Eq, Generic, Show)

instance Interpret NetworkConfig

instance Inject NetworkConfig

instance Arbitrary NetworkConfig where
    arbitrary = do
        yaml     <- arbitrary
        topology <- arbitrary
        x509path <- arbitrary
        tlspath  <- arbitrary
        host     <- arbitrary
        tlsca    <- arbitrary
        tlscert  <- arbitrary
        tlskey   <- arbitrary

        pure $ NetworkConfig
            { networkConfigurationYaml = yaml
            , networkTopology          = topology
            , networkX509ToolPath      = x509path
            , networkTlsPath           = tlspath
            , networkHost              = host
            , networkTlsca             = tlsca
            , networkTlscert           = tlscert
            , networkTlskey            = tlskey
            }

data WalletConfig = WalletConfig
    { walletDbPath   :: !WalletDbPath
    , walletPath     :: !WalletPath
    , walletLogging  :: !WalletLogging
    , walletPort     :: !WalletPort
    , walletAddress  :: !WalletAddress
    , walletRelays   :: !WalletRelays
    , walletFallback :: !WalletFallback
    , walletValency  :: !WalletValency
    } deriving (Eq, Generic, Show)

instance Interpret WalletConfig
instance Inject WalletConfig

instance Arbitrary WalletConfig where
    arbitrary = do
        dbpath   <- arbitrary
        path     <- arbitrary
        logging  <- arbitrary
        port     <- arbitrary
        address  <- arbitrary
        relays   <- arbitrary
        fallback <- arbitrary
        valency  <- arbitrary

        pure $ WalletConfig
            { walletDbPath   = dbpath
            , walletPath     = path
            , walletLogging  = logging
            , walletPort     = port
            , walletAddress  = address
            , walletRelays   = relays
            , walletFallback = fallback
            , walletValency  = valency
            }

--------------------------------------------------------------------------------
-- Auxiliary function
--------------------------------------------------------------------------------

-- | Generate random ascii string
genSafeText :: Gen Text
genSafeText = mconcat <$> listOf1 genSafeChar
  where
    genSafeChar :: Gen Text
    genSafeChar = T.singleton <$> arbitraryASCIIChar

-- | Wrap given generator with 'Maybe'
maybeOf :: Gen a -> Gen (Maybe a)
maybeOf generator = do
    random <- generator
    elements [Nothing, Just random]

-- | Define type class instance of 'Inject' with given 'InterpretOptions'
injectAutoWithOption :: (Generic a, GenericInject (Rep a))
                     => InterpretOptions
                     -> InputType a
injectAutoWithOption opt = contramap GHC.Generics.from (evalState (genericInjectWith opt) 1)
