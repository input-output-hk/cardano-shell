{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE FlexibleContexts  #-}
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
import           Dhall (GenericInject, GenericInterpret, Inject (..), InputType,
                        Interpret (..), InterpretOptions (..), Type, auto,
                        field, genericAutoWith, genericInjectWith, record,
                        strictText)
import           GHC.Generics (from, to)
import           Test.QuickCheck (Arbitrary (..), Gen, arbitraryASCIIChar,
                                  choose, elements, listOf, listOf1)

-- | Operating system
data OS
    = Linux64
    | Macos64
    | Win64
    deriving ( Eq, Read, Show)

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
        name                   <- genSafeText
        keyPrefix              <- genSafeText
        relays                 <- genSafeText
        updateServer           <- genSafeText
        reportServer           <- genSafeText
        installDirectorySuffix <- genSafeText
        macPackageSuffix       <- genSafeText
        walletPort             <- arbitrary

        pure $ ClusterConfig
            { ccfgName                   = name
            , ccfgKeyPrefix              = keyPrefix
            , ccfgRelays                 = relays
            , ccfgUpdateServer           = updateServer
            , ccfgReportServer           = reportServer
            , ccfgInstallDirectorySuffix = installDirectorySuffix
            , ccfgMacPackageSuffix       = macPackageSuffix
            , ccfgWalletPort             = walletPort
            }

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

instance Interpret NodeArgs where
    autoWith opt = interpretAutoWithOption $ opt {fieldModifier = lowerHead . T.drop 2}

instance Inject NodeArgs where
    injectWith opt = injectAutoWithOption $ opt {fieldModifier = lowerHead . T.drop 2}

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
        statePath           <- genSafeText
        nodePath            <- genSafeText
        nodeDbPath          <- genSafeText
        nodeLogConfig       <- genSafeText
        nodeLogPath         <- maybeOf genSafeText
        walletPath          <- genSafeText
        walletLogging       <- arbitrary
        workingDir          <- genSafeText
        frontendOnlyMode    <- arbitrary
        updaterPath         <- genSafeText
        updaterArgs         <- listOf genSafeText
        updateArchive       <- maybeOf genSafeText
        updateWindowsRunner <- maybeOf genSafeText
        launcherLogsPrefix  <- genSafeText

        pure Pass
            { pStatePath           = statePath
            , pNodePath            = nodePath
            , pNodeDbPath          = nodeDbPath
            , pNodeLogConfig       = nodeLogConfig
            , pNodeLogPath         = nodeLogPath
            , pWalletPath          = walletPath
            , pWalletLogging       = walletLogging
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
    , lcfgSystemStart :: !(Maybe Natural)
    , lcfgSeed        :: !(Maybe Natural)
    } deriving (Eq, Generic, Show)

instance Interpret LauncherConfig where
    autoWith opt = interpretAutoWithOption $ opt {fieldModifier = lowerHead . T.drop 4}

instance Inject LauncherConfig where
    injectWith opt = injectAutoWithOption $ opt {fieldModifier = lowerHead . T.drop 4}

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
        relays    <- arbitrary
        valency   <- arbitrary
        fallbacks <- arbitrary

        pure WalletConfig
            { wcfgRelays    = relays
            , wcfgValency   = valency
            , wcfgFallbacks = fallbacks
            }

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
        installDirectory <- genSafeText
        walletPort       <- arbitrary

        pure InstallerConfig
            { icfgInstallDirectory = installDirectory
            , icfgWalletPort       = walletPort
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

instance Interpret Launcher where
    autoWith opt = interpretAutoWithOption $ opt {fieldModifier = lowerHead . T.drop 1}

instance Inject Launcher where
    injectWith opt = injectAutoWithOption $ opt {fieldModifier = lowerHead . T.drop 1}

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
        walletDbPath      <- genSafeText
        updateLatestPath  <- genSafeText
        walletAddress     <- genSafeText
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
            , lWalletDbPath      = walletDbPath
            , lUpdateLatestPath  = updateLatestPath
            , lWalletAddress     = walletAddress
            , lUpdateWithPackage = updateWithPackage
            }

-- | Lowercase given text's first letter
lowerHead :: T.Text -> T.Text
lowerHead str = T.toLower (T.take 1 str) <> T.drop 1 str

instance Arbitrary Natural where
    arbitrary = fromInteger <$> choose (0,1000000)

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
