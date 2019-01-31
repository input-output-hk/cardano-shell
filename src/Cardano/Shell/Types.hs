module Cardano.Shell.Types
    ( CardanoConfiguration (..)
    , CardanoEnvironment (..)
    , CardanoFeature (..)
    , CardanoFeatureInit (..)
    , NoDependency (..)
    , ApplicationEnvironment (..)
    , CardanoApplication (..)
    , initializeCardanoEnvironment
    , loadCardanoConfiguration
    , applicationProductionMode
    , Core (..)
    , Genesis (..)
    , Spec (..)
    , Initializer (..)
    , TestBalance (..)
    , FakeAvvmBalance (..)
    , BlockVersionData (..)
    , LastKnownBlockVersion (..)
    , SoftForkRule (..)
    , TxFeePolicy (..)
    , TxSizeLinear (..)
    , ProtocolConstants (..)
    , NTP (..)
    , Update (..)
    , TXP (..)
    , SSC (..)
    , DLG (..)
    , Block (..)
    , Node (..)
    , TLS (..)
    , Wallet (..)
    , Throttle (..)
    , Certificate (..)
    ) where

import           Cardano.Prelude

import           Control.Concurrent.Classy (MonadConc)

import qualified System.Metrics as Ekg

-- | The top level module we use to run the key functions.
newtype CardanoApplication = CardanoApplication { runCardanoApplication :: IO () }

-- | The application environment.
data ApplicationEnvironment
    = Development
    | Production
    deriving (Eq, Show)

-- | A simple function to inform us.
applicationProductionMode :: ApplicationEnvironment -> Bool
applicationProductionMode Production = True
applicationProductionMode _          = False

-- | The common runtime environment for all features in the server.
-- All features have access to this environment.
data CardanoEnvironment = CardanoEnvironment
    { ceLogEnv   :: Text
    , ceEkgStore :: Ekg.Store
     -- ...
    }

-- | Initialise 'ServerEnv'
initializeCardanoEnvironment :: IO CardanoEnvironment
initializeCardanoEnvironment = do
    ekgStore <- Ekg.newStore
    return CardanoEnvironment
        { ceLogEnv      = "To implement"
        , ceEkgStore    = ekgStore
        }

loadCardanoConfiguration :: CardanoConfiguration -> IO CardanoConfiguration
loadCardanoConfiguration configuration = do
    pure $ configuration

-- | The option to not have any additional dependency for the @CardanoFeature@.
data NoDependency = NoDependency
    deriving (Eq, Show)

-- | The option to not have any additional configuration for the @CardanoFeature@.
data NoConfiguration = NoConfiguration
    deriving (Eq, Show)

-- | Cardano feature initialization.
-- We are saying "you have the responsibility to make sure you use the right context!".
data CardanoFeatureInit dependency configuration layer = CardanoFeatureInit
    { featureType                   :: !Text
    -- ^ The type of the feature that we use.
    , featureInit                   :: CardanoEnvironment -> dependency -> CardanoConfiguration -> configuration -> IO layer
    -- ^ Again, we are not sure how is the user going to run the actual feature,
    -- so we provide him with the most flexible/powerful context we have, @IO@.
    -- Notice the arrangement of the parameters - specific, general, specific, general, result.
    , featureCleanup                :: layer -> IO ()
    -- ^ If the user wants to clean up the resources after the module has completed running,
    -- there is an option to do so.
    }

-- | The interface for the running feature, the high-level interface we use for running it.
data CardanoFeature = CardanoFeature
    { featureName     :: Text
    -- ^ The name of the feature.
    , featureStart    :: forall m. (MonadIO m, MonadConc m) => m ()
    -- ^ What we call when we start the feature.
    , featureShutdown :: forall m. (MonadIO m, MonadConc m) => m ()
    -- ^ What we call when we shut down the feature.
    }

--------------------------------------------------------------------------------
-- Cardano Configuration Data Structures
--------------------------------------------------------------------------------
-- | The basic configuration structure. It should contain all the required
-- configuration parameters for the modules to work.

data CardanoConfiguration = CardanoConfiguration
    { ccLogPath             :: !FilePath
    -- ^ The location of the log files on the filesystem.
    , ccLogConfig           :: !FilePath
    -- ^ The location of the log configuration on the filesystem
    , ccDBPath              :: !FilePath
    -- ^ The location of the DB on the filesystem.
    , ccApplicationLockFile :: !FilePath
    -- ^ The location of the application lock file that is used
    -- as a semaphore se we can run just one application
    -- instance at a time.
    , ccCore                :: !Core
    , ccNTP                 :: !NTP
    , ccUpdate              :: !Update
    , ccTXP                 :: !TXP
    , ccSSC                 :: !SSC
    , ccDLG                 :: !DLG
    , ccBlock               :: !Block
    , ccNode                :: !Node
    , ccTLS                 :: !TLS
    , ccWallet              :: !Wallet
    } deriving (Eq, Show)

data Core = Core
    { coGenesis              :: !Genesis
    , coRequiresNetworkMagic :: !Text
      -- ^ Bool-isomorphic flag indicating whether we're on testnet
      -- or mainnet/staging.
    , coDBSerializeVersion   :: !Integer
      -- ^ Versioning for values in node's DB
    } deriving (Eq, Show)

data Genesis = Genesis { geInternal :: !Bool
                       , geSpec     :: !Spec
                       , geSrc      :: !FilePath
                       , geFileHash :: !Text
                       }
             deriving (Eq, Show)

data Spec = Spec
    { spInitializer       :: !Initializer
      -- ^ Other data which depend on genesis type.
    , spBlockVersionData  :: !BlockVersionData
      -- ^ Genesis 'BlockVersionData'.
    , spProtocolConstants :: !ProtocolConstants
      -- ^ Other constants which affect consensus.
    , spFTSSeed           :: !Text
      -- ^ Seed for FTS for 0-th epoch.
    , spHeavyDelegation   :: !Text
      -- ^ Genesis state of heavyweight delegation.
    , spAVVMDistr         :: !Text
      -- ^ Genesis data describes avvm utxo.
    } deriving (Eq, Show)

-- | This data type contains various options presense of which depends
-- on whether we want genesis for mainnet or testnet.
data Initializer = Initializer
    { inTestBalance       :: !TestBalance
    , inFakeAvvmBalance   :: !FakeAvvmBalance
    , inAVVMBalanceFactor :: !Int
    , inUseHeavyDlg       :: !Bool
    , inSeed              :: !Int
      -- ^ Seed to use to generate secret data. It's used only in
      -- testnet, shouldn't be used for anything important.
    } deriving (Eq, Show)

-- | These options determine balances of nodes specific for testnet.
data TestBalance = TestBalance
    { tePoors          :: !Int
      -- ^ Number of poor nodes (with small balance).
    , teRichmen        :: !Word
      -- ^ Number of rich nodes (with huge balance).
    , teRichmenShare   :: !Double
      -- ^ Portion of stake owned by all richmen together.
    , teUseHDAddresses :: !Bool
      -- ^ Whether generate plain addresses or with hd payload.
    , teTotalBalance   :: !Int
      -- ^ Total balance owned by these nodes.
    } deriving (Eq, Show)

-- | These options determines balances of fake AVVM nodes which didn't
-- really go through vending, but pretend they did.
data FakeAvvmBalance = FakeAvvmBalance
    { faCount      :: !Word
    , faOneBalance :: !Word64
    } deriving (Eq, Show)

-- | If we require options to automatically restart a module.
data ModuleAutoRestart
    = ModuleRestart
    | ModuleNoRestart
    deriving (Eq, Show)

data BlockVersionData = BlockVersionData
    { bvdScriptVersion     :: !Int
    , bvdSlotDuration      :: !Int
    , bvdMaxBlockSize      :: !Int
    , bvdMaxHeaderSize     :: !Int
    , bvdMaxTxSize         :: !Int
    , bvdMaxProposalSize   :: !Int
    , bvdMpcThd            :: !Float
    , bvdHeavyDelThd       :: !Float
    , bvdUpdateVoteThd     :: !Float
    , bvdUpdateProposalThd :: !Float
    , bvdUpdateImplicit    :: !Int
    , bvdSoftforkRule      :: !SoftForkRule
    , bvdTXFeePolicy       :: !TxFeePolicy
    , bvdUnlockStakeEpoch  :: !Integer
    } deriving (Eq, Show)

data SoftForkRule = SoftForkRule
    { sfrInitThd      :: !Float
    , sfrMinThd       :: !Float
    , sfrThdDecrement :: !Float
    } deriving (Eq, Show)

data TxFeePolicy = TxFeePolicy
    { txfTXSizeLinear :: !TxSizeLinear
    } deriving (Eq, Show)

data TxSizeLinear = TxSizeLinear
    { txsA :: !Int
    , txsB :: !Float
    } deriving (Eq, Show)

data ProtocolConstants = ProtocolConstants
    { prK             :: !Int
    -- ^ Security parameter from the paper.
    , prProtocolMagic :: !Int
    -- ^ Magic constant for separating real/testnet.
    } deriving (Eq, Show)

data NTP = NTP
    { ntpResponseTimeout :: !Int
    , ntpPollDelay       :: !Int
    , ntpServers         :: ![Text]
    } deriving (Eq, Show)

data Update = Update
    { upApplicationName       :: !Text
    , upApplicationVersion    :: !Int
    , upLastKnownBlockVersion :: !LastKnownBlockVersion
    } deriving (Eq, Show)

data LastKnownBlockVersion = LastKnownBlockVersion
    { lkbvMajor :: !Int
    , lkbvMinor :: !Int
    , lkbvAlt   :: !Int
    } deriving (Eq, Show)

data SSC = SSC
    { sscMPCSendInterval               :: !Word
      -- ^ Length of interval for sending MPC message
    , sscMdNoCommitmentsEpochThreshold :: !Int
      -- ^ Threshold of epochs for malicious activity detection
    , sscNoReportNoSecretsForEpoch1    :: !Bool
      -- ^ Don't print “SSC couldn't compute seed” for the first epoch.
    } deriving (Eq, Show)

data TXP = TXP
    { txpMemPoolLimitTx        :: !Int
      -- ^ Limit on the number of transactions that can be stored in the mem pool.
    , txpAssetLockedSrcAddress :: ![Text]
      -- ^ Set of source address which are asset-locked. Transactions which
      -- use these addresses as transaction inputs will be silently dropped.
    } deriving (Eq, Show)

data DLG = DLG
    { dlgCacheParam       :: !Int
      -- ^ This value parameterizes size of cache used in Delegation.
      -- Not bytes, but number of elements.
    , dlgMessageCacheTimeout :: !Int
      -- ^ Interval we ignore cached messages for if it's sent again.
    } deriving (Eq, Show)

data Block = Block
    { blNetworkDiameter        :: !Int
      -- ^Estimated time needed to broadcast message from one node to all other nodes
    , blRecoveryHeadersMessage :: !Int
      -- ^Maximum amount of headers node can put into headers message while in "after offline" or "recovery" mode.
    , blStreamWindow           :: !Int
      -- ^ Number of blocks to have inflight
    , blNonCriticalCQBootstrap :: !Double
      -- ^ If chain quality in bootstrap era is less than this value, non critical misbehavior will be reported.
    , blNonCriticalCQ          :: !Double
      -- ^ If chain quality after bootstrap era is less than this value, non critical misbehavior will be reported.
    , blCriticalCQ             :: !Double
      -- ^ If chain quality after bootstrap era is less than this value, critical misbehavior will be reported.
    , blCriticalCQBootstrap    :: !Double
      -- ^ If chain quality in bootstrap era is less than this value, critical misbehavior will be reported.
    , blCriticalForkThreshold  :: !Int
      -- ^ Number of blocks such that if so many blocks are rolled back, it requires immediate reaction.
    , blFixedTimeCQ            :: !Int
      -- ^ Chain quality will be also calculated for this amount of seconds.
    } deriving (Eq, Show)

--- | Top-level Cardano SL node configuration
data Node = Node
    { noNetworkConnectionTimeout     :: !Int
      -- ^ Network connection timeout in milliseconds
    , noConversationEstablishTimeout :: !Int
      -- ^ Conversation acknowledgement timeout in milliseconds.
    , noBlockRetrievalQueueSize      :: !Int
      -- ^ Block retrieval queue capacity
    , noPendingTxResubmissionPeriod  :: !Int
      -- ^ Minimal delay between pending transactions resubmission
    , noWalletProductionApi          :: !Bool
      -- ^ Whether hazard wallet endpoint should be disabled
    , noWalletTxCreationDisabled     :: !Bool
      -- ^ Disallow transaction creation or re-submission of
      -- pending transactions by the wallet
    , noExplorerExtendedApi          :: !Bool
      -- ^ Enable explorer extended API for fetching more
    } deriving (Eq, Show)

data TLS = TLS
    { tlsCA      :: !Certificate
    , tlsServer  :: !Certificate
    , tlsClients :: !Certificate
    } deriving (Eq, Show)

data Certificate = Certificate
    { certOrganization :: !Text
    , certCommonName   :: !Text
    , certExpiryDays   :: !Int
    , certAltDNS       :: ![Text]
    } deriving (Eq, Show)

-- | Contains wallet configuration variables.
data Wallet = Wallet
    { waThrottle :: !Throttle
    } deriving (Eq, Show)

-- | Rate-limiting/throttling parameters
data Throttle = SetThrottle
    { thEnabled :: !Bool
    , thRate    :: !Int
    , thPeriod  :: !Text
    , thBurst   :: !Int
    } deriving (Eq, Show)