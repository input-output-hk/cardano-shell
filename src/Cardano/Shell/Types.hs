{-# LANGUAGE Rank2Types #-}

module Cardano.Shell.Types where

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

-- | Cardano configuration
data CardanoConfiguration = CardanoConfiguration
    { ccLogPath                 :: !FilePath
    -- ^ The location of the log files on the filesystem.
    , ccLogConfig               :: !FilePath
    -- ^ The path to the log configuration.
    , ccDBPath                  :: !FilePath
    -- ^ The location of the DB on the filesystem.
    , ccApplicationLockFile     :: !FilePath
    -- ^ The location of the application lock file that is used
    -- as a semaphore se we can run just one application
    -- instance at a time.
    }

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

loadCardanoConfiguration :: IO CardanoConfiguration
loadCardanoConfiguration = do
    pure $ CardanoConfiguration mempty mempty mempty mempty

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
-- Cardano Mainnet Configuration
--------------------------------------------------------------------------------

mainnetConfiguration :: CardanoConfiguration
mainnetConfiguration = do

let mainnetGenesis = GenesisExternal { src  = "mainnet-genesis.json"
                                     , fileHash = "5f20df933584822601f9e3f8c024eb5eb252fe8cefb24d1317dc3d432e940ebb"
                                     }

let 
let mainnetCore = Core { genesis              = mainnetGenesis
                       , requiresNetworkMagic = Text
                       , dbSerializeVersion   = Integer
                       }

CardanoConfiguration   { scfgLogPath  = "./logs/"
                       , scfgDBPath   = "./db/"
                       , core         = mainnetCore
                       , ntp          = NTP
                       , update       = Update
                       , txp          = TXP
                       , ssc          = SSC
                       , dlg          = DLG
                       , block        = Block
                       , node         = Node
                       , tls          = TLS
                       , wallet       = Wallet
                       } deriving (Eq, Show)
--------------------------------------------------------------------------------
-- Cardano Configuration Data Structures
--------------------------------------------------------------------------------
-- | The basic configuration structure. It should contain all the required
-- configuration parameters for the modules to work.

data CardanoConfiguration = CardanoConfiguration
    { ccLogPath                 :: !FilePath
    -- ^ The location of the log files on the filesystem.
    , ccDBPath                  :: !FilePath
    -- ^ The location of the DB on the filesystem.
    , ccApplicationLockFile     :: !FilePath
    -- ^ The location of the application lock file that is used
    -- as a semaphore se we can run just one application
    -- instance at a time.
    , ccCore          :: !Core
    , ccNTP           :: !NTP
    , ccUpdate        :: !Update
    , ccTXP           :: !TXP
    , ccSSC           :: !SSC
    , ccDLG           :: !DLG
    , ccBlock         :: !Block
    , ccNode          :: !Node
    , ccTLS           :: !TLS
    , ccWallet        :: !Wallet
    } deriving (Eq, Show)

data Core = Core
    { genesis              :: !Genesis
    , requiresNetworkMagic :: !Text
      -- ^ Bool-isomorphic flag indicating whether we're on testnet
      -- or mainnet/staging.
    , dbSerializeVersion   :: !Integer
      -- ^ Versioning for values in node's DB
    } deriving (Eq, Show)

data Genesis = GenesisInternal { spec     :: !Spec }
             | GenesisExternal { src      :: !FilePath
                               , fileHash :: !Text 
                               }
             deriving (Eq, Show)

data Spec = Spec
    { initializer       :: !Initializer
      -- ^ Other data which depend on genesis type.
    , blockVersionData  :: !BlockVersionData
      -- ^ Genesis 'BlockVersionData'.
    , protocolConstants :: !ProtocolConstants
      -- ^ Other constants which affect consensus.
    , ftsSeed           :: !Text
      -- ^ Seed for FTS for 0-th epoch.
    , heavyDelegation   :: !Text
      -- ^ Genesis state of heavyweight delegation.
    , avvmDistr         :: !Text
      -- ^ Genesis data describes avvm utxo.
    } deriving (Eq, Show)

-- | This data type contains various options presense of which depends
-- on whether we want genesis for mainnet or testnet.
data Initializer = Initializer
    { testBalance       :: !TestBalance 
    , fakeAvvmBalance   :: !FakeAvvmBalance
    , avvmBalanceFactor :: !Int
    , useHeavyDlg       :: !Bool
    , seed              :: !Int
      -- ^ Seed to use to generate secret data. It's used only in
      -- testnet, shouldn't be used for anything important.
    } deriving (Eq, Show)

-- | These options determine balances of nodes specific for testnet.
data TestBalance = TestBalance
    { poors          :: !Int
      -- ^ Number of poor nodes (with small balance).
    , richmen        :: !Word
      -- ^ Number of rich nodes (with huge balance).
    , richmenShare   :: !Double
      -- ^ Portion of stake owned by all richmen together.
    , useHDAddresses :: !Bool
      -- ^ Whether generate plain addresses or with hd payload.
    , totalBalance   :: !Int
      -- ^ Total balance owned by these nodes.
    } deriving (Eq, Show)

-- | These options determines balances of fake AVVM nodes which didn't
-- really go through vending, but pretend they did.
data FakeAvvmBalance = FakeAvvmBalance
    { count      :: !Word
    , oneBalance :: !Word64
    } deriving (Eq, Show)

-- | If we require options to automatically restart a module.
data ModuleAutoRestart
    = ModuleRestart
    | ModuleNoRestart
    deriving (Eq, Show)

data BlockVersionData = BlockVersionData
    { scriptVersion     :: !Int
    , slotDuration      :: !Int
    , maxBlockSize      :: !Int
    , maxHeaderSize     :: !Int
    , maxTxSize         :: !Int
    , maxProposalSize   :: !Int
    , mpcThd            :: !Float
    , heavyDelThd       :: !Float
    , updateVoteThd     :: !Float
    , updateProposalThd :: !Float
    , updateImplicit    :: !Int
    , softforkRule      :: !SoftForkRule
    , txFeePolicy       :: !TxFeePolicy
    , unlockStakeEpoch  :: !Int
    } deriving (Eq, Show)

data SoftForkRule = SoftForkRule
    { initThd      :: !Float
    , minThd       :: !Float
    , thdDecrement :: !Float
    } deriving (Eq, Show)

data TxFeePolicy = TxFeePolicy
    { txSizeLinear :: !TxSizeLinear
    } deriving (Eq, Show)

data TxSizeLinear = TxSizeLinear
    { a :: !Int
    , b :: !Float
    } deriving (Eq, Show)

data ProtocolConstants = ProtocolConstants
    { k             :: !Int
    -- ^ Security parameter from the paper.
    , protocolMagic :: !Int
    -- ^ Magic constant for separating real/testnet.
    } deriving (Eq, Show)

data NTP = NTP
    { responseTimeout :: !Int
    , pollDelay       :: !Int
    , servers         :: ![Text]
    } deriving (Eq, Show)

data Update = Update
    { applicationName :: !Text
    , applicationVersion :: !Int
    , lastKnownBlockVersion :: !LastKnownBlockVersion
    } deriving (Eq, Show)

data LastKnownBlockVersion = LastKnownBlockVersion
    { bvMajor :: !Int
    , bvMinor :: !Int
    , bvAlt   :: !Int 
    } deriving (Eq, Show)

data SSC = SSC
    { mpcSendInterval :: !Word
      -- ^ Length of interval for sending MPC message
    , mdNoCommitmentsEpochThreshold :: !Int
      -- ^ Threshold of epochs for malicious activity detection
    , noReportNoSecretsForEpoch1 :: !Bool
      -- ^ Don't print “SSC couldn't compute seed” for the first epoch.
    } deriving (Eq, Show)

data TXP = TXP
    { memPoolLimitTx :: !Int
      -- ^ Limit on the number of transactions that can be stored in the mem pool.
    , assetLockedSrcAddress :: ![Text]
      -- ^ Set of source address which are asset-locked. Transactions which
      -- use these addresses as transaction inputs will be silently dropped.
    } deriving (Eq, Show)

data DLG = DLG
    { dlgCacheParam       :: !Int
      -- ^ This value parameterizes size of cache used in Delegation.
      -- Not bytes, but number of elements.
    , messageCacheTimeout :: !Int
      -- ^ Interval we ignore cached messages for if it's sent again.
    } deriving (Eq, Show)

data Block = Block
    { networkDiameter        :: !Int
      -- ^Estimated time needed to broadcast message from one node to all other nodes
    , recoveryHeadersMessage :: !Int
      -- ^Maximum amount of headers node can put into headers message while in "after offline" or "recovery" mode. 
    , streamWindow           :: !Int
      -- ^ Number of blocks to have inflight
    , nonCriticalCQBootstrap :: !Double
      -- ^ If chain quality in bootstrap era is less than this value, non critical misbehavior will be reported.
    , nonCriticalCQ          :: !Double
      -- ^ If chain quality after bootstrap era is less than this value, non critical misbehavior will be reported.
    , criticalCQ             :: !Double
      -- ^ If chain quality after bootstrap era is less than this value, critical misbehavior will be reported.
    , criticalForkThreshold  :: !Int
      -- ^ Number of blocks such that if so many blocks are rolled back, it requires immediate reaction.
    , fixedTimeCQ            :: !Second
      -- ^ Chain quality will be also calculated for this amount of seconds.
    } deriving (Eq, Show)

--- | Top-level Cardano SL node configuration
data Node = Node
    { networkConnectionTimeout     :: !Int
      -- ^ Network connection timeout in milliseconds
    , conversationEstablishTimeout :: !Int
      -- ^ Conversation acknowledgement timeout in milliseconds.
    , blockRetrievalQueueSize      :: !Int
      -- ^ Block retrieval queue capacity
    , pendingTxResubmissionPeriod  :: !Int
      -- ^ Minimal delay between pending transactions resubmission
    , walletProductionApi          :: !Bool
      -- ^ Whether hazard wallet endpoint should be disabled
    , walletTxCreationDisabled     :: !Bool
      -- ^ Disallow transaction creation or re-submission of
      -- pending transactions by the wallet
    , explorerExtendedApi          :: !Bool
      -- ^ Enable explorer extended API for fetching more
    } deriving (Eq, Show)

data TLS = TLS
    { ca      :: !Certificate
    , server  :: !Certificate
    , clients :: !Certificate
    } deriving (Eq, Show)

data Certificate = Certificate
    { organization :: !Text
    , commonName   :: !Text
    , expiryDays   :: !Int
    , altDNS       :: ![Text]
    } deriving (Eq, Show)

-- | Contains wallet configuration variables.
data Wallet = Wallet
    { throttle :: !Throttle
    } deriving (Eq, Show)

-- | Rate-limiting/throttling parameters
data Throttle = Throttle
    { enabled :: !Bool
    , rate    :: !Int
    , period  :: !Text
    , burst   :: !Int
    } deriving (Eq, Show)
