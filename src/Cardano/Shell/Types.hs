{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE Rank2Types        #-}

module Cardano.Shell.Types
    ( CardanoConfiguration (..)
    , CardanoEnvironment (..)
    , CardanoFeature (..)
    , CardanoFeatureInit (..)
    , NoDependency
    , ApplicationEnvironment (..)
    , CardanoApplication (..)
    , initializeCardanoEnvironment
    , loadCardanoConfiguration
    , applicationProductionMode
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

loadCardanoConfiguration :: IO CardanoConfiguration
loadCardanoConfiguration = do
    pure $ mainnetConfiguration

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
mainnetConfiguration = CardanoConfiguration
                       { ccLogPath  = "./logs/"
                       , ccLogConfig = "./log-config.yaml"
                       , ccDBPath   = "./db/"
                       , ccApplicationLockFile = ""
                       , ccCore       = Core { genesis =
                                          GenesisExternal { src      = "mainnet-genesis.json"
                                                          , fileHash = "5f20df933584822601f9e3f8c024eb5eb252fe8cefb24d1317dc3d432e940ebb"
                                                          }
                                             , requiresNetworkMagic = "NetworkMainOrStage"
                                             , dbSerializeVersion   = 0
                                             }
                       , ccNTP        = NTP { responseTimeout = 30000000
                                            , pollDelay       = 1800000000
                                            , servers         = [ "0.pool.ntp.org"
                                                                , "2.pool.ntp.org"
                                                                , "3.pool.ntp.org"
                                                                ]
                                            }
                       , ccUpdate     = Update { applicationName       = "cardano-sl"
                                               , applicationVersion    = 1
                                               , lastKnownBlockVersion =
                                                   LastKnownBlockVersion { bvMajor = 0
                                                                         , bvMinor = 2
                                                                         , bvAlt   = 0
                                                                         }
                                               }
                       , ccTXP        = TXP { memPoolLimitTx = 200
                                            , assetLockedSrcAddress = []
                                             }
                       , ccSSC        = SSC { mpcSendInterval               = 100
                                            , mdNoCommitmentsEpochThreshold = 3
                                            , noReportNoSecretsForEpoch1    = True
                                            }
                       , ccDLG        = DLG { dlgCacheParam       = 500
                                            , messageCacheTimeout = 30
                                            }
                       , ccBlock      = Block { networkDiameter        = 18
                                              , recoveryHeadersMessage = 2200
                                              , streamWindow           = 2048
                                              , nonCriticalCQBootstrap = 0.95
                                              , nonCriticalCQ          = 0.8
                                              , criticalCQBootstrap    = 0.8888
                                              , criticalCQ             = 0.654321
                                              , criticalForkThreshold  = 3
                                              , fixedTimeCQ            = 3600
                                              }
                       , ccNode       = Node { networkConnectionTimeout     = 15000
                                             , conversationEstablishTimeout = 30000
                                             , blockRetrievalQueueSize      = 100
                                             , pendingTxResubmissionPeriod  = 7
                                             , walletProductionApi          = True
                                             , walletTxCreationDisabled     = False
                                             , explorerExtendedApi          = False
                                             }
                       , ccTLS        = TLS { ca      = Certificate
                                                            { organization = "Input Output HK"
                                                            , commonName   = "Cardano SL Self-Signed Root CA"
                                                            , expiryDays   = 3600
                                                            , altDNS       = []
                                                            }
                                            , server  = Certificate
                                                            { organization = "Input Output HK"
                                                            , commonName   = "Cardano SL Server Node"
                                                            , expiryDays   = 3600
                                                            , altDNS       = [ "localhost"
                                                                             , "localhost.localdomain"
                                                                             , "127.0.0.1"
                                                                             , "::1" ]
                                                            }
                                            , clients = Certificate
                                                            { organization = "Input Output HK"
                                                            , commonName   = "Daedalus Wallet"
                                                            , expiryDays   = 3600
                                                            , altDNS       = []
                                                            }
                                            }
                       , ccWallet    = Wallet { throttle = NoThrottle }
                       }

--------------------------------------------------------------------------------
-- Cardano Dev Configuration
--------------------------------------------------------------------------------

devConfiguration :: CardanoConfiguration
devConfiguration = CardanoConfiguration
                       { ccLogPath  = "./logs/"
                       , ccDBPath   = "./db/"
                       , ccLogConfig = "./log-config.yaml"
                       , ccApplicationLockFile = ""
                       , ccCore     = Core { genesis  =
                                        GenesisInternal { spec =
                                          Spec { initializer =
                                            Initializer { testBalance =
                                              TestBalance { poors          = 12
                                                          , richmen        = 4
                                                          , richmenShare   = 0.99
                                                          , useHDAddresses = True
                                                          , totalBalance   = 600000000000000000
                                                          }
                                                        , fakeAvvmBalance  =
                                                            FakeAvvmBalance { count      = 10
                                                                            , oneBalance = 100000
                                                                            }
                                                        , avvmBalanceFactor = 1
                                                        , useHeavyDlg       = True
                                                        , seed              = 0
                                                        }

                                               , blockVersionData  =
                                                   BlockVersionData { scriptVersion = 0
                                                                    , slotDuration  = 7000
                                                                    , maxBlockSize  = 2000000
                                                                    , maxHeaderSize = 2000000
                                                                    , maxTxSize     = 4096
                                                                    , maxProposalSize = 700
                                                                    , mpcThd            = 0.01
                                                                    , heavyDelThd       = 0.005
                                                                    , updateVoteThd     = 0.001
                                                                    , updateProposalThd = 0.1
                                                                    , updateImplicit    = 10
                                                                    , softforkRule =
                                                                        SoftForkRule { initThd      = 0.9
                                                                                     , minThd       = 0.6
                                                                                     , thdDecrement = 0.05
                                                                                     }
                                                                    , txFeePolicy =
                                                                        TxFeePolicy { txSizeLinear =
                                                                          TxSizeLinear { a = 155381
                                                                                       , b = 43.946
                                                                                       }
                                                                                    }
                                                                    , unlockStakeEpoch = 18446744073709551615
                                                                    }

                                               , protocolConstants =
                                                   ProtocolConstants { k             = 2
                                                                     , protocolMagic = 55550001
                                                                     }
                                               , ftsSeed           = "c2tvdm9yb2RhIEdndXJkYSBib3JvZGEgcHJvdm9kYSA="
                                               , heavyDelegation   = ""
                                               , avvmDistr         = ""
                                               }
                                                        }
                                          , requiresNetworkMagic = "RequiresNoMagic"
                                          , dbSerializeVersion   = 0
                                          }
                       , ccNTP        = NTP { responseTimeout = 30000000
                                            , pollDelay       = 1800000000
                                            , servers         = [ "0.pool.ntp.org"
                                                                , "2.pool.ntp.org"
                                                                , "3.pool.ntp.org"
                                                                ]
                                            }
                       , ccUpdate     = Update { applicationName       = "cardano-sl"
                                               , applicationVersion    = 0
                                               , lastKnownBlockVersion =
                                                   LastKnownBlockVersion { bvMajor = 0
                                                                         , bvMinor = 0
                                                                         , bvAlt   = 0
                                                                         }
                                               }
                       , ccTXP        = TXP { memPoolLimitTx = 200
                                            , assetLockedSrcAddress = []
                                            }
                       , ccSSC        = SSC { mpcSendInterval               = 10
                                            , mdNoCommitmentsEpochThreshold = 3
                                            , noReportNoSecretsForEpoch1    = False
                                            }
                       , ccDLG        = DLG { dlgCacheParam       = 500
                                            , messageCacheTimeout = 30
                                            }
                       , ccBlock      = Block { networkDiameter        = 3
                                              , recoveryHeadersMessage = 20
                                              , streamWindow           = 2048
                                              , nonCriticalCQBootstrap = 0.95
                                              , nonCriticalCQ          = 0.8
                                              , criticalCQBootstrap    = 0.8888
                                              , criticalCQ             = 0.654321
                                              , criticalForkThreshold  = 2
                                              , fixedTimeCQ            = 10
                                              }
                       , ccNode       = Node { networkConnectionTimeout     = 15000
                                             , conversationEstablishTimeout = 30000
                                             , blockRetrievalQueueSize      = 100
                                             , pendingTxResubmissionPeriod  = 7
                                             , walletProductionApi          = False
                                             , walletTxCreationDisabled     = False
                                             , explorerExtendedApi          = False
                                             }
                       , ccTLS        = TLS { ca      = Certificate
                                                            { organization = "Input Output HK"
                                                            , commonName   = "Cardano SL Self-Signed Root CA"
                                                            , expiryDays   = 3650
                                                            , altDNS       = []
                                                            }
                                            , server  = Certificate
                                                            { organization = "Input Output HK"
                                                            , commonName   = "Cardano SL Server Node"
                                                            , expiryDays   = 365
                                                            , altDNS       = [ "localhost"
                                                                             , "localhost.localdomain"
                                                                             , "127.0.0.1"
                                                                             , "::1" ]
                                                            }
                                            , clients = Certificate
                                                            { organization = "Input Output HK"
                                                            , commonName   = "Daedalus Wallet"
                                                            , expiryDays   = 365
                                                            , altDNS       = []
                                                            }
                                            }
                       , ccWallet     =
                           Wallet { throttle = NoThrottle }
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
    , unlockStakeEpoch  :: !Integer
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
    { applicationName       :: !Text
    , applicationVersion    :: !Int
    , lastKnownBlockVersion :: !LastKnownBlockVersion
    } deriving (Eq, Show)

data LastKnownBlockVersion = LastKnownBlockVersion
    { bvMajor :: !Int
    , bvMinor :: !Int
    , bvAlt   :: !Int
    } deriving (Eq, Show)

data SSC = SSC
    { mpcSendInterval               :: !Word
      -- ^ Length of interval for sending MPC message
    , mdNoCommitmentsEpochThreshold :: !Int
      -- ^ Threshold of epochs for malicious activity detection
    , noReportNoSecretsForEpoch1    :: !Bool
      -- ^ Don't print “SSC couldn't compute seed” for the first epoch.
    } deriving (Eq, Show)

data TXP = TXP
    { memPoolLimitTx        :: !Int
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
    , criticalCQBootstrap    :: !Double
      -- ^ If chain quality in bootstrap era is less than this value, critical misbehavior will be reported.
    , criticalForkThreshold  :: !Int
      -- ^ Number of blocks such that if so many blocks are rolled back, it requires immediate reaction.
    , fixedTimeCQ            :: !Int
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
data Throttle = NoThrottle | Throttle
    { enabled :: !Bool
    , rate    :: !Int
    , period  :: !Text
    , burst   :: !Int
    } deriving (Eq, Show)
