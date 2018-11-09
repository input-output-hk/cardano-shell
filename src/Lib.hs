{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE TemplateHaskell   #-}
module Lib
    ( CardanoModule (..)
    , someFunc
    , runCardanoModule
    , runCardanoModuleWithDependency
    ) where

import           Cardano.Prelude

--import           Lens.Micro
--import           Lens.Micro.TH

someFunc :: IO ()
someFunc = putStrLn "something"

----------------------------------------------------------------------------
-- General architecture
----------------------------------------------------------------------------

-- | The basic configuration structure. It should contain all the required
-- configuration parameters for the modules to work.
-- This is _just an example_ and it's purpose it's just to show how it would work.


data Configuration = Configuration
    { core   :: !Text
    , ntp    :: !Text
    , update :: !Text
    , txp    :: !Text
    , dlg    :: !Text
    , block  :: !Text
    , node   :: !Text
    , tls    :: !Text
    , wallet :: !Text
    } deriving (Eq, Show)

data Core = Core
    { genesis              :: !Genesis
    , requiresNetworkMagic :: !Text
    , dbSerializeVersion   :: !Integer
    }

data Genesis = Genesis
    { spec :: !Spec
    }

data Spec = Spec
    { initializer       :: !Initializer
    , blockVersionData  :: !BlockVersionData
    , protocolConstants :: !ProtocolConstants
    , ftsSeed           :: !Text
    , heavyDelegation   :: !Text
    , avvmDistr         :: !Text
    }

data Initializer = Initializer
    { testBalance       :: !TestBalance
    , fakeAvvmBalance   :: !FakeAvvmBalance
    , avvmBalanceFactor :: !Int
    , useHeavyDlg       :: !Bool
    , seed              :: !Int
    }

data TestBalance = TestBalance
    { poors          :: !Int
    , richmen        :: !Int
    , richmenShare   :: !Float
    , useHDAddresses :: !Bool
    , totalBalance   :: !Int
    }

data FakeAvvmBalance = FakeAvvmBalance
    { count      :: !Int
    , oneBalance :: !Int
    }

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
    }

data SoftForkRule = SoftForkRule
    { initThd      :: !Float
    , minThd       :: !Float
    , thdDecrement :: !Float

    }

data TxFeePolicy = TxFeePolicy
    { txSizeLinear :: !TxSizeLinear
    }

data TxSizeLinear = TxSizeLinear
    { a :: !Int
    , b :: !Float
    }

data ProtocolConstants = ProtocolConstants
    { k             :: !Int
    , protocolMagic :: !Int
    }

data NTP = NTP
    { responseTimeout :: !Int
    , pollDelay       :: !Int
    , servers         :: ![Text]
    }

data Update = Update
    { dlgCacheParam       :: !Int
    , messageCacheTimeout :: !Int
    }

data Block = Block
    { networkDiameter        :: !Int
    , recoveryHEadersMessage :: !Int
    , streamWindow           :: !Int
    , nonCriticalCQBootstrap :: !Float
    , nonCriticalCQ          :: !Float
    , criticalCQ             :: !Float
    , criticalForkThreshold  :: !Int
    , fixedTimeCQ            :: !Int
    }

data Node = Node
    { networkConnectionTimeout     :: !Int
    , conversationEstablishTimeout :: !Int
    , blockRetrievalQueueSize      :: !Int
    , pendingTxREsubmissionPeriod  :: !Int
    , walletProductionApi          :: !Bool
    , walletTxCreationDisabled     :: !Bool
    , explorerExtendedApi          :: !Bool
    }

data TLS = TLS
    { ca      :: !Certificate
    , server  :: !Certificate
    , clients :: !Certificate
    }

data Certificate = Certificate
    { organization :: !Text
    , commonName   :: !Text
    , expiryDays   :: !Int
    , altDNS       :: ![Text]
    }

data Wallet = Wallet
    { throttle :: !Throttle
    }

data Throttle = Throttle
    { enabled :: !Bool
    , rate    :: !Int
    , period  :: !Text
    , burst   :: !Int
    }

-- waitCatch :: Async a -> IO (Either SomeException a)

-- | A general workflow for any cardano module.
data CardanoModule configuration result = CardanoModule
    { _parseConfiguration :: IO configuration
    -- ^ A parser for the configuration
    , _initialization     :: IO () -- TODO(ks): add as a type parameter
    -- ^ Initialization if required
    , _moduleRunner       :: Async configuration -> IO result
    -- ^ The actual runner for the module
    , _cleanup            :: IO () -- TODO(ks): remove
    -- ^ Cleanup if neccessary.
    }

-- https://mail.haskell.org/pipermail/haskell/2005-September/016502.html

-- This is an example of how a @CardanoModule@ could work.
runCardanoModule :: CardanoModule Configuration () -> IO ()
runCardanoModule cardanoModule = do

    -- we initialize the module if required
    _initialization cardanoModule

    -- then we run the module after parsing the configuration
    let parsedConfiguration     = _parseConfiguration cardanoModule
    let moduleRunner            = _moduleRunner cardanoModule

    result <- withAsync parsedConfiguration moduleRunner

    -- clean it up
    _       <- _cleanup cardanoModule

    -- return the result
    pure result

-- This is an example of how a @CardanoModule@ could work if it requires
-- a dependency.
-- dependencyModule ~ (LoggingCardanoModule, MonitoringCardanoModule, ...)
runCardanoModuleWithDependency :: dependencyModule -> CardanoModule configuration result -> IO result
runCardanoModuleWithDependency _ cardanoModule = do

    -- if the dependency is another cardano module
    --runCardanoModule logging
    --runCardanoModule monitoring

    -- we initialize the module if required
    _initialization cardanoModule

    -- then we run the module after parsing the configuration
    let parsedConfiguration     = _parseConfiguration cardanoModule
    let moduleRunner            = _moduleRunner cardanoModule

    result  <- withAsync parsedConfiguration moduleRunner

    -- clean it up
    _       <- _cleanup cardanoModule

    -- return the result
    pure result

{-

fix :: (a        -> a       ) -> a
fix :: ((b -> c) -> (b -> c)) -> (b -> c)
fix :: ((b -> c) ->  b -> c ) -> b -> c

mfix :: (a -> m a) -> m a
mfix :: (CardanoModule configuration result -> IO (CardanoModule configuration result)) -> IO (CardanoModule configuration result)

-}

-- | We can structure the construction of the module in phases.
data CardanoShellPhases
    = LoggingPhase
    | MonitoringPhase
    | NetworkPhase
    | BlockchainPhase
    | LedgerPhase
--  | ...
    deriving (Eq, Show)

----------------------------------------------------------------------------
-- Lenses derivation
----------------------------------------------------------------------------

--makeLenses 'Configuration
--makeLenses 'CardanoModule

