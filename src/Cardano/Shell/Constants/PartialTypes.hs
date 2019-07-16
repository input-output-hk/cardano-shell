{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia        #-}
{-# LANGUAGE DeriveGeneric      #-}

module Cardano.Shell.Constants.PartialTypes
    ( PartialCardanoConfiguration (..)
    , PartialCore (..)
    , PartialGenesis (..)
    , PartialNode (..)
    -- * re-exports
    , RequireNetworkMagic (..)
    ) where

import           Cardano.Prelude

import           Data.Monoid.Generic

import           Cardano.Shell.Constants.Types

-- | The partial cardano configuration.
data PartialCardanoConfiguration = PartialCardanoConfiguration
    { pccLogPath             :: !(Last FilePath)
    , pccLogConfig           :: !(Last FilePath)
    , pccDBPath              :: !(Last FilePath)
    , pccApplicationLockFile :: !(Last FilePath)
    , pccCore                :: !(Last PartialCore)
    , pccNTP                 :: !(Last NTP)
    , pccUpdate              :: !(Last Update)
    , pccTXP                 :: !(Last TXP)
    , pccSSC                 :: !(Last SSC)
    , pccDLG                 :: !(Last DLG)
    , pccBlock               :: !(Last Block)
    , pccNode                :: !(Last PartialNode)
    , pccTLS                 :: !(Last TLS)
    , pccWallet              :: !(Last Wallet)
    } deriving (Eq, Show, Generic)

-- | Partial @Core@ configuration.
data PartialCore = PartialCore
    { pcoGenesis              :: !(Last PartialGenesis)
    , pcoRequiresNetworkMagic :: !(Last RequireNetworkMagic)
    , pcoDBSerializeVersion   :: !(Last Integer)
    } deriving (Eq, Show, Generic)
    deriving Semigroup via GenericSemigroup PartialCore
    deriving Monoid    via GenericMonoid PartialCore

-- | Partial @Genesis@.
data PartialGenesis = PartialGenesis
    { pgeSrc           :: !(Last FilePath)
    , pgeGenesisHash   :: !(Last Text)
    , pgePrevBlockHash :: !(Last Text)
    } deriving (Eq, Show, Generic)
    deriving Semigroup via GenericSemigroup PartialGenesis
    deriving Monoid    via GenericMonoid PartialGenesis

--- | Top-level Cardano SL node configuration
data PartialNode = PartialNode
    { pnoNetworkConnectionTimeout     :: !(Last Int)
      -- ^ Network connection timeout in milliseconds.
    , pnoConversationEstablishTimeout :: !(Last Int)
      -- ^ Conversation acknowledgement timeout in milliseconds.
    , pnoBlockRetrievalQueueSize      :: !(Last Int)
      -- ^ Block retrieval queue capacity.
    , pnoPendingTxResubmissionPeriod  :: !(Last Int)
      -- ^ Minimal delay between pending transactions resubmission.
    , pnoWalletProductionApi          :: !(Last Bool)
      -- ^ Whether hazard wallet endpoint should be disabled.
    , pnoWalletTxCreationDisabled     :: !(Last Bool)
      -- ^ Disallow transaction creation or re-submission of
      -- pending transactions by the wallet.
    , pnoExplorerExtendedApi          :: !(Last Bool)
      -- ^ Enable explorer extended API for fetching more.
    } deriving (Eq, Show, Generic)
    deriving Semigroup via GenericSemigroup PartialNode
    deriving Monoid    via GenericMonoid PartialNode

