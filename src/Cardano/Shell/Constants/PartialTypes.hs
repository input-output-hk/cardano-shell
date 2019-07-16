{-# LANGUAGE DeriveGeneric #-}

module Cardano.Shell.Constants.PartialTypes
    ( PartialCardanoConfiguration (..)
    , PartialCore (..)
    , PartialGenesis (..)
    , PartialNode (..)
    -- * re-exports
    , RequireNetworkMagic (..)
    ) where

import           Data.Function (on)

import           Cardano.Prelude

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
    } deriving (Eq, Show)

-- | Partial @Core@ configuration.
data PartialCore = PartialCore
    { pcoGenesis              :: !(Last PartialGenesis)
    , pcoRequiresNetworkMagic :: !(Last RequireNetworkMagic)
    , pcoDBSerializeVersion   :: !(Last Integer)
    } deriving (Eq, Show, Generic)

instance Semigroup PartialCore where
    x <> y =
        PartialCore
            { pcoGenesis                 = on (<>) pcoGenesis              x y
            , pcoRequiresNetworkMagic    = on (<>) pcoRequiresNetworkMagic x y
            , pcoDBSerializeVersion      = on (<>) pcoDBSerializeVersion   x y
            }

instance Monoid PartialCore where
    mempty =
        PartialCore
            { pcoGenesis                 = mempty
            , pcoRequiresNetworkMagic    = mempty
            , pcoDBSerializeVersion      = mempty
            }

-- | Partial @Genesis@.
data PartialGenesis = PartialGenesis
    { pgeSrc           :: !(Last FilePath)
    , pgeGenesisHash   :: !(Last Text)
    , pgePrevBlockHash :: !(Last Text)
    } deriving (Eq, Show, Generic)

instance Semigroup PartialGenesis where
    x <> y =
        PartialGenesis
            { pgeSrc             = on (<>) pgeSrc           x y
            , pgeGenesisHash     = on (<>) pgeGenesisHash   x y
            , pgePrevBlockHash   = on (<>) pgePrevBlockHash x y
            }

instance Monoid PartialGenesis where
    mempty =
        PartialGenesis
            { pgeSrc             = mempty
            , pgeGenesisHash     = mempty
            , pgePrevBlockHash   = mempty
            }

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
    } deriving (Eq, Show)

instance Semigroup PartialNode where
    x <> y =
        PartialNode
            { pnoNetworkConnectionTimeout     = on (<>) pnoNetworkConnectionTimeout     x y
            , pnoConversationEstablishTimeout = on (<>) pnoConversationEstablishTimeout x y
            , pnoBlockRetrievalQueueSize      = on (<>) pnoBlockRetrievalQueueSize      x y
            , pnoPendingTxResubmissionPeriod  = on (<>) pnoPendingTxResubmissionPeriod  x y
            , pnoWalletProductionApi          = on (<>) pnoWalletProductionApi          x y
            , pnoWalletTxCreationDisabled     = on (<>) pnoWalletTxCreationDisabled     x y
            , pnoExplorerExtendedApi          = on (<>) pnoExplorerExtendedApi          x y
            }

instance Monoid PartialNode where
    mempty =
        PartialNode
            { pnoNetworkConnectionTimeout     = mempty
            , pnoConversationEstablishTimeout = mempty
            , pnoBlockRetrievalQueueSize      = mempty
            , pnoPendingTxResubmissionPeriod  = mempty
            , pnoWalletProductionApi          = mempty
            , pnoWalletTxCreationDisabled     = mempty
            , pnoExplorerExtendedApi          = mempty
            }
