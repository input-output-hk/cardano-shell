{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia        #-}
{-# LANGUAGE DeriveGeneric      #-}

module Cardano.Shell.Constants.PartialTypes
    ( PartialCardanoConfiguration (..)
    , PartialCore (..)
    , PartialGenesis (..)
    , PartialStaticKeyMaterial (..)
    , PartialNode (..)
    , PartialBlock (..)
    , PartialTLS (..)
    , PartialCertificate (..)
    , PartialWallet (..)
    , PartialThrottle (..)
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
    , pccBlock               :: !(Last PartialBlock)
    , pccNode                :: !(Last PartialNode)
    , pccTLS                 :: !(Last PartialTLS)
    , pccWallet              :: !(Last PartialWallet)
    } deriving (Eq, Show, Generic)

-- | Partial @Core@ configuration.
data PartialCore = PartialCore
    { pcoGenesis              :: !(Last PartialGenesis)
    , pcoStaticKeyMaterial    :: !(Last PartialStaticKeyMaterial)
    , pcoRequiresNetworkMagic :: !(Last RequireNetworkMagic)
    , pcoDBSerializeVersion   :: !(Last Integer)
    } deriving (Eq, Show, Generic)
    deriving Semigroup via GenericSemigroup PartialCore
    deriving Monoid    via GenericMonoid PartialCore

-- | Partial @Genesis@.
data PartialGenesis = PartialGenesis
    { pgeSrc           :: !(Last FilePath)
    , pgeGenesisHash   :: !(Last Text)
    } deriving (Eq, Show, Generic)
    deriving Semigroup via GenericSemigroup PartialGenesis
    deriving Monoid    via GenericMonoid PartialGenesis

data PartialStaticKeyMaterial = PartialStaticKeyMaterial
    { pskmSigningKeyFile :: !(Last FilePath)
    , pskmDlgCertFile    :: !(Last FilePath)
    } deriving (Eq, Show, Generic)
    deriving Semigroup via GenericSemigroup PartialStaticKeyMaterial
    deriving Monoid    via GenericMonoid    PartialStaticKeyMaterial

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

-- | Partial @Block@ configuration.
data PartialBlock = PartialBlock
    { pblNetworkDiameter        :: !(Last Int)
      -- ^Estimated time needed to broadcast message from one node to all other nodes.
    , pblRecoveryHeadersMessage :: !(Last Int)
      -- ^Maximum amount of headers node can put into headers message while in "after offline" or "recovery" mode.
    , pblStreamWindow           :: !(Last Int)
      -- ^ Number of blocks to have inflight
    , pblNonCriticalCQBootstrap :: !(Last Double)
      -- ^ If chain quality in bootstrap era is less than this value, non critical misbehavior will be reported.
    , pblNonCriticalCQ          :: !(Last Double)
      -- ^ If chain quality after bootstrap era is less than this value, non critical misbehavior will be reported.
    , pblCriticalCQ             :: !(Last Double)
      -- ^ If chain quality after bootstrap era is less than this value, critical misbehavior will be reported.
    , pblCriticalCQBootstrap    :: !(Last Double)
      -- ^ If chain quality in bootstrap era is less than this value, critical misbehavior will be reported.
    , pblCriticalForkThreshold  :: !(Last Int)
      -- ^ Number of blocks such that if so many blocks are rolled back, it requires immediate reaction.
    , pblFixedTimeCQ            :: !(Last Int)
      -- ^ Chain quality will be also calculated for this amount of seconds.
    } deriving (Eq, Show, Generic)
    deriving Semigroup via GenericSemigroup PartialBlock
    deriving Monoid    via GenericMonoid PartialBlock

-- | Partial @TLS@ configuration.
data PartialTLS = PartialTLS
    { ptlsCA      :: !(Last PartialCertificate)
    -- ^ Certificate Authoritiy certificate.
    , ptlsServer  :: !(Last PartialCertificate)
    -- ^ Server certificate.
    , ptlsClients :: !(Last PartialCertificate)
    -- ^ Client certificate.
    } deriving (Eq, Show, Generic)
    deriving Semigroup via GenericSemigroup PartialTLS
    deriving Monoid    via GenericMonoid PartialTLS

-- | Partial @Certificate@ configuration.
data PartialCertificate = PartialCertificate
    { pcertOrganization :: !(Last Text)
    -- ^ Certificate organization.
    , pcertCommonName   :: !(Last Text)
    -- ^ Certificate common name.
    , pcertExpiryDays   :: !(Last Int)
    -- ^ Certificate days of expiration.
    , pcertAltDNS       :: !(Last [Text])
    -- ^ Certificate alternative DNS.
    } deriving (Eq, Show, Generic)
    deriving Semigroup via GenericSemigroup PartialCertificate
    deriving Monoid    via GenericMonoid PartialCertificate

-- | Partial @Wallet@ configuration.
data PartialWallet = PartialWallet
    { pwaThrottle :: !(Last PartialThrottle)
    -- ^ Wallet throttle configuration.
    } deriving (Eq, Show, Generic)
    deriving Semigroup via GenericSemigroup PartialWallet
    deriving Monoid    via GenericMonoid PartialWallet

-- | Partial @Throttle@ configuration.
data PartialThrottle = PartialThrottle
    { pthEnabled :: !(Last Bool)
    -- ^ Is throttle enabled?
    , pthRate    :: !(Last Int)
    -- ^ Throttle rate.
    , pthPeriod  :: !(Last Text)
    -- ^ Throttle period.
    , pthBurst   :: !(Last Int)
    -- ^ Throttle burst.
    } deriving (Eq, Show, Generic)
    deriving Semigroup via GenericSemigroup PartialThrottle
    deriving Monoid    via GenericMonoid PartialThrottle

