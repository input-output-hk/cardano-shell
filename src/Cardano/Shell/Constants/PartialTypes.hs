{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia        #-}
{-# LANGUAGE DeriveGeneric      #-}

module Cardano.Shell.Constants.PartialTypes
    ( PartialCardanoConfiguration (..)
    , PartialCore (..)
    , PartialNode (..)
    , PartialNTP (..)
    , PartialUpdate (..)
    , PartialLastKnownBlockVersion (..)
    , PartialSSC (..)
    , PartialTXP (..)
    , PartialDLG (..)
    , PartialBlock (..)
    , PartialTLS (..)
    , PartialCertificate (..)
    , PartialWallet (..)
    -- * re-exports
    , RequireNetworkMagic (..)
    ) where

import           Cardano.Prelude

import           Data.Monoid.Generic

import           Cardano.Shell.Constants.Types

-- | Partial @CardanoConfiguration@ configuration.
data PartialCardanoConfiguration = PartialCardanoConfiguration
    { pccLogPath             :: !(Last FilePath)
    , pccLogConfig           :: !(Last FilePath)
    , pccDBPath              :: !(Last FilePath)
    , pccApplicationLockFile :: !(Last FilePath)
    , pccCore                :: !PartialCore
    , pccNTP                 :: !PartialNTP
    , pccUpdate              :: !PartialUpdate
    , pccTXP                 :: !PartialTXP
    , pccSSC                 :: !PartialSSC
    , pccDLG                 :: !PartialDLG
    , pccBlock               :: !PartialBlock
    , pccNode                :: !PartialNode
    , pccTLS                 :: !PartialTLS
    , pccWallet              :: !PartialWallet
    } deriving (Eq, Show, Generic)
    deriving Semigroup via GenericSemigroup PartialCardanoConfiguration
    deriving Monoid    via GenericMonoid PartialCardanoConfiguration

-- | Partial @Core@ configuration.
data PartialCore = PartialCore
    { pcoGenesisFile                :: !(Last FilePath)
    , pcoGenesisHash                :: !(Last Text)
    , pcoStaticKeySigningKeyFile    :: !(Last (Maybe FilePath))
    , pcoStaticKeyDlgCertFile       :: !(Last (Maybe FilePath))
    , pcoRequiresNetworkMagic       :: !(Last RequireNetworkMagic)
    , pcoDBSerializeVersion         :: !(Last Integer)
    , pcoPBftSigThd                 :: !(Last (Maybe Double))
    } deriving (Eq, Show, Generic)
    deriving Semigroup via GenericSemigroup PartialCore
    deriving Monoid    via GenericMonoid PartialCore

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

-- | Partial @NTP@ configuration.
data PartialNTP = PartialNTP
    { pntpResponseTimeout :: !(Last Int)
    -- ^ NTP response timeout.
    , pntpPollDelay       :: !(Last Int)
    -- ^ NTP poll delay.
    , pntpServers         :: !(Last [Text])
    -- ^ A list of NTP servers.
    } deriving (Eq, Show, Generic)
    deriving Semigroup via GenericSemigroup PartialNTP
    deriving Monoid    via GenericMonoid PartialNTP

-- | Partial @TXP@ configuration.
data PartialTXP = PartialTXP
    { ptxpMemPoolLimitTx        :: !(Last Int)
    -- ^ Limit on the number of transactions that can be stored in the mem pool.
    , ptxpAssetLockedSrcAddress :: !(Last [Text])
    -- ^ Set of source address which are asset-locked. Transactions which
    -- use these addresses as transaction inputs will be silently dropped.
    } deriving (Eq, Show, Generic)
    deriving Semigroup via GenericSemigroup PartialTXP
    deriving Monoid    via GenericMonoid PartialTXP

-- | Partial @Update@ configuration.
data PartialUpdate = PartialUpdate
    { pupApplicationName       :: !(Last Text)
    -- ^ Update application name.
    , pupApplicationVersion    :: !(Last Int)
    -- ^ Update application version.
    , pupLastKnownBlockVersion :: !PartialLastKnownBlockVersion
    -- ^ Update last known block version.
    } deriving (Eq, Show, Generic)
    deriving Semigroup via GenericSemigroup PartialUpdate
    deriving Monoid    via GenericMonoid PartialUpdate

-- | Partial @LastKnownBlockVersion@ configuration.
data PartialLastKnownBlockVersion = PartialLastKnownBlockVersion
    { plkbvMajor :: !(Last Int)
    -- ^ Last known block version major.
    , plkbvMinor :: !(Last Int)
    -- ^ Last known block version minor.
    , plkbvAlt   :: !(Last Int)
    -- ^ Last known block version alternative.
    } deriving (Eq, Show, Generic)
    deriving Semigroup via GenericSemigroup PartialLastKnownBlockVersion
    deriving Monoid    via GenericMonoid PartialLastKnownBlockVersion

-- | Partial @SSC@ configuration.
data PartialSSC = PartialSSC
    { psscMPCSendInterval               :: !(Last Word)
      -- ^ Length of interval for sending MPC message
    , psscMdNoCommitmentsEpochThreshold :: !(Last Int)
      -- ^ Threshold of epochs for malicious activity detection
    , psscNoReportNoSecretsForEpoch1    :: !(Last Bool)
      -- ^ Don't print “SSC couldn't compute seed” for the first epoch.
    } deriving (Eq, Show, Generic)
    deriving Semigroup via GenericSemigroup PartialSSC
    deriving Monoid    via GenericMonoid PartialSSC

-- | Partial @DLG@ configuration.
data PartialDLG = PartialDLG
    { pdlgCacheParam          :: !(Last Int)
      -- ^ This value parameterizes size of cache used in Delegation.
      -- Not bytes, but number of elements.
    , pdlgMessageCacheTimeout :: !(Last Int)
      -- ^ Interval we ignore cached messages for if it's sent again.
    } deriving (Eq, Show, Generic)
    deriving Semigroup via GenericSemigroup PartialDLG
    deriving Monoid    via GenericMonoid PartialDLG

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
    { ptlsCA      :: !PartialCertificate
    -- ^ Certificate Authoritiy certificate.
    , ptlsServer  :: !PartialCertificate
    -- ^ Server certificate.
    , ptlsClients :: !PartialCertificate
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
    { pthEnabled :: !(Last Bool)
    -- ^ Is throttle enabled?
    , pthRate    :: !(Last Int)
    -- ^ Throttle rate.
    , pthPeriod  :: !(Last Text)
    -- ^ Throttle period.
    , pthBurst   :: !(Last Int)
    -- ^ Throttle burst.
    } deriving (Eq, Show, Generic)
    deriving Semigroup via GenericSemigroup PartialWallet
    deriving Monoid    via GenericMonoid PartialWallet

