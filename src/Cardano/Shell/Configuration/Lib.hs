{-# LANGUAGE RecordWildCards #-}

module Cardano.Shell.Configuration.Lib
    ( finaliseCardanoConfiguration
    , mkLauncher
    , mkTopology
    , mkOSConfig
    , mkInstallerConfig
    -- Configurations for features
    , mkBlockchainConfig
    , mkLoggingConfig
    , mkNetworkConfig
    , mkWalletConfig
    -- Tools
    , lastToEither
    ) where

import           Cardano.Prelude

import           Dhall (auto, input)

import           Cardano.Shell.Configuration.Types (BlockchainConfig,
                                                    Cluster (..),
                                                    InstallerConfig, Launcher,
                                                    Launcher, LoggingConfig,
                                                    NetworkConfig, OS (..),
                                                    OSConfig, TopologyConfig,
                                                    WalletConfig, renderCluster,
                                                    renderOS)
import           Cardano.Shell.Constants.PartialTypes (PartialBlock (..), PartialCardanoConfiguration (..),
                                                       PartialCertificate (..),
                                                       PartialCore (..),
                                                       PartialDLG (..),
                                                       PartialLastKnownBlockVersion (..),
                                                       PartialNTP (..),
                                                       PartialNode (..),
                                                       PartialSSC (..),
                                                       PartialTLS (..),
                                                       PartialTXP (..),
                                                       PartialUpdate (..),
                                                       PartialWallet (..))
import           Cardano.Shell.Constants.Types (Block (..),
                                                CardanoConfiguration (..),
                                                Certificate (..), Core (..),
                                                DLG (..),
                                                LastKnownBlockVersion (..),
                                                NTP (..), Node (..), SSC (..),
                                                TLS (..), TXP (..), Update (..),
                                                Wallet (..))

-- | Converting a @Last@ to an @Either@
lastToEither :: Text -> Last a -> Either Text a
lastToEither errMsg (Last x) = maybe (Left errMsg) Right x

--
-- The finalise* family of functions are supposed to be called at the very last stage
-- in the partial options monoid approach, after all the parametrisation layers have been merged,
-- and we're intending to use the resultant config -- they ensure that all values are defined.
--
-- NOTE: we should look into applying generic programming and/or TH for this boilerlate.
--
finaliseCardanoConfiguration :: PartialCardanoConfiguration -> Either Text CardanoConfiguration
finaliseCardanoConfiguration PartialCardanoConfiguration{..} = do

    ccLogPath                <- lastToEither "Unspecified ccLogPath"    pccLogPath
    ccLogConfig              <- lastToEither "Unspecified ccLogConfig"  pccLogConfig
    ccDBPath                 <- lastToEither "Unspecified ccDBPath"     pccDBPath

    ccApplicationLockFile    <- lastToEither "Unspecified ccApplicationLockFile"
                                    pccApplicationLockFile

    ccCore                   <- finaliseCore pccCore
    ccNTP                    <- finaliseNTP pccNTP
    ccUpdate                 <- finaliseUpdate pccUpdate
    ccTXP                    <- finaliseTXP pccTXP
    ccSSC                    <- finaliseSSC pccSSC
    ccDLG                    <- finaliseDLG pccDLG
    ccBlock                  <- finaliseBlock pccBlock

    ccNode                   <- finaliseNode pccNode

    ccTLS                    <- finaliseTLS pccTLS

    ccWallet                 <- finaliseWallet pccWallet

    pure CardanoConfiguration{..}
  where
    -- | Finalize the @PartialCore@, convert to @Core@.
    finaliseCore :: PartialCore -> Either Text Core
    finaliseCore PartialCore{..} = do

        coGenesisFile                   <- lastToEither "Unspecified coGenesisFile"
                                            pcoGenesisFile

        coGenesisHash                   <- lastToEither "Unspecified coGenesisHash"
                                            pcoGenesisHash

        coNodeId                        <- lastToEither "Unspecified coNodeId"
                                            pcoNodeId

        coNumCoreNodes                  <- lastToEither "Unspecified coNumCoreNodes"
                                            pcoNumCoreNodes

        coNodeProtocol                  <- lastToEither "Unspecified coNodeProtocol"
                                            pcoNodeProtocol

        let coStaticKeySigningKeyFile   = getLast pcoStaticKeySigningKeyFile
        let coStaticKeyDlgCertFile      = getLast pcoStaticKeyDlgCertFile

        coRequiresNetworkMagic          <- lastToEither "Unspecified coRequiresNetworkMagic"
                                            pcoRequiresNetworkMagic

        coDBSerializeVersion            <- lastToEither "Unspecified coDBSerializeVersion"
                                            pcoDBSerializeVersion

        let coPBftSigThd                = getLast pcoPBftSigThd

        pure Core{..}


    -- | Finalize the @PartialTXP@, convert to @TXP@.
    finaliseTXP :: PartialTXP -> Either Text TXP
    finaliseTXP PartialTXP{..} = do

        txpMemPoolLimitTx           <- lastToEither "Unspecified txpMemPoolLimitTx"
                                        ptxpMemPoolLimitTx

        txpAssetLockedSrcAddress    <- lastToEither "Unspecified txpAssetLockedSrcAddress"
                                        ptxpAssetLockedSrcAddress

        pure TXP{..}

    -- | Finalize the @PartialUpdate@, convert to @Update@.
    finaliseUpdate :: PartialUpdate -> Either Text Update
    finaliseUpdate PartialUpdate{..} = do

        upApplicationName          <- lastToEither "Unspecified upApplicationName"      pupApplicationName
        upApplicationVersion       <- lastToEither "Unspecified upApplicationVersion"   pupApplicationVersion
        upLastKnownBlockVersion    <- finaliseLastKnownBlockVersion pupLastKnownBlockVersion

        pure Update{..}
      where
        finaliseLastKnownBlockVersion :: PartialLastKnownBlockVersion -> Either Text LastKnownBlockVersion
        finaliseLastKnownBlockVersion PartialLastKnownBlockVersion{..} = do

            lkbvMajor  <- lastToEither "Unspecified lkbvMajor"     plkbvMajor
            lkbvMinor  <- lastToEither "Unspecified lkbvMinor"     plkbvMinor
            lkbvAlt    <- lastToEither "Unspecified lkbvAlt"       plkbvAlt

            pure LastKnownBlockVersion{..}


    -- | Finalize the @PartialNTP@, convert to @NTP@.
    finaliseSSC :: PartialSSC -> Either Text SSC
    finaliseSSC PartialSSC{..} = do

        sscMPCSendInterval                 <- lastToEither "Unspecified sscMPCSendInterval"
                                                psscMPCSendInterval

        sscMdNoCommitmentsEpochThreshold   <- lastToEither "Unspecified sscMdNoCommitmentsEpochThreshold"
                                                psscMdNoCommitmentsEpochThreshold

        sscNoReportNoSecretsForEpoch1      <- lastToEither "Unspecified sscNoReportNoSecretsForEpoch1"
                                                psscNoReportNoSecretsForEpoch1

        pure SSC{..}


    -- | Finalize the @PartialNTP@, convert to @NTP@.
    finaliseNTP :: PartialNTP -> Either Text NTP
    finaliseNTP PartialNTP{..} = do

        ntpResponseTimeout  <- lastToEither "Unspecified ntpResponseTimeout"    pntpResponseTimeout
        ntpPollDelay        <- lastToEither "Unspecified ntpPollDelay"          pntpPollDelay
        ntpServers          <- lastToEither "Unspecified ntpServers"            pntpServers

        pure NTP{..}

    -- | Finalize the @PartialNode@, convert to @Node@.
    finaliseNode :: PartialNode -> Either Text Node
    finaliseNode PartialNode{..} = do

        noSystemStartTime               <- lastToEither "Unspecified noSystemStartTime"
                                            pnoSystemStartTime

        noSlotLength                    <- lastToEither "Unspecified noSlotLength"
                                            pnoSlotLength

        noNetworkConnectionTimeout      <- lastToEither "Unspecified noNetworkConnectionTimeout"
                                            pnoNetworkConnectionTimeout

        noConversationEstablishTimeout  <- lastToEither "Unspecified noConversationEstablishTimeout"
                                            pnoConversationEstablishTimeout

        noBlockRetrievalQueueSize       <- lastToEither "Unspecified noBlockRetrievalQueueSize"
                                            pnoBlockRetrievalQueueSize

        noPendingTxResubmissionPeriod   <- lastToEither "Unspecified noPendingTxResubmissionPeriod"
                                            pnoPendingTxResubmissionPeriod

        noWalletProductionApi           <- lastToEither "Unspecified noWalletProductionApi"
                                            pnoWalletProductionApi

        noWalletTxCreationDisabled      <- lastToEither "Unspecified noWalletTxCreationDisabled"
                                            pnoWalletTxCreationDisabled

        noExplorerExtendedApi           <- lastToEither "Unspecified noExplorerExtendedApi"
                                            pnoExplorerExtendedApi

        pure Node{..}

    -- | Finalize the @PartialDLG@, convert to @DLG@.
    finaliseDLG :: PartialDLG -> Either Text DLG
    finaliseDLG PartialDLG{..} = do

        dlgCacheParam           <- lastToEither "Unspecified dlgCacheParam"             pdlgCacheParam
        dlgMessageCacheTimeout  <- lastToEither "Unspecified dlgMessageCacheTimeout"    pdlgMessageCacheTimeout

        pure DLG{..}


    -- | Finalize the @PartialBlock@, convert to @Block@.
    finaliseBlock :: PartialBlock -> Either Text Block
    finaliseBlock PartialBlock{..} = do

        blNetworkDiameter        <- lastToEither "Unspecified blNetworkDiameter"        pblNetworkDiameter
        blRecoveryHeadersMessage <- lastToEither "Unspecified blRecoveryHeadersMessage" pblRecoveryHeadersMessage
        blStreamWindow           <- lastToEither "Unspecified blStreamWindow"           pblStreamWindow
        blNonCriticalCQBootstrap <- lastToEither "Unspecified blNonCriticalCQBootstrap" pblNonCriticalCQBootstrap
        blNonCriticalCQ          <- lastToEither "Unspecified blNonCriticalCQ"          pblNonCriticalCQ
        blCriticalCQ             <- lastToEither "Unspecified blCriticalCQ"             pblCriticalCQ
        blCriticalCQBootstrap    <- lastToEither "Unspecified blCriticalCQBootstrap"    pblCriticalCQBootstrap
        blCriticalForkThreshold  <- lastToEither "Unspecified blCriticalForkThreshold"  pblCriticalForkThreshold
        blFixedTimeCQ            <- lastToEither "Unspecified blFixedTimeCQ"            pblFixedTimeCQ

        pure Block{..}

    -- | Finalize the @PartialCertificate@, convert to @Certificate@.
    finaliseCertificate :: PartialCertificate -> Either Text Certificate
    finaliseCertificate PartialCertificate{..} = do

        certOrganization    <- lastToEither "Unspecified certOrganization"  pcertOrganization
        certCommonName      <- lastToEither "Unspecified certCommonName"    pcertCommonName
        certExpiryDays      <- lastToEither "Unspecified certExpiryDays"    pcertExpiryDays
        certAltDNS          <- lastToEither "Unspecified certAltDNS"        pcertAltDNS

        pure Certificate{..}

    -- | Finalize the @PartialTLS@, convert to @TLS@.
    finaliseTLS :: PartialTLS -> Either Text TLS
    finaliseTLS PartialTLS{..} = do

        tlsCA       <- finaliseCertificate ptlsCA
        tlsServer   <- finaliseCertificate ptlsServer
        tlsClients  <- finaliseCertificate ptlsClients

        pure TLS{..}

    -- | Finalize the @PartialWallet@, convert to @Wallet@.
    finaliseWallet :: PartialWallet -> Either Text Wallet
    finaliseWallet PartialWallet{..} = do

        thEnabled   <- lastToEither "Unspecified thEnabled" pthEnabled
        thRate      <- lastToEither "Unspecified thRate"    pthRate
        thPeriod    <- lastToEither "Unspecified thPeriod"  pthPeriod
        thBurst     <- lastToEither "Unspecified thBurst"   pthBurst

        pure Wallet {..}

-- | Generate 'TopologyConfig' with given 'Cluster'
mkTopology :: Cluster -> IO TopologyConfig
mkTopology cluster = input auto topologyPath
  where
    topologyPath = toPath "topology" <> " " <> toPath (renderCluster cluster)

-- | Generate 'OSConfig' with given 'OS' and 'Cluster'
mkOSConfig :: OS -> Cluster -> IO OSConfig
mkOSConfig os cluster = input auto osConfigPath
  where
    osConfigPath = toPath (renderOS os) <> " " <> toPath (renderCluster cluster)

-- | Generate 'InstallerConfig' with given 'OS' and 'Cluster'
mkInstallerConfig :: OS -> Cluster -> IO InstallerConfig
mkInstallerConfig os cluster = input auto installerConfigPath
  where
    installerConfigPath = toPath "installer"
        <> " " <> toPath (renderCluster cluster)
        <> " (" <> toPath (renderOS os) <> " " <> toPath (renderCluster cluster) <> ")"

-- | Generate 'Launcher' config with given 'OS' and 'Cluster'
mkLauncher :: OS -> Cluster -> IO Launcher
mkLauncher os cluster = input auto launcherPath
  where
    launcherPath = toPath "launcher"
        <> " " <> toPath (renderCluster cluster)
        <> " " <> "(" <> toPath (renderOS os) <> " " <> toPath (renderCluster cluster) <> ")"

--------------------------------------------------------------------------------
-- Features
--------------------------------------------------------------------------------

mkBlockchainConfig :: OS -> Cluster -> IO BlockchainConfig
mkBlockchainConfig os cluster = input auto blockchainPath
  where
    blockchainPath = toFeaturePath "blockchain"
        <> "(" <> osPath os <> " " <> clusterPath cluster <> ")"

mkLoggingConfig :: OS -> Cluster -> IO LoggingConfig
mkLoggingConfig os cluster = input auto loggingPath
  where
    loggingPath = toFeaturePath "logging"
        <> "(" <> osPath os <> " " <> clusterPath cluster <> ")"
        <> "(" <> toPath "launcher" <> " " <> clusterPath cluster <> " " <>
        "(" <> osPath os <> " " <> clusterPath cluster <> ")" <>")"

mkNetworkConfig :: OS -> Cluster -> IO NetworkConfig
mkNetworkConfig os cluster = input auto networkPath
  where
    networkPath = toFeaturePath "network" <> " "
        <> toPath (renderCluster cluster)
        <> "(" <> osPath os <> " " <> clusterPath cluster <> ") "
        <> "(" <> toPath "launcher" <> " " <> clusterPath cluster <> " " <>
        "(" <> osPath os <> " " <> clusterPath cluster <> ")" <>")"

-- TODO(KS): This is a bit complicated.
mkWalletConfig :: OS -> Cluster -> IO WalletConfig
mkWalletConfig os cluster = input auto walletPath
  where
    walletPath = toFeaturePath "wallet" <> " "
        <> clusterPath cluster
        <> "(" <> osPath os <> " " <> clusterPath cluster <> ") "
        <> "(" <> toPath "launcher" <> " " <> clusterPath cluster <> " " <>
        "(" <> osPath os <> " " <> clusterPath cluster <> ")" <>") "
        <> "(" <> toPath "topology" <> " " <> clusterPath cluster <> ")"

--------------------------------------------------------------------------------
-- Helper function
--------------------------------------------------------------------------------

-- | Render given text into dhall file path
toFeaturePath :: Text -> Text
toFeaturePath fileName = "./dhall/features/" <> fileName <> ".dhall"

-- | Given an FileName, return 'FilePath' to dhall file
toPath :: Text -> Text
toPath fileName = "./dhall/" <> fileName <> ".dhall"

-- | Return given 'Cluster' dhall filepath
clusterPath :: Cluster -> Text
clusterPath cluster = toPath $ renderCluster cluster

-- | Return givne 'OS' dhall filepath
osPath :: OS -> Text
osPath os = toPath $ renderOS os
