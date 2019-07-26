{-# LANGUAGE RecordWildCards #-}

module Cardano.Shell.Configuration.Lib
    ( finaliseCardanoConfiguration
    , finaliseCore
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
                                                       PartialNode (..),
                                                       PartialTLS (..),
                                                       PartialWallet (..))
import           Cardano.Shell.Constants.Types (Block (..),
                                                CardanoConfiguration (..),
                                                Certificate (..), Core (..),
                                                Node (..), TLS (..),
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
    ccLogPath                <- lastToEither "Unspecified ccLogPath"      pccLogPath
    ccLogConfig              <- lastToEither "Unspecified ccLogConfig"    pccLogConfig
    ccDBPath                 <- lastToEither "Unspecified ccDBPath"       pccDBPath
    ccApplicationLockFile    <- lastToEither "Unspecified ccApplicationLockFile"
                                    pccApplicationLockFile
    ccCore                   <- join $ finaliseCore <$>
                                    lastToEither "Unspecified ccCore"     pccCore
    ccNTP                    <- lastToEither "Unspecified ccNTP"          pccNTP
    ccUpdate                 <- lastToEither "Unspecified ccUpdate"       pccUpdate
    ccTXP                    <- lastToEither "Unspecified ccTXP"          pccTXP
    ccSSC                    <- lastToEither "Unspecified ccSSC"          pccSSC
    ccDLG                    <- lastToEither "Unspecified ccDLG"          pccDLG
    ccBlock                  <- join $ finaliseBlock <$>
                                    lastToEither "Unspecified ccBlock"    pccBlock
    ccNode                   <- join $ finaliseNode <$>
                                    lastToEither "Unspecified ccNode"     pccNode
    ccTLS                    <- join $ finaliseTLS <$>
                                    lastToEither "Unspecified ccTLS"      pccTLS
    ccWallet                 <- join $ finaliseWallet <$>
                                    lastToEither "Unspecified ccWallet"   pccWallet

    pure CardanoConfiguration{..}

-- | Finalize the @PartialCore@, convert to @Core@.
finaliseCore :: PartialCore -> Either Text Core
finaliseCore PartialCore{..} = do

    coGenesisFile               <- lastToEither "Unspecified coGenesisFile"             pcoGenesisFile
    coGenesisHash               <- lastToEither "Unspecified coGenesisHash"             pcoGenesisHash

    coStaticKeySigningKeyFile   <- lastToEither "Unspecified coStaticKeySigningKeyFile" pcoStaticKeySigningKeyFile
    coStaticKeyDlgCertFile      <- lastToEither "Unspecified coStaticKeyDlgCertFile"    pcoStaticKeyDlgCertFile

    coRequiresNetworkMagic      <- lastToEither "Unspecified coRequiresNetworkMagic"    pcoRequiresNetworkMagic
    coDBSerializeVersion        <- lastToEither "Unspecified coDBSerializeVersion"      pcoDBSerializeVersion

    pure Core{..}

-- | Finalize the @PartialNode@, convert to @Node@.
finaliseNode :: PartialNode -> Either Text Node
finaliseNode PartialNode{..} = do

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

    tlsCA       <- join $ finaliseCertificate <$> lastToEither "Unspecified tlsCS"         ptlsCA
    tlsServer   <- join $ finaliseCertificate <$> lastToEither "Unspecified tlsServer"     ptlsServer
    tlsClients  <- join $ finaliseCertificate <$> lastToEither "Unspecified tlsClients"    ptlsClients

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
