module Cardano.Shell.Presets
    ( mainnetConfiguration
    , devConfiguration
    ) where

import           Cardano.Prelude

import           Cardano.Shell.Constants.PartialTypes (PartialCardanoConfiguration (..),
                                                       PartialCore (..),
                                                       PartialGenesis (..),
                                                       PartialNode (..))
import           Cardano.Shell.Constants.Types (Block (..), Certificate (..),
                                                DLG (..),
                                                LastKnownBlockVersion (..),
                                                NTP (..),
                                                RequireNetworkMagic (..),
                                                SSC (..), TLS (..), TXP (..),
                                                Throttle (..), Update (..),
                                                Wallet (..))

--------------------------------------------------------------------------------
-- Cardano Mainnet Configuration
--------------------------------------------------------------------------------

mainnetConfiguration :: PartialCardanoConfiguration
mainnetConfiguration =
  PartialCardanoConfiguration
    { pccLogPath             = pure "./logs/"
    , pccLogConfig           = pure "./configuration/log-configuration.yaml"
    , pccDBPath              = pure "./db/"
    , pccApplicationLockFile = pure ""
    , pccCore =
        pure PartialCore
          { pcoGenesis =
              pure PartialGenesis
                { pgeSrc             = pure "mainnet-genesis.json"
                , pgeGenesisHash     = pure "89d9b5a5b8ddc8d7e5a6795e9774d97faf1efea59b2caf7eaf9f8c5b32059df4"
                , pgePrevBlockHash   = pure "5f20df933584822601f9e3f8c024eb5eb252fe8cefb24d1317dc3d432e940ebb"
                }
          , pcoRequiresNetworkMagic = pure RequireNetworkMagic
          , pcoDBSerializeVersion   = mempty
          }
    , pccNTP = pure
        NTP
          { ntpResponseTimeout = 30000000
          , ntpPollDelay       = 1800000000
          , ntpServers         =
              [ "0.pool.ntp.org"
              , "2.pool.ntp.org"
              , "3.pool.ntp.org"
              ]
          }
    , pccUpdate = pure
        Update
          { upApplicationName       = "cardano-sl"
          , upApplicationVersion    = 1
          , upLastKnownBlockVersion =
              LastKnownBlockVersion
                { lkbvMajor = 0
                , lkbvMinor = 2
                , lkbvAlt   = 0
                }
                                               }
    , pccTXP = pure
        TXP
          { txpMemPoolLimitTx = 200
          , txpAssetLockedSrcAddress = []
          }
    , pccSSC = pure
        SSC
          { sscMPCSendInterval               = 100
          , sscMdNoCommitmentsEpochThreshold = 3
          , sscNoReportNoSecretsForEpoch1    = True
          }
    , pccDLG = pure
        DLG { dlgCacheParam          = 500
            , dlgMessageCacheTimeout = 30
            }
    , pccBlock = pure
        Block
          { blNetworkDiameter        = 18
          , blRecoveryHeadersMessage = 2200
          , blStreamWindow           = 2048
          , blNonCriticalCQBootstrap = 0.95
          , blNonCriticalCQ          = 0.8
          , blCriticalCQBootstrap    = 0.8888
          , blCriticalCQ             = 0.654321
          , blCriticalForkThreshold  = 3
          , blFixedTimeCQ            = 3600
          }
    , pccNode = pure
        PartialNode
          { pnoNetworkConnectionTimeout     = pure 15000
          , pnoConversationEstablishTimeout = pure 30000
          , pnoBlockRetrievalQueueSize      = pure 100
          , pnoPendingTxResubmissionPeriod  = pure 7
          , pnoWalletProductionApi          = pure True
          , pnoWalletTxCreationDisabled     = pure False
          , pnoExplorerExtendedApi          = pure False
          }
    , pccTLS = pure
        TLS
          { tlsCA =
              Certificate
                { certOrganization = "Input Output HK"
                , certCommonName   = "Cardano SL Self-Signed Root CA"
                , certExpiryDays   = 3600
                , certAltDNS       = []
                }
          , tlsServer =
              Certificate
                { certOrganization = "Input Output HK"
                , certCommonName   = "Cardano SL Server Node"
                , certExpiryDays   = 3600
                , certAltDNS       =
                    [ "localhost"
                    , "localhost.localdomain"
                    , "127.0.0.1"
                    , "::1" ]
                }
          , tlsClients =
              Certificate
                { certOrganization = "Input Output HK"
                , certCommonName   = "Daedalus Wallet"
                , certExpiryDays   = 3600
                , certAltDNS       = []
                }
                                            }
    , pccWallet = pure
        Wallet
          { waThrottle =
              SetThrottle
                { thEnabled = False
                , thRate    = 0
                , thPeriod  = ""
                , thBurst   = 0
                }
          }
    }

--------------------------------------------------------------------------------
-- Cardano Dev Configuration
--------------------------------------------------------------------------------

devConfiguration :: PartialCardanoConfiguration
devConfiguration =
  PartialCardanoConfiguration
    { pccLogPath             = pure "./logs/"
    , pccDBPath              = pure "./db/"
    , pccLogConfig           = pure "./log-config.yaml"
    , pccApplicationLockFile = pure ""
    , pccCore                = pure
      PartialCore
        { pcoGenesis  =
          pure PartialGenesis
            { pgeSrc             = pure "testnet-genesis.json"
            , pgeGenesisHash     = pure "7f141ea26e189c9cb09e2473f6499561011d5d3c90dd642fde859ce02282a3ae"
            , pgePrevBlockHash   = pure "b7f76950bc4866423538ab7764fc1c7020b24a5f717a5bee3109ff2796567214"
            }
        , pcoRequiresNetworkMagic = pure RequireNetworkMagic
        , pcoDBSerializeVersion   = mempty
        }
    , pccNTP                 = pure
         NTP
          { ntpResponseTimeout = 30000000
          , ntpPollDelay       = 1800000000
          , ntpServers         =
            [ "0.pool.ntp.org"
            , "2.pool.ntp.org"
            , "3.pool.ntp.org"
            ]
          }
    , pccUpdate              = pure
        Update
          { upApplicationName       = "cardano-sl"
          , upApplicationVersion    = 0
          , upLastKnownBlockVersion =
            LastKnownBlockVersion
              { lkbvMajor = 0
              , lkbvMinor = 0
              , lkbvAlt   = 0
              }
                                               }
    , pccTXP                 = pure
        TXP
          { txpMemPoolLimitTx = 200
          , txpAssetLockedSrcAddress = []
          }
    , pccSSC                 = pure
        SSC
          { sscMPCSendInterval = 10
          , sscMdNoCommitmentsEpochThreshold = 3
          , sscNoReportNoSecretsForEpoch1    = False
          }
    , pccDLG                 = pure
        DLG
          { dlgCacheParam          = 500
          , dlgMessageCacheTimeout = 30
          }
    , pccBlock               = pure
        Block
          { blNetworkDiameter        = 3
          , blRecoveryHeadersMessage = 20
          , blStreamWindow           = 2048
          , blNonCriticalCQBootstrap = 0.95
          , blNonCriticalCQ          = 0.8
          , blCriticalCQBootstrap    = 0.8888
          , blCriticalCQ             = 0.654321
          , blCriticalForkThreshold  = 2
          , blFixedTimeCQ            = 10
          }
    , pccNode                = pure
        PartialNode
          { pnoNetworkConnectionTimeout     = pure 15000
          , pnoConversationEstablishTimeout = pure 30000
          , pnoBlockRetrievalQueueSize      = pure 100
          , pnoPendingTxResubmissionPeriod  = pure 7
          , pnoWalletProductionApi          = pure False
          , pnoWalletTxCreationDisabled     = pure False
          , pnoExplorerExtendedApi          = pure False
          }
    , pccTLS                 = pure
        TLS
          { tlsCA =
              Certificate
                { certOrganization = "Input Output HK"
                , certCommonName   = "Cardano SL Self-Signed Root CA"
                , certExpiryDays   = 3650
                , certAltDNS       = []
                }
          , tlsServer =
              Certificate
                { certOrganization = "Input Output HK"
                , certCommonName   = "Cardano SL Server Node"
                , certExpiryDays   = 365
                , certAltDNS       =
                    [ "localhost"
                    , "localhost.localdomain"
                    , "127.0.0.1"
                    , "::1"
                    ]
                }
          , tlsClients =
              Certificate
                { certOrganization = "Input Output HK"
                , certCommonName   = "Daedalus Wallet"
                , certExpiryDays   = 365
                , certAltDNS       = []
                }
          }
    , pccWallet              = pure
        Wallet
          { waThrottle =  SetThrottle
            { thEnabled = False
            , thRate    = 0
            , thPeriod  = ""
            , thBurst   = 0
            }
          }
    }
