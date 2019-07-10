module Cardano.Shell.Presets
    ( mainnetConfiguration
    , devConfiguration
    ) where

import           Cardano.Prelude

import           Cardano.Shell.Constants.Types (Block (..),
                                                CardanoConfiguration (..),
                                                Certificate (..), Core (..),
                                                DLG (..), Genesis (..),
                                                LastKnownBlockVersion (..),
                                                NTP (..), Node (..),
                                                RequireNetworkMagic (..),
                                                SSC (..), TLS (..), TXP (..),
                                                Throttle (..), Update (..),
                                                Wallet (..))

--------------------------------------------------------------------------------
-- Cardano Mainnet Configuration
--------------------------------------------------------------------------------

mainnetConfiguration :: CardanoConfiguration
mainnetConfiguration =
  CardanoConfiguration
    { ccLogPath             = "./logs/"
    , ccLogConfig           = "./configuration/log-configuration.yaml"
    , ccDBPath              = "./db/"
    , ccApplicationLockFile = ""
    , ccCore =
        pure Core
          { coGenesis =
              pure Genesis
                { geSrc             = "mainnet-genesis.json"
                , geGenesisHash     = "89d9b5a5b8ddc8d7e5a6795e9774d97faf1efea59b2caf7eaf9f8c5b32059df4"
                , gePrevBlockHash   = "5f20df933584822601f9e3f8c024eb5eb252fe8cefb24d1317dc3d432e940ebb"
                }
          , coRequiresNetworkMagic = Last $ Just RequireNetworkMagic
          , coDBSerializeVersion   = Last Nothing
          }
    , ccNTP =
        NTP
          { ntpResponseTimeout = 30000000
          , ntpPollDelay       = 1800000000
          , ntpServers         =
              [ "0.pool.ntp.org"
              , "2.pool.ntp.org"
              , "3.pool.ntp.org"
              ]
          }
    , ccUpdate =
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
    , ccTXP =
        TXP
          { txpMemPoolLimitTx = 200
          , txpAssetLockedSrcAddress = []
          }
    , ccSSC =
        SSC
          { sscMPCSendInterval               = 100
          , sscMdNoCommitmentsEpochThreshold = 3
          , sscNoReportNoSecretsForEpoch1    = True
          }
    , ccDLG =
        DLG { dlgCacheParam          = 500
            , dlgMessageCacheTimeout = 30
            }
    , ccBlock =
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
    , ccNode =
        Node
          { noNetworkConnectionTimeout     = 15000
          , noConversationEstablishTimeout = 30000
          , noBlockRetrievalQueueSize      = 100
          , noPendingTxResubmissionPeriod  = 7
          , noWalletProductionApi          = True
          , noWalletTxCreationDisabled     = False
          , noExplorerExtendedApi          = False
          }
    , ccTLS =
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
    , ccWallet =
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

devConfiguration :: CardanoConfiguration
devConfiguration =
  CardanoConfiguration
    { ccLogPath             = "./logs/"
    , ccDBPath              = "./db/"
    , ccLogConfig           = "./log-config.yaml"
    , ccApplicationLockFile = ""
    , ccCore     =
      pure Core
        { coGenesis  =
          pure Genesis
            { geSrc             = "testnet-genesis.json"
            , geGenesisHash     = "7f141ea26e189c9cb09e2473f6499561011d5d3c90dd642fde859ce02282a3ae"
            , gePrevBlockHash   = "b7f76950bc4866423538ab7764fc1c7020b24a5f717a5bee3109ff2796567214"
            }
        , coRequiresNetworkMagic = Last $ Just RequireNetworkMagic
        , coDBSerializeVersion   = Last Nothing
        }
    , ccNTP =
        NTP
          { ntpResponseTimeout = 30000000
          , ntpPollDelay       = 1800000000
          , ntpServers         =
            [ "0.pool.ntp.org"
            , "2.pool.ntp.org"
            , "3.pool.ntp.org"
            ]
          }
    , ccUpdate =
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
    , ccTXP =
        TXP
          { txpMemPoolLimitTx = 200
          , txpAssetLockedSrcAddress = []
          }
    , ccSSC =
        SSC
          { sscMPCSendInterval = 10
          , sscMdNoCommitmentsEpochThreshold = 3
          , sscNoReportNoSecretsForEpoch1    = False
          }
    , ccDLG =
        DLG
          { dlgCacheParam          = 500
          , dlgMessageCacheTimeout = 30
          }
    , ccBlock =
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
    , ccNode =
        Node
          { noNetworkConnectionTimeout     = 15000
          , noConversationEstablishTimeout = 30000
          , noBlockRetrievalQueueSize      = 100
          , noPendingTxResubmissionPeriod  = 7
          , noWalletProductionApi          = False
          , noWalletTxCreationDisabled     = False
          , noExplorerExtendedApi          = False
          }
    , ccTLS =
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
    , ccWallet =
        Wallet
          { waThrottle =  SetThrottle
            { thEnabled = False
            , thRate    = 0
            , thPeriod  = ""
            , thBurst   = 0
            }
          }
    }
