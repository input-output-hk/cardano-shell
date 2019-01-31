{-# LANGUAGE RecordWildCards #-}

module Cardano.Shell.Presets
    ( mainnetConfiguration
    , devConfiguration
    ) where

import Cardano.Shell.Types ( CardanoConfiguration (..)
                           , CardanoEnvironment (..)
                           , CardanoFeature (..)
                           , CardanoFeatureInit (..)
                           , NoDependency (..)
                           , ApplicationEnvironment (..)
                           , CardanoApplication (..)
                           , initializeCardanoEnvironment
                           , loadCardanoConfiguration
                           , applicationProductionMode
                           , Core (..)
                           , Genesis (..)
                           , Spec (..)
                           , Initializer (..)
                           , TestBalance (..)
                           , FakeAvvmBalance (..)
                           , BlockVersionData (..)
                           , LastKnownBlockVersion (..)
                           , SoftForkRule (..)
                           , TxFeePolicy (..)
                           , TxSizeLinear (..)
                           , ProtocolConstants (..)
                           , NTP (..)
                           , Update (..)
                           , TXP (..)
                           , SSC (..)
                           , DLG (..)
                           , Block (..)
                           , Node (..)
                           , TLS (..)
                           , Wallet (..)
                           , Throttle (..)
                           , Certificate (..)
                           )

--------------------------------------------------------------------------------
-- Cardano Mainnet Configuration
--------------------------------------------------------------------------------

mainnetConfiguration :: CardanoConfiguration
mainnetConfiguration = CardanoConfiguration
                       { ccLogPath  = "./logs/"
                       , ccLogConfig = "./log-config.yaml"
                       , ccDBPath   = "./db/"
                       , ccApplicationLockFile = ""
                       , ccCore       = Core { coGenesis =
                                          Genesis { geInternal = False
                                                  , geSpec     = Spec {..}
                                                  , geSrc      = "mainnet-genesis.json"
                                                  , geFileHash = "5f20df933584822601f9e3f8c024eb5eb252fe8cefb24d1317dc3d432e940ebb"
                                                  }
                                             , coRequiresNetworkMagic = "NetworkMainOrStage"
                                             , coDBSerializeVersion   = 0
                                             }
                       , ccNTP        = NTP { ntpResponseTimeout = 30000000
                                            , ntpPollDelay       = 1800000000
                                            , ntpServers         = [ "0.pool.ntp.org"
                                                                , "2.pool.ntp.org"
                                                                , "3.pool.ntp.org"
                                                                ]
                                            }
                       , ccUpdate     = Update { upApplicationName       = "cardano-sl"
                                               , upApplicationVersion    = 1
                                               , upLastKnownBlockVersion =
                                                   LastKnownBlockVersion { lkbvMajor = 0
                                                                         , lkbvMinor = 2
                                                                         , lkbvAlt   = 0
                                                                         }
                                               }
                       , ccTXP        = TXP { txpMemPoolLimitTx = 200
                                            , txpAssetLockedSrcAddress = []
                                             }
                       , ccSSC        = SSC { sscMPCSendInterval               = 100
                                            , sscMdNoCommitmentsEpochThreshold = 3
                                            , sscNoReportNoSecretsForEpoch1    = True
                                            }
                       , ccDLG        = DLG { dlgCacheParam       = 500
                                            , dlgMessageCacheTimeout = 30
                                            }
                       , ccBlock      = Block { blNetworkDiameter        = 18
                                              , blRecoveryHeadersMessage = 2200
                                              , blStreamWindow           = 2048
                                              , blNonCriticalCQBootstrap = 0.95
                                              , blNonCriticalCQ          = 0.8
                                              , blCriticalCQBootstrap    = 0.8888
                                              , blCriticalCQ             = 0.654321
                                              , blCriticalForkThreshold  = 3
                                              , blFixedTimeCQ            = 3600
                                              }
                       , ccNode       = Node { noNetworkConnectionTimeout     = 15000
                                             , noConversationEstablishTimeout = 30000
                                             , noBlockRetrievalQueueSize      = 100
                                             , noPendingTxResubmissionPeriod  = 7
                                             , noWalletProductionApi          = True
                                             , noWalletTxCreationDisabled     = False
                                             , noExplorerExtendedApi          = False
                                             }
                       , ccTLS        = TLS { tlsCA      = Certificate
                                                            { certOrganization = "Input Output HK"
                                                            , certCommonName   = "Cardano SL Self-Signed Root CA"
                                                            , certExpiryDays   = 3600
                                                            , certAltDNS       = []
                                                            }
                                            , tlsServer  = Certificate
                                                            { certOrganization = "Input Output HK"
                                                            , certCommonName   = "Cardano SL Server Node"
                                                            , certExpiryDays   = 3600
                                                            , certAltDNS       = [ "localhost"
                                                                             , "localhost.localdomain"
                                                                             , "127.0.0.1"
                                                                             , "::1" ]
                                                            }
                                            , tlsClients = Certificate
                                                            { certOrganization = "Input Output HK"
                                                            , certCommonName   = "Daedalus Wallet"
                                                            , certExpiryDays   = 3600
                                                            , certAltDNS       = []
                                                            }
                                            }
                       , ccWallet    = Wallet { waThrottle = SetThrottle { thEnabled = False
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
devConfiguration = CardanoConfiguration
                       { ccLogPath  = "./logs/"
                       , ccDBPath   = "./db/"
                       , ccLogConfig = "./log-config.yaml"
                       , ccApplicationLockFile = ""
                       , ccCore     = Core { coGenesis  =
                                        Genesis { geSpec =
                                          Spec { spInitializer =
                                            Initializer { inTestBalance =
                                              TestBalance { tePoors          = 12
                                                          , teRichmen        = 4
                                                          , teRichmenShare   = 0.99
                                                          , teUseHDAddresses = True
                                                          , teTotalBalance   = 600000000000000000
                                                          }
                                                        , inFakeAvvmBalance  =
                                                            FakeAvvmBalance { faCount      = 10
                                                                            , faOneBalance = 100000
                                                                            }
                                                        , inAVVMBalanceFactor = 1
                                                        , inUseHeavyDlg       = True
                                                        , inSeed              = 0
                                                        }

                                               , spBlockVersionData  =
                                                   BlockVersionData { bvdScriptVersion = 0
                                                                    , bvdSlotDuration  = 7000
                                                                    , bvdMaxBlockSize  = 2000000
                                                                    , bvdMaxHeaderSize = 2000000
                                                                    , bvdMaxTxSize     = 4096
                                                                    , bvdMaxProposalSize = 700
                                                                    , bvdMpcThd            = 0.01
                                                                    , bvdHeavyDelThd       = 0.005
                                                                    , bvdUpdateVoteThd     = 0.001
                                                                    , bvdUpdateProposalThd = 0.1
                                                                    , bvdUpdateImplicit    = 10
                                                                    , bvdSoftforkRule =
                                                                        SoftForkRule { sfrInitThd      = 0.9
                                                                                     , sfrMinThd       = 0.6
                                                                                     , sfrThdDecrement = 0.05
                                                                                     }
                                                                    , bvdTXFeePolicy =
                                                                        TxFeePolicy { txfTXSizeLinear =
                                                                          TxSizeLinear { txsA = 155381
                                                                                       , txsB = 43.946
                                                                                       }
                                                                                    }
                                                                    , bvdUnlockStakeEpoch = 18446744073709551615
                                                                    }

                                               , spProtocolConstants =
                                                   ProtocolConstants { prK             = 2
                                                                     , prProtocolMagic = 55550001
                                                                     }
                                               , spFTSSeed           = "c2tvdm9yb2RhIEdndXJkYSBib3JvZGEgcHJvdm9kYSA="
                                               , spHeavyDelegation   = ""
                                               , spAVVMDistr         = ""
                                               }
                                                        }
                                          , coRequiresNetworkMagic = "RequiresNoMagic"
                                          , coDBSerializeVersion   = 0
                                          }
                       , ccNTP        = NTP { ntpResponseTimeout = 30000000
                                            , ntpPollDelay       = 1800000000
                                            , ntpServers         = [ "0.pool.ntp.org"
                                                                , "2.pool.ntp.org"
                                                                , "3.pool.ntp.org"
                                                                ]
                                            }
                       , ccUpdate     = Update { upApplicationName       = "cardano-sl"
                                               , upApplicationVersion    = 0
                                               , upLastKnownBlockVersion =
                                                   LastKnownBlockVersion { lkbvMajor = 0
                                                                         , lkbvMinor = 0
                                                                         , lkbvAlt   = 0
                                                                         }
                                               }
                       , ccTXP        = TXP { txpMemPoolLimitTx = 200
                                            , txpAssetLockedSrcAddress = []
                                            }
                       , ccSSC        = SSC { sscMPCSendInterval               = 10
                                            , sscMdNoCommitmentsEpochThreshold = 3
                                            , sscNoReportNoSecretsForEpoch1    = False
                                            }
                       , ccDLG        = DLG { dlgCacheParam       = 500
                                            , dlgMessageCacheTimeout = 30
                                            }
                       , ccBlock      = Block { blNetworkDiameter        = 3
                                              , blRecoveryHeadersMessage = 20
                                              , blStreamWindow           = 2048
                                              , blNonCriticalCQBootstrap = 0.95
                                              , blNonCriticalCQ          = 0.8
                                              , blCriticalCQBootstrap    = 0.8888
                                              , blCriticalCQ             = 0.654321
                                              , blCriticalForkThreshold  = 2
                                              , blFixedTimeCQ            = 10
                                              }
                       , ccNode       = Node { noNetworkConnectionTimeout     = 15000
                                             , noConversationEstablishTimeout = 30000
                                             , noBlockRetrievalQueueSize      = 100
                                             , noPendingTxResubmissionPeriod  = 7
                                             , noWalletProductionApi          = False
                                             , noWalletTxCreationDisabled     = False
                                             , noExplorerExtendedApi          = False
                                             }
                       , ccTLS        = TLS { tlsCA      = Certificate
                                                            { certOrganization = "Input Output HK"
                                                            , certCommonName   = "Cardano SL Self-Signed Root CA"
                                                            , certExpiryDays   = 3650
                                                            , certAltDNS       = []
                                                            }
                                            , tlsServer  = Certificate
                                                            { certOrganization = "Input Output HK"
                                                            , certCommonName   = "Cardano SL Server Node"
                                                            , certExpiryDays   = 365
                                                            , certAltDNS       = [ "localhost"
                                                                             , "localhost.localdomain"
                                                                             , "127.0.0.1"
                                                                             , "::1" ]
                                                            }
                                            , tlsClients = Certificate
                                                            { certOrganization = "Input Output HK"
                                                            , certCommonName   = "Daedalus Wallet"
                                                            , certExpiryDays   = 365
                                                            , certAltDNS       = []
                                                            }
                                            }
                       , ccWallet     =
                           Wallet { waThrottle =  SetThrottle { thEnabled = False
                                                              , thRate    = 0
                                                              , thPeriod  = ""
                                                              , thBurst   = 0
                                                              }
                                 }
                       }