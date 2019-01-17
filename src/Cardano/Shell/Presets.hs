module Cardano.Shell.Presets
    ( mainnetConfiguration
    , devConfiguration
    ) where

import Cardano.Shell.Types ( Core (..)
                           , GenesisExternal (..)
                           , GenesisInternal (..)
                           , Spec (..)
                           , Initializer (..)
                           , TestBalance (..)
                           , FakeAvvmBalance (..)
                           , BlockVersionData (..)
                           , SoftForkRule (..)
                           , TxFeePolicy (..)
                           , TxSizeLinear (..)
                           , ProtocolConstants 
                           , NTP (..)
                           , Update (..)
                           , TXP (..)
                           , SSC (..)
                           , DLG (..)
                           , Block (..)
                           , Node (..)
                           , TLS (..)
                           , Wallet (..)
                           , NoThrottle (..)
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
                       , ccCore       = Core { genesis =
                                          GenesisExternal { src      = "mainnet-genesis.json"
                                                          , fileHash = "5f20df933584822601f9e3f8c024eb5eb252fe8cefb24d1317dc3d432e940ebb"
                                                          }
                                             , requiresNetworkMagic = "NetworkMainOrStage"
                                             , dbSerializeVersion   = 0
                                             }
                       , ccNTP        = NTP { responseTimeout = 30000000
                                            , pollDelay       = 1800000000
                                            , servers         = [ "0.pool.ntp.org"
                                                                , "2.pool.ntp.org"
                                                                , "3.pool.ntp.org"
                                                                ]
                                            }
                       , ccUpdate     = Update { applicationName       = "cardano-sl"
                                               , applicationVersion    = 1
                                               , lastKnownBlockVersion =
                                                   LastKnownBlockVersion { bvMajor = 0
                                                                         , bvMinor = 2
                                                                         , bvAlt   = 0
                                                                         }
                                               }
                       , ccTXP        = TXP { memPoolLimitTx = 200
                                            , assetLockedSrcAddress = []
                                             }
                       , ccSSC        = SSC { mpcSendInterval               = 100
                                            , mdNoCommitmentsEpochThreshold = 3
                                            , noReportNoSecretsForEpoch1    = True
                                            }
                       , ccDLG        = DLG { dlgCacheParam       = 500
                                            , messageCacheTimeout = 30
                                            }
                       , ccBlock      = Block { networkDiameter        = 18
                                              , recoveryHeadersMessage = 2200
                                              , streamWindow           = 2048
                                              , nonCriticalCQBootstrap = 0.95
                                              , nonCriticalCQ          = 0.8
                                              , criticalCQBootstrap    = 0.8888
                                              , criticalCQ             = 0.654321
                                              , criticalForkThreshold  = 3
                                              , fixedTimeCQ            = 3600
                                              }
                       , ccNode       = Node { networkConnectionTimeout     = 15000
                                             , conversationEstablishTimeout = 30000
                                             , blockRetrievalQueueSize      = 100
                                             , pendingTxResubmissionPeriod  = 7
                                             , walletProductionApi          = True
                                             , walletTxCreationDisabled     = False
                                             , explorerExtendedApi          = False
                                             }
                       , ccTLS        = TLS { ca      = Certificate
                                                            { organization = "Input Output HK"
                                                            , commonName   = "Cardano SL Self-Signed Root CA"
                                                            , expiryDays   = 3600
                                                            , altDNS       = []
                                                            }
                                            , server  = Certificate
                                                            { organization = "Input Output HK"
                                                            , commonName   = "Cardano SL Server Node"
                                                            , expiryDays   = 3600
                                                            , altDNS       = [ "localhost"
                                                                             , "localhost.localdomain"
                                                                             , "127.0.0.1"
                                                                             , "::1" ]
                                                            }
                                            , clients = Certificate
                                                            { organization = "Input Output HK"
                                                            , commonName   = "Daedalus Wallet"
                                                            , expiryDays   = 3600
                                                            , altDNS       = []
                                                            }
                                            }
                       , ccWallet    = Wallet { throttle = NoThrottle }
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
                       , ccCore     = Core { genesis  =
                                        GenesisInternal { spec =
                                          Spec { initializer =
                                            Initializer { testBalance =
                                              TestBalance { poors          = 12
                                                          , richmen        = 4
                                                          , richmenShare   = 0.99
                                                          , useHDAddresses = True
                                                          , totalBalance   = 600000000000000000
                                                          }
                                                        , fakeAvvmBalance  =
                                                            FakeAvvmBalance { count      = 10
                                                                            , oneBalance = 100000
                                                                            }
                                                        , avvmBalanceFactor = 1
                                                        , useHeavyDlg       = True
                                                        , seed              = 0
                                                        }

                                               , blockVersionData  =
                                                   BlockVersionData { scriptVersion = 0
                                                                    , slotDuration  = 7000
                                                                    , maxBlockSize  = 2000000
                                                                    , maxHeaderSize = 2000000
                                                                    , maxTxSize     = 4096
                                                                    , maxProposalSize = 700
                                                                    , mpcThd            = 0.01
                                                                    , heavyDelThd       = 0.005
                                                                    , updateVoteThd     = 0.001
                                                                    , updateProposalThd = 0.1
                                                                    , updateImplicit    = 10
                                                                    , softforkRule =
                                                                        SoftForkRule { initThd      = 0.9
                                                                                     , minThd       = 0.6
                                                                                     , thdDecrement = 0.05
                                                                                     }
                                                                    , txFeePolicy =
                                                                        TxFeePolicy { txSizeLinear =
                                                                          TxSizeLinear { a = 155381
                                                                                       , b = 43.946
                                                                                       }
                                                                                    }
                                                                    , unlockStakeEpoch = 18446744073709551615
                                                                    }

                                               , protocolConstants =
                                                   ProtocolConstants { k             = 2
                                                                     , protocolMagic = 55550001
                                                                     }
                                               , ftsSeed           = "c2tvdm9yb2RhIEdndXJkYSBib3JvZGEgcHJvdm9kYSA="
                                               , heavyDelegation   = ""
                                               , avvmDistr         = ""
                                               }
                                                        }
                                          , requiresNetworkMagic = "RequiresNoMagic"
                                          , dbSerializeVersion   = 0
                                          }
                       , ccNTP        = NTP { responseTimeout = 30000000
                                            , pollDelay       = 1800000000
                                            , servers         = [ "0.pool.ntp.org"
                                                                , "2.pool.ntp.org"
                                                                , "3.pool.ntp.org"
                                                                ]
                                            }
                       , ccUpdate     = Update { applicationName       = "cardano-sl"
                                               , applicationVersion    = 0
                                               , lastKnownBlockVersion =
                                                   LastKnownBlockVersion { bvMajor = 0
                                                                         , bvMinor = 0
                                                                         , bvAlt   = 0
                                                                         }
                                               }
                       , ccTXP        = TXP { memPoolLimitTx = 200
                                            , assetLockedSrcAddress = []
                                            }
                       , ccSSC        = SSC { mpcSendInterval               = 10
                                            , mdNoCommitmentsEpochThreshold = 3
                                            , noReportNoSecretsForEpoch1    = False
                                            }
                       , ccDLG        = DLG { dlgCacheParam       = 500
                                            , messageCacheTimeout = 30
                                            }
                       , ccBlock      = Block { networkDiameter        = 3
                                              , recoveryHeadersMessage = 20
                                              , streamWindow           = 2048
                                              , nonCriticalCQBootstrap = 0.95
                                              , nonCriticalCQ          = 0.8
                                              , criticalCQBootstrap    = 0.8888
                                              , criticalCQ             = 0.654321
                                              , criticalForkThreshold  = 2
                                              , fixedTimeCQ            = 10
                                              }
                       , ccNode       = Node { networkConnectionTimeout     = 15000
                                             , conversationEstablishTimeout = 30000
                                             , blockRetrievalQueueSize      = 100
                                             , pendingTxResubmissionPeriod  = 7
                                             , walletProductionApi          = False
                                             , walletTxCreationDisabled     = False
                                             , explorerExtendedApi          = False
                                             }
                       , ccTLS        = TLS { ca      = Certificate
                                                            { organization = "Input Output HK"
                                                            , commonName   = "Cardano SL Self-Signed Root CA"
                                                            , expiryDays   = 3650
                                                            , altDNS       = []
                                                            }
                                            , server  = Certificate
                                                            { organization = "Input Output HK"
                                                            , commonName   = "Cardano SL Server Node"
                                                            , expiryDays   = 365
                                                            , altDNS       = [ "localhost"
                                                                             , "localhost.localdomain"
                                                                             , "127.0.0.1"
                                                                             , "::1" ]
                                                            }
                                            , clients = Certificate
                                                            { organization = "Input Output HK"
                                                            , commonName   = "Daedalus Wallet"
                                                            , expiryDays   = 365
                                                            , altDNS       = []
                                                            }
                                            }
                       , ccWallet     =
                           Wallet { throttle = NoThrottle }
                       }