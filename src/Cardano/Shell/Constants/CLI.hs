{-# LANGUAGE RankNTypes #-}

module Cardano.Shell.Constants.CLI
    ( configCardanoConfigurationCLIParser
    -- * Core CLI parsers
    , configCoreCLIParser
    -- * Node
    , configNodeCLIParser
    -- * NTP
    , configNTPCLIParser
    -- * TXP
    , configTXPCLIParser
    -- * Update
    , configUpdateCLIParser
    -- * SSC
    , configSSCCLIParser
    -- * DLG
    , configDLGCLIParser
    -- * Block
    , configBlockCLIParser
    -- * TLS
    , configTLSCLIParser
    , configCertificateCLIParser
    -- * Wallet
    , configWalletCLIParser
    ) where

import           Cardano.Prelude hiding (option)

import           Options.Applicative

import           Cardano.Shell.Constants.PartialTypes

--------------------------------------------------------------------------------
-- General
--------------------------------------------------------------------------------

-- | Lift the parser to an optional @Last@ type.
lastOption :: Parser a -> Parser (Last a)
lastOption parser = Last <$> optional parser

-- | General @Last@ auto option from @Read@ instance.
lastAutoOption :: Read a => Mod OptionFields a -> Parser (Last a)
lastAutoOption args = lastOption (option auto args)

lastIntOption :: Mod OptionFields Int -> Parser (Last Int)
lastIntOption = lastAutoOption

lastIntegerOption :: Mod OptionFields Integer -> Parser (Last Integer)
lastIntegerOption = lastAutoOption

lastDoubleOption :: Mod OptionFields Double -> Parser (Last Double)
lastDoubleOption = lastAutoOption

lastBoolOption :: Mod OptionFields Bool -> Parser (Last Bool)
lastBoolOption = lastAutoOption

lastWordOption :: Mod OptionFields Word -> Parser (Last Word)
lastWordOption = lastAutoOption

lastTextListOption :: Mod OptionFields [Text] -> Parser (Last [Text])
lastTextListOption = lastAutoOption

lastStrOption :: IsString a => Mod OptionFields a -> Parser (Last a)
lastStrOption args = Last <$> optional (strOption args)

--------------------------------------------------------------------------------
-- Cardano Configuration
--------------------------------------------------------------------------------

configCardanoConfigurationCLIParser :: Parser PartialCardanoConfiguration
configCardanoConfigurationCLIParser =
    PartialCardanoConfiguration
        <$> lastStrOption
            ( long "log-path"
           <> metavar "FILEPATH"
           <> help "The filepath to the log file."
            )
        <*> lastStrOption
            ( long "log-config"
            <> metavar "FILEPATH"
            <> help "The filepath to the log config file."
            )
        <*> lastStrOption
            ( long "db-path"
            <> metavar "FILEPATH"
            <> help "The filepath to the DB."
            )
        <*> lastStrOption
            ( long "application-lock-file"
            <> metavar "FILEPATH"
            <> help "The filepath to the application lock file."
            )
        <*> configCoreCLIParser
        <*> configNTPCLIParser
        <*> configUpdateCLIParser
        <*> configTXPCLIParser
        <*> configSSCCLIParser
        <*> configDLGCLIParser
        <*> configBlockCLIParser
        <*> configNodeCLIParser
        <*> configTLSCLIParser
        <*> configWalletCLIParser

--------------------------------------------------------------------------------
-- Core
--------------------------------------------------------------------------------

-- | The parser for the logging specific arguments.
configCoreCLIParser :: Parser PartialCore
configCoreCLIParser = PartialCore
    <$> lastStrOption
           ( long "genesis-file"
          <> metavar "FILEPATH"
          <> help "The filepath to the genesis file."
           )
    <*> lastStrOption
           ( long "genesis-hash"
          <> metavar "GENESIS-HASH"
          <> help "The genesis hash value."
           )
    <*> lastIntOption
           ( long "node-id"
          <> metavar "INT"
          <> help "Core node ID, the unique number of the node."
           )
    <*> lastIntOption
           ( long "num-cores"
          <> metavar "INT"
          <> help "The number of the core nodes."
           )
    <*> lastOption parseNodeProtocol
    <*> lastStrOption
           ( long "signing-key"
          <> metavar "FILEPATH"
          <> help "Path to the signing key."
           )
    <*> lastStrOption
           ( long "delegation-certificate"
          <> metavar "FILEPATH"
          <> help "Path to the delegation certificate."
           )
    <*> lastOption configNetworkMagicCLIParser
    <*> lastOption configDBVersionCLIParser
    <*> lastDoubleOption
           ( long "pbft-signature-threshold"
          <> metavar "DOUBLE"
          <> help "The PBFT signature threshold."
           )
  where
    -- | Parser for the network magic options.
    configNetworkMagicCLIParser :: Parser RequireNetworkMagic
    configNetworkMagicCLIParser = requiredNetworkMagicParser <|> noRequiredNetworkMagicParser
      where
        requiredNetworkMagicParser :: Parser RequireNetworkMagic
        requiredNetworkMagicParser = flag' RequireNetworkMagic
            ( long "require-network-magic"
           <> help "Requires network magic"
            )

        noRequiredNetworkMagicParser :: Parser RequireNetworkMagic
        noRequiredNetworkMagicParser = flag' NoRequireNetworkMagic
            ( long "no-require-network-magic"
           <> help "Doesn not require network magic"
            )

    -- | The parser for the DB version.
    configDBVersionCLIParser :: Parser Integer
    configDBVersionCLIParser =
        option auto
            ( long "db-version"
           <> metavar "VERSION"
           <> help "The version of the DB."
            )

    -- | The parser for the type of the node procotol.
    parseNodeProtocol :: Parser NodeProtocol
    parseNodeProtocol = asum
        [ flag' BFTProtocol $ mconcat
            [ long "bft"
            , help "Use the BFT consensus algorithm"
            ]
        , flag' PraosProtocol $ mconcat
            [ long "praos"
            , help "Use the Praos consensus algorithm"
            ]
        , flag' MockPBFTProtocol $ mconcat
            [ long "mock-pbft"
            , help "Use the Permissive BFT consensus algorithm using a mock ledger"
            ]
        , flag' RealPBFTProtocol $ mconcat
            [ long "real-pbft"
            , help "Use the Permissive BFT consensus algorithm using the real ledger"
            ]
        ]

--------------------------------------------------------------------------------
-- Node
--------------------------------------------------------------------------------

-- | Node CLI parser.
configNodeCLIParser :: Parser PartialNode
configNodeCLIParser =
    PartialNode
        <$> lastIntegerOption
           ( long "system-start"
          <> metavar "INTEGER"
          <> help "Node system start time."
           )
        <*> lastIntegerOption
           ( long "slot-length"
          <> metavar "INTEGER"
          <> help "Slot length time."
           )
        <*> lastIntOption
           ( long "network-connection-timeout"
          <> metavar "TIMEOUT"
          <> help "Network connection timeout in milliseconds."
           )
        <*> lastIntOption
           ( long "conversation-acknowledgement-timeout"
          <> metavar "TIMEOUT"
          <> help "Conversation acknowledgement timeout in milliseconds."
           )
        <*> lastIntOption
           ( long "block-queue-capacity"
          <> metavar "CAPACITY"
          <> help "Block retrieval queue capacity."
           )
        <*> lastIntOption
           ( long "transaction-resubmission-delay"
          <> metavar "DELAY"
          <> help "Minimal delay between pending transactions resubmission."
           )
        <*> lastBoolOption
           ( long "wallet-production-api"
          <> metavar "BOOL"
          <> help "Whether hazard wallet endpoint should be disabled."
           )
        <*> lastBoolOption
           ( long "block-pending-transactions"
          <> metavar "BOOL"
          <> help "Disallow transaction creation or re-submission of pending transactions by the wallet."
           )
        -- TODO(KS): Pretty sure we don't need this one.
        <*> lastBoolOption
           ( long "explorer-extended-api"
          <> metavar "BOOL"
          <> help "Enable explorer extended API for fetching more."
           )

--------------------------------------------------------------------------------
-- TXP
--------------------------------------------------------------------------------

-- | TXP CLI parser.
configTXPCLIParser :: Parser PartialTXP
configTXPCLIParser =
    PartialTXP
        <$> lastIntOption
           ( long "txp-mempool-queue-size"
          <> metavar "NUMBER"
          <> help "Limit on the number of transactions that can be stored in the mem pool."
           )
        <*> lastTextListOption
           ( long "txp-asset-locked-addresses"
          <> metavar "ADRESS-LIST"
          <> help "Set of source address which are asset-locked. Transactions which use these addresses as transaction inputs will be silently dropped."
           )

--------------------------------------------------------------------------------
-- Update
--------------------------------------------------------------------------------

-- | Update CLI parser.
configUpdateCLIParser :: Parser PartialUpdate
configUpdateCLIParser =
    PartialUpdate
        <$> lastStrOption
           ( long "update-application-name"
          <> metavar "NAME"
          <> help "The name of the application target update."
           )
        <*> lastIntOption
           ( long "update-application-version"
          <> metavar "VERSION"
          <> help "The version of the application target update."
           )
        <*> configLastKnownBlockVersionCLIParser

  where
    -- | Last known block version CLI parser.
    configLastKnownBlockVersionCLIParser :: Parser PartialLastKnownBlockVersion
    configLastKnownBlockVersionCLIParser =
        PartialLastKnownBlockVersion
            <$> lastIntOption
               ( long "last-block-version-major"
              <> metavar "INT"
              <> help "Last known block version major."
               )
            <*> lastIntOption
               ( long "last-block-version-minor"
              <> metavar "INT"
              <> help "Last known block version minor."
               )
            <*> lastIntOption
               ( long "last-block-version-alternative"
              <> metavar "INT"
              <> help "Last known block version alternative."
               )

--------------------------------------------------------------------------------
-- SSC
--------------------------------------------------------------------------------

-- | SSC CLI parser.
configSSCCLIParser :: Parser PartialSSC
configSSCCLIParser =
    PartialSSC
        <$> lastWordOption
           ( long "ssc-mpc-send-interval"
          <> metavar "INTERVAL"
          <> help "Length of interval for sending MPC message."
           )
        <*> lastIntOption
           ( long "ssc-no-commitments-epoch-threshold"
          <> metavar "THRESHOLD"
          <> help "Threshold of epochs for malicious activity detection."
           )
        <*> lastBoolOption
           ( long "ssc-no-report-no-secrets-for-fepoch"
          <> metavar "SERVER-LIST"
          <> help "Don't print “SSC couldn't compute seed” for the first epoch."
           )

--------------------------------------------------------------------------------
-- NTP
--------------------------------------------------------------------------------

-- | NTP CLI parser.
configNTPCLIParser :: Parser PartialNTP
configNTPCLIParser =
    PartialNTP
        <$> lastIntOption
           ( long "ntp-response-timeout"
          <> metavar "TIMEOUT"
          <> help "NTP response timeout."
           )
        <*> lastIntOption
           ( long "ntp-poll-delay"
          <> metavar "DELAY"
          <> help "NTP poll delay."
           )
        <*> lastTextListOption
           ( long "ntp-servers"
          <> metavar "SERVER-LIST"
          <> help "A list of NTP servers."
           )

--------------------------------------------------------------------------------
-- DLG
--------------------------------------------------------------------------------

-- | DLG CLI parser.
configDLGCLIParser :: Parser PartialDLG
configDLGCLIParser =
    PartialDLG
        <$> lastIntOption
           ( long "delegation-cache-size"
          <> metavar "CACHE-SIZE"
          <> help "This value parameterizes size of cache used in Delegation. Not bytes, but number of elements."
           )
        <*> lastIntOption
           ( long "delegation-cache-timeout"
          <> metavar "CACHE-AMOUNT"
          <> help "Interval we ignore cached messages for if it's sent again."
           )

--------------------------------------------------------------------------------
-- Block
--------------------------------------------------------------------------------

-- | Block CLI parser.
configBlockCLIParser :: Parser PartialBlock
configBlockCLIParser =
    PartialBlock
        <$> lastIntOption
           ( long "network-diameter"
          <> metavar "TIME"
          <> help "Estimated time needed to broadcast message from one node to all other nodes."
           )
        <*> lastIntOption
           ( long "recovery-headers-amount"
          <> metavar "AMOUNT"
          <> help "Maximum amount of headers node can put into headers message while in 'after offline' or 'recovery' mode."
           )
        <*> lastIntOption
           ( long "stream-window"
          <> metavar "CAPACITY"
          <> help "Number of blocks to have inflight."
           )
        <*> lastDoubleOption
           ( long "noncritical-cq-bootstrap"
          <> metavar "QUALITY"
          <> help "If chain quality in bootstrap era is less than this value, non critical misbehavior will be reported."
           )
        <*> lastDoubleOption
           ( long "critical-cq-bootstrap"
          <> metavar "QUALITY"
          <> help "If chain quality in bootstrap era is less than this value, critical misbehavior will be reported."
           )
        <*> lastDoubleOption
           ( long "noncritical-cq"
          <> metavar "QUALITY"
          <> help "If chain quality after bootstrap era is less than this value, non critical misbehavior will be reported."
           )
        <*> lastDoubleOption
           ( long "critical-cq"
          <> metavar "QUALITY"
          <> help "If chain quality after bootstrap era is less than this value, critical misbehavior will be reported."
           )
        <*> lastIntOption
           ( long "critical-fork-threshold"
          <> metavar "BLOCKS"
          <> help "Number of blocks such that if so many blocks are rolled back, it requires immediate reaction."
           )
        <*> lastIntOption
           ( long "fixed-time-cq"
          <> metavar "TIME"
          <> help "Chain quality will be also calculated for this amount of seconds."
           )

--------------------------------------------------------------------------------
-- Certificates
--------------------------------------------------------------------------------

-- | TLS CLI Parser.
configTLSCLIParser :: Parser PartialTLS
configTLSCLIParser =
    PartialTLS
        <$> configCertificateCLIParser
        <*> configCertificateCLIParser
        <*> configCertificateCLIParser

-- | Certificate CLI parser.
configCertificateCLIParser :: Parser PartialCertificate
configCertificateCLIParser =
    PartialCertificate
        <$> lastStrOption
           ( long "cert-organization-name"
          <> metavar "CERT-ORGANIZATION-NAME"
          <> help "Certificate organization."
           )
        <*> lastStrOption
           ( long "cert-common-name"
          <> metavar "CERT-COMMON-NAME"
          <> help "Certificate common name."
           )
        <*> lastIntOption
           ( long "cert-expiry-days"
          <> metavar "CERT-EXPIRY-DAYS"
          <> help "Certificate days of expiration."
           )
        <*> lastTextListOption
           ( long "cert-alternative-dns"
          <> metavar "CERT-ALTERNATIVE-DNS"
          <> help "Certificate alternative DNS."
           )

--------------------------------------------------------------------------------
-- Wallet
--------------------------------------------------------------------------------

-- | Wallet CLI parser.
configWalletCLIParser :: Parser PartialWallet
configWalletCLIParser =
    PartialWallet
        <$> lastBoolOption
           ( long "th-enabled"
          <> metavar "TH-ENABLED"
          <> help "Throttle enabled/disabled."
           )
        <*> lastIntOption
           ( long "th-rate"
          <> metavar "TH-RATE"
          <> help "Throttle rate."
           )
        <*> lastStrOption
           ( long "th-period"
          <> metavar "TH-PERIOD"
          <> help "Throttle period."
           )
        <*> lastIntOption
           ( long "th-burst"
          <> metavar "TH-BURST"
          <> help "Throttle burst."
           )

