module Cardano.Shell.Constants.CLI
    ( configCoreCLIParser
    -- * Core CLI parsers
    , configGenesisCLIParser
    , configNetworkMagicCLIParser
    , configDBVersionCLIParser
    -- * Node
    , configNodeCLIParser
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

lastStrOption :: IsString a => Mod OptionFields a -> Parser (Last a)
lastStrOption args = Last <$> optional (strOption args)

--------------------------------------------------------------------------------
-- Core
--------------------------------------------------------------------------------

-- | The parser for the logging specific arguments.
configCoreCLIParser :: Parser PartialCore
configCoreCLIParser = PartialCore
    <$> lastOption configGenesisCLIParser
    <*> lastOption configNetworkMagicCLIParser
    <*> lastOption configDBVersionCLIParser

-- | CLI parser for @Genesis@.
configGenesisCLIParser :: Parser PartialGenesis
configGenesisCLIParser =
    PartialGenesis
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
        <*> lastStrOption
           ( long "prev-block-hash"
          <> metavar "PREV-BLOCK-HASH"
          <> help "The hash of the previous block."
           )

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
       <> metavar "DB-VERSION"
       <> help "The version of the DB."
        )



--------------------------------------------------------------------------------
-- Node
--------------------------------------------------------------------------------

-- | Node CLI parser.
configNodeCLIParser :: Parser PartialNode
configNodeCLIParser =
    PartialNode
        <$> option auto
           ( long "network-connection-timeout"
          <> metavar "CONNETION-TIMEOUT"
          <> help "Network connection timeout in milliseconds."
           )
        <*> option auto
           ( long "conversation-acknowledgement-timeout"
          <> metavar "ACKNOWLEDGEMENT-TIMEOUT"
          <> help "Conversation acknowledgement timeout in milliseconds."
           )
        <*> option auto
           ( long "block-queue-capacity"
          <> metavar "BLOCK-CAPACITY"
          <> help "Block retrieval queue capacity."
           )
        <*> option auto
           ( long "transaction-resubmission-delay"
          <> metavar "TX-RESUBMISSION-DELAY"
          <> help "Minimal delay between pending transactions resubmission."
           )
        <*> option auto
           ( long "wallet-production-api"
          <> metavar "WALLET-PROD-API-ENABLE"
          <> help "Whether hazard wallet endpoint should be disabled."
           )
        <*> option auto
           ( long "block-pending-transactions"
          <> metavar "PENDING-TX-BLOCK-ENABLE"
          <> help "Disallow transaction creation or re-submission of pending transactions by the wallet."
           )
        -- TODO(KS): Pretty sure we don't need this one.
        <*> option auto
           ( long "explorer-extended-api"
          <> metavar "EXPLORER-EXTENDED-API-ENABLE"
          <> help "Enable explorer extended API for fetching more."
           )

