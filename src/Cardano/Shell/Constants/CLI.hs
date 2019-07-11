module Cardano.Shell.Constants.CLI
    ( configCoreCLIParser
    , parseGenesis
    , parseNetworkMagic
    , parseDBVersion
    ) where

import           Cardano.Prelude hiding (option)

import           Options.Applicative

import           Cardano.Shell.Constants.Types

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
    <$> lastOption parseGenesis
    <*> lastOption parseNetworkMagic
    <*> lastOption parseDBVersion

-- | Parser for the network magic options.
parseNetworkMagic :: Parser RequireNetworkMagic
parseNetworkMagic = requiredNetworkMagicParser <|> noRequiredNetworkMagicParser
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
parseDBVersion :: Parser Integer
parseDBVersion =
    option auto
        ( long "db-version"
       <> metavar "DB-VERSION"
       <> help "The version of the DB."
        )

-- | CLI parser for @Genesis@.
parseGenesis :: Parser PartialGenesis
parseGenesis =
    PartialGenesis
        <$> lastStrOption
           ( long "src-file-path"
          <> metavar "SRC-FILE-PATH"
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




