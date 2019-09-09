module Cardano.Shell.CLI
    ( getLauncherOptions
    ) where

import           Cardano.Prelude

import           Data.Yaml (ParseException, decodeFileEither)
import           Options.Applicative (Parser, ParserInfo, execParser, fullDesc,
                                      header, help, helper, info, long, metavar,
                                      progDesc, short, strOption, value)
import           System.Environment (getExecutablePath)
import           System.FilePath (takeDirectory, (</>))

import           Cardano.Shell.Launcher

-- | Path to launcher-config.yaml file
newtype LauncherOptionPath = LauncherOptionPath
    { getLauncherOptionPath  :: FilePath
    }

-- | Default path to the launcher-config.yaml file
--
-- This used on both windows and mac.
--
-- this will enable the launcher to load launcher-config.yaml from the same
-- directory as the cardano-launcher binary
-- This will be used if the filepath was not provided via CLI
getDefaultConfigPath :: IO FilePath
getDefaultConfigPath = do
    launcherDir <- takeDirectory <$> getExecutablePath
    pure $ launcherDir </> "launcher-config.yaml"

-- | CLI for @LauncherOptionPath@
launcherArgsParser :: FilePath -> Parser LauncherOptionPath
launcherArgsParser defaultPath = LauncherOptionPath <$>
    strOption (
        short   'c' <>
        long    "config" <>
        help    ("Path to the launcher configuration file. If not provided, it'll\
                \ instead use\n" <> defaultPath) <>
        metavar "PATH" <>
        value defaultPath )

data LauncherOptionError =
    FailedToParseLauncherOption ParseException
    -- ^ Failed to parse launcher-config.yaml
    deriving Show

-- | Parser
getLauncherOptions :: IO (Either LauncherOptionError LauncherOptions)
getLauncherOptions = do
    defaultPath <- getDefaultConfigPath
    loPath <- execParser $ opts defaultPath
    eLauncherOption <- decodeFileEither $ getLauncherOptionPath loPath
    case eLauncherOption of
        Left parseError -> return . Left $ FailedToParseLauncherOption parseError
        Right launcherOptions -> return . Right $ launcherOptions
  where
    opts :: FilePath -> ParserInfo LauncherOptionPath
    opts path = info (launcherArgsParser path <**> helper)
        ( fullDesc
        <> progDesc "Tool for launching Daedalus"
        <> header "cardano-launcher"
        )
