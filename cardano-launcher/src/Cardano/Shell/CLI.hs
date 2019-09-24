module Cardano.Shell.CLI
    ( getLauncherOptions
    ) where

import           Cardano.Prelude

import           Cardano.Shell.Environment (SubstitutionError,
                                            substituteEnvVars)
import           Cardano.Shell.Launcher (LauncherOptions (..))
import           Control.Monad.Except (liftEither)
import           Data.Aeson (Result (..), fromJSON)
import           Data.Yaml (ParseException, decodeFileEither)
import           Distribution.System (OS (Windows), buildOS)
import           Options.Applicative (Parser, ParserInfo, execParser, fullDesc,
                                      header, help, helper, info, long, metavar,
                                      progDesc, short, strOption, value)
import           System.Directory (XdgDirectory (XdgData), getXdgDirectory)
import           System.Environment (getExecutablePath, setEnv)
import           System.FilePath (takeDirectory, (</>))

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
getDefaultConfigPath :: IO FilePath
getDefaultConfigPath = do
    launcherDir <- takeDirectory <$> getExecutablePath
    pure $ launcherDir </> "launcher-config.yaml"

-- | CLI for @LauncherOptionPath@
launcherArgsParser :: FilePath -> Parser LauncherOptionPath
launcherArgsParser defaultPath = LauncherOptionPath <$> strOption (
    short   'c' <>
    long    "config" <>
    help    ("Path to the launcher configuration file. If not provided, it'll\
        \ instead use\n" <> defaultPath) <>
    metavar "PATH" <>
    value defaultPath )

data LauncherOptionError
    = FailedToParseLauncherOption Text
    -- ^ Failed to convert yaml @Value@ into @LauncherOption@ type
    | FailedToDecodeFile ParseException
    -- ^ Failed to decode yaml file
    | SubstitutionFailed SubstitutionError
    -- ^ Failed to perform env var substitution
    deriving Show

-- | Command line argument parser for @LauncherOptions@
getLauncherOptions :: IO (Either LauncherOptionError LauncherOptions)
getLauncherOptions = do
    defaultPath <- getDefaultConfigPath
    loPath <- execParser $ opts defaultPath
    setupEnvVars loPath
    eLauncherOption <- decodeLauncherOption loPath
    case eLauncherOption of
        Left decodeError      -> return . Left $ decodeError
        Right launcherOptions -> return . Right $ launcherOptions
  where
    opts :: FilePath -> ParserInfo LauncherOptionPath
    opts path = info (launcherArgsParser path <**> helper)
        ( fullDesc
        <> progDesc "Tool for launching Daedalus"
        <> header "cardano-launcher"
        )
    -- There a lot of @withExceptT@ 's since all these function returns different
    -- types of @Either@ so I have to make the types align
    decodeLauncherOption :: LauncherOptionPath -> IO (Either LauncherOptionError LauncherOptions)
    decodeLauncherOption loPath = runExceptT $ do
            decodedVal <- withExceptT FailedToDecodeFile .
                ExceptT . decodeFileEither . getLauncherOptionPath $ loPath
            substituted <- withExceptT SubstitutionFailed .
                substituteEnvVars $ decodedVal
            parsed <- withExceptT FailedToParseLauncherOption .
                liftEither . resultToEither . fromJSON $ substituted
            return parsed
    -- Set environment variables that we need in order for launcher to perform
    -- env var substitution
    setupEnvVars :: LauncherOptionPath -> IO ()
    setupEnvVars (LauncherOptionPath configPath) = do
        daedalusDir <- takeDirectory <$> getExecutablePath
        setEnv "DAEDALUS_INSTALL_DIRECTORY" daedalusDir
        getXdgDirectory XdgData "" >>= setEnv "XDG_DATA_HOME"
        setEnv "LAUNCHER_CONFIG" configPath

-- | Convert @Result a@ type into @Either Text a@
resultToEither :: Result a -> Either Text a
resultToEither (Success a) = Right a
resultToEither (Error str) = Left (toS str)
