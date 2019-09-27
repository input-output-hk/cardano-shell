{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE MultiParamTypeClasses      #-}

module Cardano.Shell.Launcher
    ( WalletMode (..)
    , LauncherConfig (..)
    , WalletArguments (..)
    , WalletPath (..)
    , WalletRunner (..)
    , walletRunnerProcess
    , ExternalDependencies (..)
    -- * Functions
    , runWalletProcess
    -- * Critical exports (testing)
    , DaedalusExitCode (..)
    , handleDaedalusExitCode
    , UpdateRunner (..)
    , RestartRunner (..)
    -- * Typeclass
    , Isomorphism (..)
    -- * Configuration
    , ConfigurationOptions(..)
    , LauncherOptions(..)
    , getUpdaterData
    , getWargs
    , getWPath
    , getLauncherOption
    , setWorkingDirectory
    ) where

import           Cardano.Prelude
import           Prelude (Show (..))

import           Data.Aeson (FromJSON (..), withObject, (.:), (.:?))
import           Data.Time.Units (Microsecond, fromMicroseconds)
import           Data.Yaml (ParseException, decodeFileEither)

import           System.Directory (doesDirectoryExist, setCurrentDirectory)
import qualified System.Process as Process
import           Turtle (system)

import           Cardano.Shell.Update.Lib (UpdaterData (..), runUpdater)

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Launcher configuration
data LauncherConfig = LauncherConfig
    { lcfgFilePath    :: !Text -- We really need @FilePath@ here.
    , lcfgKey         :: !Text
    , lcfgSystemStart :: !(Maybe Integer)
    , lcfgSeed        :: !(Maybe Integer)
    } deriving (Eq, Show)

-- | Arguments that will be used to execute the wallet
newtype WalletArguments = WalletArguments
    { getWalletArguments :: [Text]
    } deriving (Eq, Show)

-- | We define the instance on it's wrapped type.
instance Semigroup WalletArguments where
    (<>) = \wArgs1 wArgs2 -> WalletArguments $ getWalletArguments wArgs1 <> getWalletArguments wArgs2

newtype WalletPath = WalletPath
    { getWalletPath :: Text
    } deriving (Eq, Show)

data ExternalDependencies = ExternalDependencies
    { logInfo   :: Text -> IO ()
    , logError  :: Text -> IO ()
    , logNotice :: Text -> IO ()
    }

-- | This is here so we don't mess up the order. It's VERY important.
-- The type that runs the update.
newtype UpdateRunner = UpdateRunner { runUpdate :: IO ExitCode }

-- | There is no way we can show this value.
instance Show UpdateRunner where
    show _ = "<UpdateRunner>"

-- | This type is responsible for launching and re-launching the wallet
-- inside the launcher process.
-- Do we want to restart it in @WalletModeSafe@ or not?
newtype RestartRunner = RestartRunner { runRestart :: WalletMode -> IO ExitCode }

-- | There is no way we can show this value.
instance Show RestartRunner where
    show _ = "<RestartRunner>"

-- | The wallet mode that it's supposed to use.
-- Here we are making the @WalletMode@ explicit.
data WalletMode
    = WalletModeNormal
    | WalletModeSafe
    deriving (Eq, Show)

-- | All the important exit codes. Since we cover "other" cases as well, this is a total mapping.
-- That is good.
-- TODO(KS): We could extend this to try to encode some interesting properties about it.
data DaedalusExitCode
    = RunUpdate
    -- ^ Daedalus is ready to run the update system.
    | RestartInGPUSafeMode
    -- ^ Daedalus asks launcher to relaunch Daedalus with GPU safe mode.
    | RestartInGPUNormalMode
    -- ^ Daedalus asks launcher to relaunch Daedalus with normal mode (turn off GPU safe mode).
    | ExitCodeFailure Int
    -- ^ Daedalus wants launcher to exit as well. Unexpected exit code.
    | ExitCodeSuccess
    -- ^ Daedalus "happy path" where it could shut down with success.
    deriving (Eq, Show, Generic)

-- | A simplified typeclass. Maybe we could fetch it from somewhere?
-- This will work for this case.
--
-- from . to == to . from == id
class Isomorphism a b where
    isoFrom     :: a -> b
    isoTo       :: b -> a

-- | A simple instance for converting there and back.
-- The main reason we have it is so we can decouple the implementation.
-- It's a very convenient way to define what exit code means what.
-- Not all that type safe, though, but at least it's defined in one place.
instance Isomorphism DaedalusExitCode ExitCode where

    isoFrom =   \case
        RunUpdate               -> ExitFailure 20
        RestartInGPUSafeMode    -> ExitFailure 21
        RestartInGPUNormalMode  -> ExitFailure 22

        ExitCodeSuccess         -> ExitSuccess
        ExitCodeFailure ef      -> ExitFailure ef

    isoTo   =   \case
        ExitFailure 20          -> RunUpdate
        ExitFailure 21          -> RestartInGPUSafeMode
        ExitFailure 22          -> RestartInGPUNormalMode

        ExitSuccess             -> ExitCodeSuccess
        ExitFailure ef          -> ExitCodeFailure ef


--------------------------------------------------------------------------------
-- Functions
--------------------------------------------------------------------------------

-- | Here we handle the exit codes.
-- It's a simple mapping from exit code to actions that the launcher takes.
--
-- This is much simpler to test, no?
handleDaedalusExitCode
    :: UpdateRunner
    -> RestartRunner
    -> DaedalusExitCode
    -> IO DaedalusExitCode
handleDaedalusExitCode runUpdater restartWallet = isoTo <<$>> \case
    RunUpdate               -> runUpdate runUpdater >> runRestart restartWallet WalletModeNormal
    -- Run the actual update, THEN restart launcher.
    -- Do we maybe need to handle the update ExitCode as well?
    RestartInGPUSafeMode    -> runRestart restartWallet WalletModeSafe
    -- Enable safe mode (GPU safe mode).
    RestartInGPUNormalMode  -> runRestart restartWallet WalletModeNormal
    -- Disable safe mode (GPU safe mode).
    ExitCodeSuccess         -> return ExitSuccess
    -- All is well, exit "mucho bien".
    ExitCodeFailure ef      -> return $ ExitFailure ef
    -- Some other unexpected error popped up.

-- | Wallet runner type.
-- I give you the path to the wallet, it's arguments and you execute it
-- and return me the @ExitCode@.
newtype WalletRunner = WalletRunner
    { runWalletSystemProcess :: WalletPath -> WalletArguments -> IO ExitCode
    }

-- | Launching the wallet.
-- For now, this is really light since we don't know whether we will reuse the
-- older configuration and if so, which parts of it.
-- We passed in the bare minimum and if we require anything else, we will add it.
runWalletProcess
    :: ExternalDependencies
    -> WalletMode
    -> WalletPath
    -> WalletArguments
    -> WalletRunner
    -> UpdaterData
    -> IO ExitCode
runWalletProcess ed walletMode walletPath walletArguments walletRunner updaterData = do

    -- Parametrized by @WalletMode@ so we can change it on restart depending
    -- on the Daedalus exit code.
    let restart :: WalletMode -> IO ExitCode
        restart =  \walletMode' -> runWalletProcess
                        ed
                        walletMode'
                        walletPath
                        walletArguments
                        walletRunner
                        updaterData

    -- Additional arguments we need to pass if it's a SAFE mode.
    let walletSafeModeArgs :: WalletArguments
        walletSafeModeArgs = WalletArguments [ "--safe-mode", "--disable-gpu", "--disable-d3d11" ]

    -- Daedalus safe mode.
    let walletArgs :: WalletArguments
        walletArgs =    if walletMode == WalletModeSafe
                            then walletArguments <> walletSafeModeArgs
                            else walletArguments

    logNotice ed $ "Starting the wallet"

    -- create the wallet process
    walletExitStatus <- runWalletSystemProcess walletRunner walletPath walletArgs

    -- Let us map the interesting commands into a very simple "language".
    let exitCode :: DaedalusExitCode
        exitCode = isoTo walletExitStatus

    -- Here we can interpret what that simple "language" means. This allows us to "cut"
    -- through the function and separate it. When we decouple it, we can test parts in isolation.
    -- We separate the description of the computation, from the computation itself.
    -- There are other ways of doing this, of course.
    isoFrom <$> handleDaedalusExitCode
        (UpdateRunner $ runUpdater updaterData)
        (RestartRunner restart)
        exitCode


-- | Create the wallet runner proces which will actually run the wallet.
walletRunnerProcess :: WalletRunner
walletRunnerProcess = WalletRunner $ \walletPath walletArgs ->
    system (createProc Process.Inherit walletPath walletArgs) mempty
  where
    -- | The creation of the process.
    createProc
        :: Process.StdStream
        -> WalletPath
        -> WalletArguments
        -> Process.CreateProcess
    createProc stdStream (WalletPath commandPath) (WalletArguments commandArguments) =
        (Process.proc (toS commandPath) (map toS commandArguments))
            { Process.std_in    = Process.CreatePipe
            , Process.std_out   = stdStream
            , Process.std_err   = stdStream
            }

--------------------------------------------------------------------------------
-- Configuration
--------------------------------------------------------------------------------

-- Todo: Add haddock comment for each field
-- | Launcher options
data LauncherOptions = LauncherOptions
    { loConfiguration       :: !ConfigurationOptions
    , loTlsPath             :: !FilePath
    , loUpdaterPath         :: !FilePath
    , loUpdaterArgs         :: ![Text]
    , loUpdateArchive       :: !(Maybe FilePath)
    , loUpdateWindowsRunner :: !(Maybe FilePath)
    , loWalletPath          :: !FilePath
    , loWalletArgs          :: ![Text]
    , loWorkingDirectory    :: !FilePath
    } deriving (Show, Generic)

instance FromJSON LauncherOptions where
    parseJSON = withObject "LauncherOptions" $ \o -> do

        walletPath          <- o .: "walletPath"
        walletArgs          <- o .: "walletArgs"
        updaterPath         <- o .: "updaterPath"
        updaterArgs         <- o .: "updaterArgs"
        updateArchive       <- o .: "updateArchive"
        updateWindowsRunner <- o .: "updateWindowsRunner"
        configuration       <- o .: "configuration"
        tlsPath             <- o .: "tlsPath"
        workingDir          <- o .: "workingDir"

        pure $ LauncherOptions
            configuration
            tlsPath
            updaterPath
            updaterArgs
            updateArchive
            updateWindowsRunner
            walletPath
            walletArgs
            workingDir

-- | Configuration yaml file location and the key to use. The file should
-- parse to a MultiConfiguration and the 'cfoKey' should be one of the keys
-- in the map.
data ConfigurationOptions = ConfigurationOptions
    { cfoFilePath    :: !FilePath
    , cfoKey         :: !Text
    , cfoSystemStart :: !(Maybe Timestamp)
    -- ^ An optional system start time override. Required when using a
    -- testnet genesis configuration.
    , cfoSeed        :: !(Maybe Integer)
    -- ^ Seed for secrets generation can be provided via CLI, in
    -- this case it overrides one from configuration file.
    } deriving (Show)

-- | Timestamp is a number which represents some point in time. It is
-- used in MonadSlots and its meaning is up to implementation of this
-- type class. The only necessary knowledge is that difference between
-- timestamps is microsecond. Hence underlying type is Microsecond.
-- Amount of microseconds since Jan 1, 1970 UTC.

newtype Timestamp = Timestamp
    { getTimestamp :: Microsecond
    } deriving (Show, Num, Eq, Ord, Enum, Real, Integral, Typeable, Generic)

instance FromJSON ConfigurationOptions where
    parseJSON = withObject "ConfigurationOptions" $ \o -> do
        path            <- o .: "filePath"
        key             <- o .: "key"
        systemStart     <- (Timestamp . fromMicroseconds . (*) 1000000) <<$>> o .:? "systemStart"
        seed            <- o .:? "seed"
        pure $ ConfigurationOptions path key systemStart seed

-- | Parses config file and return @LauncherOptions@ if successful
getLauncherOption :: FilePath -> IO (Either ParseException LauncherOptions)
getLauncherOption = decodeFileEither

--------------------------------------------------------------------------------
-- These functions will take LauncherOptions as an argument and put together
-- that data so that it can be used
--------------------------------------------------------------------------------

-- | Create @UpdaterData@ with given @LauncherOptions@
getUpdaterData :: LauncherOptions -> UpdaterData
getUpdaterData lo =
    let path            = loUpdaterPath lo
        args            = loUpdaterArgs lo
        windowsRunner   = loUpdateWindowsRunner lo
        archivePath     = fromMaybe "" (loUpdateArchive lo)
    in UpdaterData path args windowsRunner archivePath

-- I think it'll be easier if we introduce sum type that will put together all
-- the datas that are need to launch wallet-frontend..
-- Something like this:
--data NodeData = NodeData
-- { ndPath    :: !FilePath
-- , ndArgs    :: ![Text]
-- , ndLogPath :: Maybe FilePath }

-- | Return WalletArguments
getWargs :: LauncherOptions -> WalletArguments
getWargs lo = WalletArguments $ loWalletArgs lo

-- | Return WalletPath
getWPath :: LauncherOptions -> WalletPath
getWPath lo = WalletPath $ toS $ loWalletPath lo

-- | Set working directory to given @FilePath@, return false if directory does
-- not exist
setWorkingDirectory :: FilePath -> IO Bool
setWorkingDirectory filePath = do
    directoryExists <- doesDirectoryExist filePath
    when directoryExists $ setCurrentDirectory filePath
    return directoryExists
