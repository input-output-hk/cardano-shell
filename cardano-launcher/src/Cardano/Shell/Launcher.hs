{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Cardano.Shell.Launcher
    ( WalletMode (..)
    , LauncherConfig (..)
    , WalletArguments (..)
    , WalletPath (..)
    , ExternalDependencies (..)
    -- * Functions
    , runWalletProcess
    -- * Critical exports (testing)
    , DaedalusExitCode (..)
    , handleDaedalusExitCode
    , UpdateRunner (..)
    , WalletRunner (..)
    -- * Typeclass
    , Isomorphism (..)
    ) where

import           Cardano.Prelude
import           Cardano.Shell.Update.Lib (UpdaterData (..), runUpdater)
import qualified System.Process as Process
import           Turtle (system)

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

newtype WalletArguments = WalletArguments
    { getWalletArguments    :: [Text]
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

-- | This type is responsible for launching and re-launching the wallet
-- inside the launcher process.
newtype WalletRunner = WalletRunner { runWallet :: IO ExitCode }

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
    deriving (Eq, Show)

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

        ExitCodeFailure ef      -> ExitFailure ef
        ExitCodeSuccess         -> ExitSuccess

    isoTo   =   \case
        ExitFailure 20          -> RunUpdate
        ExitFailure 21          -> RestartInGPUSafeMode
        ExitFailure 22          -> RestartInGPUNormalMode

        ExitFailure ef          -> ExitCodeFailure ef
        ExitSuccess             -> ExitCodeSuccess


--------------------------------------------------------------------------------
-- Functions
--------------------------------------------------------------------------------

-- | Here we handle the exit codes.
-- It's a simple mapping from exit code to actions that the launcher takes.
--
-- This is much simpler to test, no?
handleDaedalusExitCode
    :: UpdateRunner
    -> WalletRunner
    -> DaedalusExitCode
    -> IO DaedalusExitCode
handleDaedalusExitCode runUpdaterFunction restartWalletFunction = isoTo <<$>> \case
    RunUpdate               -> runUpdate runUpdaterFunction >> runWallet restartWalletFunction
    -- ^ Run the actual update, THEN restart launcher.
    -- Do we maybe need to handle the update ExitCode as well?
    RestartInGPUSafeMode    -> runWallet restartWalletFunction
    -- ^ Enable safe mode (GPU safe mode).
    RestartInGPUNormalMode  -> runWallet restartWalletFunction
    -- ^ Disable safe mode (GPU safe mode).
    ExitCodeFailure ef      -> return $ ExitFailure ef
    -- ^ Some other unexpected error popped up.
    ExitCodeSuccess         -> return ExitSuccess
    -- ^ All is well, exit "mucho bien".

-- | Wallet runner type.
-- I give you the path to the wallet, it's arguments and you execute it
-- and return me the @ExitCode@.
-- TODO(KS): Replace so we can get more flexibile and testable code?
--newtype WalletRunner = WalletRunner
--    { runWalletSystemProcess :: WalletPath -> WalletArguments -> IO ExitCode
--    }

-- | Launching the wallet.
-- For now, this is really light since we don't know whether we will reuse the
-- older configuration and if so, which parts of it.
-- We passed in the bare minimum and if we require anything else, we will add it.
runWalletProcess
    :: ExternalDependencies
    -> WalletMode
    -> WalletPath
    -> WalletArguments
    -> UpdaterData
    -> IO ExitCode
runWalletProcess ed walletMode walletPath walletArguments updaterData = do

    let restart :: IO ExitCode
        restart = runWalletProcess ed walletMode walletPath walletArguments updaterData

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
    walletExitStatus <- system (createProc Process.Inherit walletPath walletArgs) mempty

    -- Let us map the interesting commands into a very simple "language".
    let exitCode :: DaedalusExitCode
        exitCode = isoTo walletExitStatus

    -- Here we can interpret what that simple "language" means. This allows us to "cut"
    -- through the function and separate it. When we decouple it, we can test parts in isolation.
    -- We separate the description of the computation, from the computation itself.
    -- There are other ways of doing this, of course.
    isoFrom <$> handleDaedalusExitCode
        (UpdateRunner $ runUpdater updaterData)
        (WalletRunner restart)
        exitCode
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

