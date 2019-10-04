{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE MultiParamTypeClasses      #-}

module Cardano.Shell.Launcher
    ( WalletMode (..)
    , WalletRunner (..)
    , walletRunnerProcess
    , LoggingDependencies (..)
    -- * Functions
    , runWalletProcess
    -- * Critical exports (testing)
    , DaedalusExitCode (..)
    , handleDaedalusExitCode
    , UpdateRunner (..)
    , RestartRunner (..)
    -- * Typeclass
    , Isomorphism (..)
    ) where

import           Cardano.Prelude

import           Prelude (Show (..))
import qualified System.Process as Process
import           Turtle (system)

import           Cardano.Shell.Configuration (WalletArguments (..),
                                              WalletPath (..))
import           Cardano.Shell.Types (LoggingDependencies (..))
import           Cardano.Shell.Update.Lib (UpdaterData (..),
                                           runDefaultUpdateProcess, runUpdater)

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

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
handleDaedalusExitCode runUpdater' restartWallet = isoTo <<$>> \case
    RunUpdate               -> runUpdate runUpdater' >> runRestart restartWallet WalletModeNormal
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
    :: LoggingDependencies
    -> WalletMode
    -> WalletPath
    -> WalletArguments
    -> WalletRunner
    -> UpdaterData
    -> IO ExitCode
runWalletProcess logDep walletMode walletPath walletArguments walletRunner updaterData = do

    -- Parametrized by @WalletMode@ so we can change it on restart depending
    -- on the Daedalus exit code.
    let restart :: WalletMode -> IO ExitCode
        restart =  \walletMode' -> runWalletProcess
                        logDep
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

    logNotice logDep $ "Starting the wallet"

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
        (UpdateRunner $ runUpdater runDefaultUpdateProcess logDep updaterData)
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
