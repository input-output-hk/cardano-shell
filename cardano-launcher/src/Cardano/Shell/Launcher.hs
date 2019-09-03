{-# LANGUAGE LambdaCase #-}

module Cardano.Shell.Launcher
    ( LauncherConfig (..)
    , WalletArguments (..)
    , WalletPath (..)
    , ExternalDependencies (..)
    -- * Functions
    , runWallet
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

newtype WalletPath = WalletPath
    { getWalletPath         :: Text
    } deriving (Eq, Show)

data ExternalDependencies = ExternalDependencies
    { logInfo   :: Text -> IO ()
    , logError  :: Text -> IO ()
    , logNotice :: Text -> IO ()
    }

-- This is here so we don't mess up the order. It's VERY important.
newtype UpdateRunner = UpdateRunner { runUpdate :: IO ExitCode }

newtype LauncherRunner = LauncherRunner { runLauncher :: IO ExitCode }

--------------------------------------------------------------------------------
-- Functions
--------------------------------------------------------------------------------

-- | All the important exit codes. Since we cover "other" cases as well, this is a total mapping.
-- That is good.
-- TODO(KS): We could extend this to try to encode some interesting properties about it.
data DaedalusExitCodes
    = RunUpdate
    -- ^ Daedalus is ready to run the update system.
    | RestartInGPUSafeMode
    -- ^ Daedalus asks launcher to relaunch Daedalus with GPU safe mode.
    | RestartInGPUNormalMode
    -- ^ Daedalus asks launcher to relaunch Daedalus with normal mode (turn off GPU safe mode).
    | ExitCodeOther Int
    -- ^ Daedalus wants launcher to exit as well. Unexpected exit code.
    | ExitCodeSuccess
    -- ^ Daedalus "happy path" where it could shut down with success.

-- | Here we handle the exit codes.
-- It's a simple mapping from exit code to actions that the launcher takes.
--
-- This is much simpler to test, no?
handleDaedalusExitcode
    :: UpdateRunner
    -> LauncherRunner
    -> DaedalusExitCodes
    -> IO ExitCode
handleDaedalusExitcode runUpdaterFunction restartLauncherFunction = \case
    RunUpdate               -> runUpdate runUpdaterFunction >> runLauncher restartLauncherFunction
    -- ^ Run the actual update, THEN restart launcher.
    RestartInGPUSafeMode    -> runLauncher restartLauncherFunction
    -- ^ Enable safe mode (GPU safe mode). TODO(KS): Feedback from Daedalus?
    RestartInGPUNormalMode  -> runLauncher restartLauncherFunction
    -- ^ Disable safe mode (GPU safe mode).
    ExitCodeOther ef        -> return $ ExitFailure ef
    -- ^ Some other unexpected error popped up.
    ExitCodeSuccess         -> return ExitSuccess
    -- ^ All is well, exit "mucho bien".

-- | Launching the wallet.
-- For now, this is really light since we don't know whether we will reuse the
-- older configuration and if so, which parts of it.
-- We passed in the bare minimum and if we require anything else, we will add it.
runWallet
    :: ExternalDependencies
    -> WalletPath
    -> WalletArguments
    -> UpdaterData
    -> IO ExitCode
runWallet ed walletPath walletArguments updaterData = do
    let restart = runWallet ed walletPath walletArguments updaterData
    (logNotice ed) "Starting the wallet"

    -- create the wallet process
    walletExitStatus <- system (createProc Process.Inherit walletPath walletArguments) mempty

    -- Let us map the interesting commands into a very simple "language".
    let exitCode :: DaedalusExitCodes
        exitCode = case walletExitStatus of
            ExitFailure 20  -> RunUpdate
            ExitFailure 21  -> RestartInGPUSafeMode
            ExitFailure 22  -> RestartInGPUNormalMode

            ExitFailure ef  -> ExitCodeOther ef
            ExitSuccess     -> ExitCodeSuccess

    -- Here we can interpret what that simple "language" means. This allows us to "cut"
    -- through the function and separate it. When we decouple it, we can test parts in isolation.
    -- We separate the description of the computation, from the computation itself.
    -- There are other ways of doing this, of course.
    handleDaedalusExitcode
        (UpdateRunner $ runUpdater updaterData)
        (LauncherRunner restart)
        exitCode
  where
    -- | The creation of the process.
    createProc
        :: Process.StdStream
        -> WalletPath
        -> WalletArguments
        -> Process.CreateProcess
    createProc stdStream (WalletPath commandPath) (WalletArguments commandArguments) =
        (Process.proc (strConv Lenient commandPath) (map (strConv Lenient) commandArguments))
            { Process.std_in    = Process.CreatePipe
            , Process.std_out   = stdStream
            , Process.std_err   = stdStream
            }

