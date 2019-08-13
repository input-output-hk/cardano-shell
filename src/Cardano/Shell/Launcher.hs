module Cardano.Shell.Launcher where

import           Cardano.Prelude
import           Cardano.Shell.Update.Lib (UpdaterData (..), runUpdater)
import qualified System.Process as Process
import           Turtle (system)

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

    case walletExitStatus of
        ExitFailure 20 -> do
            void $ runUpdater updaterData
            restart
        ExitFailure 21 -> do
            (logNotice ed) "The wallet has exited with code 21"
            --logInfo "Switching Configuration to safe mode"
            --saveSafeMode lo True
            restart

        ExitFailure 22 -> do
            (logNotice ed) "The wallet has exited with code 22"
            --logInfo "Switching Configuration to normal mode"
            --saveSafeMode lo False
            restart
        -- Otherwise, return the exit status.
        _ -> pure walletExitStatus
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
