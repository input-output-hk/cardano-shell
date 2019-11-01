module Cardano.Shell.Application
    ( checkIfApplicationIsRunning
    ) where

import           Cardano.Prelude
import           Prelude (Show (..))

import           Control.Exception.Safe (throwM)

import           GHC.IO.Handle.Lock (LockMode (..), hTryLock)

import           System.Directory (doesFileExist)

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

data ApplicationError
    = ApplicationAlreadyRunningException
    deriving (Eq)

instance Exception ApplicationError

instance Show ApplicationError where
    show ApplicationAlreadyRunningException = "Daedalus application is already running. \
        \There cannot be two applications running at the same time. Please close one \
        \application before starting another instance."

--------------------------------------------------------------------------------
-- Functions
--------------------------------------------------------------------------------

-- | Use the GHC.IO.Handle.Lock API. It needs an application lock file,
-- but the lock is not just that the file exists, it's a proper OS level API
-- that automatically unlocks the file if the process terminates.
-- This is based on the problem that we observe with the existing code
-- that we suspect many of the upgrade problems are due to the old version still running.
-- The point here would be to make that diagnosis clear and reliable, to help reduce user confusion.
-- For example, somebody has two installations, one in /home/user/cardano-sl-2.0 and
-- the other in /home/user/cardano-sl-1.33. Each instance of the program that runs knows
-- which dir is its app state dir, and it uses the lock file in that dir.
-- So, in this case, there will be two lock files, and you can run both
-- versions concurrently, but not two instances of the same version.
-- I guess it's better to think about it as the lock file protecting the
-- application state, rather than about preventing multiple instances of
-- the application from running.
-- Another example, somebody has two installations,
-- one in /home/user/cardano-sl-2.0-installation-1 and one
-- in /home/user/cardano-sl-2.0-installation-2. Perhaps ports will still conflict.
-- But it catches the primary issue with upgrades, where we don't change the state dir.
-- This fits in as one of the modular features in the framework, that we provide as optional
-- bundled features. It does a check on initialization (and can fail synchronously),
-- it can find the app state dir by config, or from the server environment. It can release
-- the lock file on shutdown (ok, that's actually automatic, but it fits
-- into the framework as a nice example).
checkIfApplicationIsRunning :: FilePath -> IO ()
checkIfApplicationIsRunning lockFilePath = do

    fileExist <- doesFileExist lockFilePath

    -- If it doesn't exist, create it?
    -- We might add some checks for permissions?
    when (not fileExist) $
        writeFile lockFilePath ""

    lockfileHandle      <- openFile lockFilePath ReadMode
    isAlreadyRunning    <- hTryLock lockfileHandle ExclusiveLock

    -- We need to inform the user if the application version is already running.
    when (not isAlreadyRunning) $
        throwM ApplicationAlreadyRunningException

    -- Otherwise, all is good.
    return ()
