{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Cardano.Shell.Lib
    ( ApplicationEnvironment (..)
    , GeneralException (..)
    , CardanoApplication (..)
    , runCardanoApplicationWithFeatures
    , runApplication
    -- * configuration for running
    , AllFeaturesInitFunction
    , initializeCardanoEnvironment
    , checkIfApplicationIsRunning
    ) where

import           Cardano.Prelude hiding (async, cancel, (%))
import           Prelude (Show (..))

import           Control.Exception.Safe (throwM)

import           Control.Concurrent.Classy hiding (catch)
import           Control.Concurrent.Classy.Async (async, cancel)

import           GHC.IO.Handle.Lock (LockMode (..), hTryLock)

import           Formatting (bprint, build, formatToString, stext, (%))
import           Formatting.Buildable (Buildable (..))

import           System.Directory (doesFileExist)

import           Cardano.Shell.Types (ApplicationEnvironment (..),
                                      CardanoApplication (..),
                                      CardanoEnvironment, CardanoFeature (..),
                                      applicationProductionMode,
                                      initializeCardanoEnvironment)

import           Cardano.Shell.Constants.Types (CardanoConfiguration (..))

import           Cardano.Shell.Presets (mainnetConfiguration)

--------------------------------------------------------------------------------
-- General exceptions
--------------------------------------------------------------------------------

data GeneralException
    = UnknownFailureException -- the "catch-all"
    | FileNotFoundException FilePath
    | ApplicationAlreadyRunningException
    | LockFileDoesNotExist FilePath
    deriving (Eq)

instance Exception GeneralException

instance Buildable GeneralException where
    build UnknownFailureException               = bprint ("Something went wrong and we don't know what.")
    build (FileNotFoundException filePath)      = bprint ("File not found on path '"%stext%"'.") (strConv Lenient filePath)
    build ApplicationAlreadyRunningException    = bprint "Application is already running. Please shut down the application first."
    build (LockFileDoesNotExist filePath)       = bprint ("Lock file not found on path '"%stext%"'.") (strConv Lenient filePath)

-- | Instance so we can see helpful error messages when something goes wrong.
instance Show GeneralException where
    show = formatToString Formatting.build

--------------------------------------------------------------------------------
-- Feature initialization
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
checkIfApplicationIsRunning :: CardanoConfiguration -> IO ()
checkIfApplicationIsRunning cardanoConfiguration = do

    -- Load the path for the lock file from the configuration.
    let lockFilePath    =  ccApplicationLockFile cardanoConfiguration

    -- If the lock file doesn't exist, throw an exception.
    -- We want to differentiate between different exceptional situations.
    whenM (not <$> doesFileExist lockFilePath) $ do
        throwM $ LockFileDoesNotExist lockFilePath

    lockfileHandle      <- openFile lockFilePath ReadMode
    isAlreadyRunning    <- hTryLock lockfileHandle ExclusiveLock

    -- We need to inform the user if the application version is already running.
    when (not isAlreadyRunning) $
        throwM ApplicationAlreadyRunningException

    -- Otherwise, all is good.
    pure ()

-- Here we run all the features.
-- A general pattern. The dependency is always in a new thread, and we depend on it,
-- so when that dependency gets shut down all the other features that depend on it get
-- shut down as well.
runCardanoApplicationWithFeatures
    :: forall m. (MonadIO m, MonadConc m)
    => ApplicationEnvironment
    -> [CardanoFeature]
    -> CardanoApplication
    -> m ()
runCardanoApplicationWithFeatures applicationEnvironment cardanoFeatures cardanoApplication = do

    -- We start all the new features.
    asyncCardanoFeatures <- mapM (async . featureStart) cardanoFeatures

    -- Here we run the actual application.
    -- We presume that the control-flow is now in the hands of that function.
    -- An example of top-level-last-resort-error-handling-strategy.
    liftIO $ catchAny (runCardanoApplication cardanoApplication) $ \_ -> do
        --putTextLn "Exception occured!"
        pure ()

    -- When we reach this point, we cancel all the features.
    _ <- mapM cancel (reverse asyncCardanoFeatures)

    -- Then we cleanup all the features if we need to do so.
    _ <- mapM featureShutdown (reverse cardanoFeatures)

    -- And we are done! Or are we? A simple idea is to restart the application if it's
    -- in production.
    when (applicationProductionMode applicationEnvironment) $
       runCardanoApplicationWithFeatures applicationEnvironment cardanoFeatures cardanoApplication

  where
    -- | Util function. Yes, yes, we can import this.
    catchAny :: IO a -> (SomeException -> IO a) -> IO a
    catchAny = catch

type AllFeaturesInitFunction = CardanoConfiguration -> CardanoEnvironment -> IO [CardanoFeature]


-- | The wrapper for the application providing modules.
runApplication :: forall m. (MonadIO m, MonadConc m) => AllFeaturesInitFunction -> IO () -> m ()
runApplication initializeAllFeatures application = do

    -- General
    cardanoConfiguration            <-  liftIO $ pure mainnetConfiguration
    cardanoEnvironment              <-  liftIO initializeCardanoEnvironment

    let cardanoApplication :: CardanoApplication
        cardanoApplication = CardanoApplication application

    -- Here we initialize all the features.
    cardanoFeatures <- liftIO $ initializeAllFeatures cardanoConfiguration cardanoEnvironment

    -- Here we run them.
    runCardanoApplicationWithFeatures Development cardanoFeatures cardanoApplication
