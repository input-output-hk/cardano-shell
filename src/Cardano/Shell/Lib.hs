{-# LANGUAGE ScopedTypeVariables #-}

module Cardano.Shell.Lib
    ( ApplicationEnvironment (..)
    , GeneralException (..)
    , CardanoApplication (..)
    , runCardanoApplicationWithFeatures
    , runApplication
    -- * configuration for running
    , AllFeaturesInitFunction
    , loadCardanoConfiguration
    , initializeCardanoEnvironment
    ) where

import           Cardano.Prelude hiding (async, cancel)

import           Control.Concurrent.Classy hiding (catch)
import           Control.Concurrent.Classy.Async (async, cancel)

import           Cardano.Shell.Types (ApplicationEnvironment (..),
                                      CardanoApplication (..),
                                      CardanoConfiguration, CardanoEnvironment,
                                      CardanoFeature (..),
                                      applicationProductionMode,
                                      initializeCardanoEnvironment,
                                      loadCardanoConfiguration)

--------------------------------------------------------------------------------
-- General exceptions
--------------------------------------------------------------------------------

data GeneralException
    = UnknownFailureException -- the "catch-all"
    | MissingResourceException
    | FileNotFoundException
    deriving (Eq, Show)

instance Exception GeneralException


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
    cardanoConfiguration            <-  liftIO loadCardanoConfiguration
    cardanoEnvironment              <-  liftIO initializeCardanoEnvironment

    let cardanoApplication :: CardanoApplication
        cardanoApplication = CardanoApplication application

    -- Here we initialize all the features.
    cardanoFeatures <- liftIO $ initializeAllFeatures cardanoConfiguration cardanoEnvironment

    -- Here we run them.
    runCardanoApplicationWithFeatures Development cardanoFeatures cardanoApplication


