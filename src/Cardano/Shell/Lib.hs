{-# LANGUAGE ScopedTypeVariables #-}

module Cardano.Shell.Lib
    ( ApplicationEnvironment (..)
    , GeneralException (..)
    , CardanoApplication (..)
    , initializeAllFeatures
    , runCardanoApplicationWithFeatures
    , runApplication
    -- * configuration for running
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

import           Cardano.Shell.Features.Logging (createLoggingFeature)
import           Cardano.Shell.Features.Networking (createNetworkingFeature)

--------------------------------------------------------------------------------
-- General exceptions
--------------------------------------------------------------------------------

data GeneralException
    = UnknownFailureException -- the "catch-all"
    | MissingResourceException
    | FileNotFoundException
    deriving (Eq, Show)

instance Exception GeneralException

--------------------------------------------------------------------------------
-- Feature initialization
--------------------------------------------------------------------------------

-- Let's presume that we have the order of the features like this:
-- 1. logging
-- 2. networking
-- 3. blockchain
-- 4. ledger
-- 5. wallet?

-- The important bit here is that @LogginLayer@ and @LoggingCardanoFeature@ don't know anything
-- about networking, the same way that @NetworkLayer@ and @NetworkingCardanoFeature@ doesn't know
-- anything about blockchain, and so on.
-- The same can be said about the configuration.
-- In summary, the two things that the team implementing these should know is it's configuration and it's
-- result, which is a layer (a list of functions that we provide via the record function interface).
-- So they live in separate modules, contain only what they need and are private. Their implementation can be changed
-- anytime.
-- Another interesting thing is that we stack the effects ONLY when we use a function from
-- another layer, and we don't get all the effects, just the ones the function contains.
initializeAllFeatures :: CardanoConfiguration -> CardanoEnvironment -> IO [CardanoFeature]
initializeAllFeatures cardanoConfiguration cardanoEnvironment = do

    -- Here we initialize all the features
    (loggingLayer, loggingFeature)  <- createLoggingFeature cardanoEnvironment cardanoConfiguration

    (_           , networkFeature)  <- createNetworkingFeature loggingLayer cardanoEnvironment cardanoConfiguration

    -- Here we return all the features.
    let allCardanoFeatures :: [CardanoFeature]
        allCardanoFeatures =
            [ loggingFeature
            , networkFeature
            ]

    pure allCardanoFeatures

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

-- | The wrapper for the application providing modules.
runApplication :: forall m. (MonadIO m, MonadConc m) => IO () -> m ()
runApplication application = do
    -- General
    cardanoConfiguration            <-  liftIO loadCardanoConfiguration
    cardanoEnvironment              <-  liftIO initializeCardanoEnvironment

    let cardanoApplication :: CardanoApplication
        cardanoApplication = CardanoApplication application

    -- Here we initialize all the features.
    cardanoFeatures <- liftIO $ initializeAllFeatures cardanoConfiguration cardanoEnvironment

    -- Here we run them.
    runCardanoApplicationWithFeatures Development cardanoFeatures cardanoApplication


