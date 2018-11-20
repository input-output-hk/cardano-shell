{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Lib where

import Cardano.Prelude

import qualified Control.Exception.Base as E

import Types

import Features.Logging
import Features.Networking

--------------------------------------------------------------------------------
-- General exceptions
--------------------------------------------------------------------------------

data GeneralException
    = UnknownFailureException -- the "catch-all"
    | FeatureCancelled
    | MissingResourceException
    | FileNotFoundException
    -- | ...
    deriving (Eq, Show)

instance Exception GeneralException

--------------------------------------------------------------------------------
-- Feature initialization
--------------------------------------------------------------------------------

-- http://hackage.haskell.org/package/base-4.12.0.0/docs/Control-Exception-Base.html#v:bracket

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

-- | A feature layer with the corresponding feature @ThreadId@.
data Feature a = Feature ThreadId a
    deriving (Eq, Show)

-- | The construction very similar to @Async@ which allows us to cancel specific threads/features.
withFeatureUsing :: forall a b. IO a -> (a -> IO b) -> IO b
withFeatureUsing = \action inner -> do
  var <- newEmptyMVar

  mask $ \restore -> do
    -- In another thread, we don't know the type of exception beforehand.
    threadId    <- forkIO $ try @SomeException (restore action) >>= putMVar var
    var         <- readMVar var

    -- If there is an error when building the feature.
    result      <- either (\_ -> E.throwIO UnknownFailureException) pure var

    let constructedFeature :: Feature a
        constructedFeature = Feature threadId result

    r           <- restore (inner result) `catchAll` \e -> do
      uninterruptibleCancel constructedFeature
      throwIO e

    uninterruptibleCancel constructedFeature
    return r

  where
    catchAll :: forall a b. IO a -> (SomeException -> IO a) -> IO a
    catchAll = catch

    uninterruptibleCancel :: forall a. Feature a -> IO ()
    uninterruptibleCancel = uninterruptibleMask_ . featureCancel

featureCancel :: forall a. Feature a -> IO ()
featureCancel (Feature t _) = throwTo t FeatureCancelled



initializeRunAllFeatures :: IO ()
initializeRunAllFeatures = do
    -- General
    cardanoConfiguration        <-  loadCardanoConfiguration
    cardanoEnvironment          <-  initializeCardanoEnvironment

    -- Logging
    loggingConfiguration        <-  featureParseConfiguration loggingCardanoFeature

    -- Networking
    networkingConfiguration     <-  featureParseConfiguration networkingCardanoFeature



    -- A general pattern. The dependency is always in a new thread, and we depend on it,
    -- so when that dependency gets shut down all the other features that depend on it get
    -- shut down as well.
    -- http://hackage.haskell.org/package/async-2.2.1/docs/Control-Concurrent-Async.html#v:withAsync
    -- http://hackage.haskell.org/package/base-4.12.0.0/docs/Control-Concurrent.html#v:forkFinally
    let noDependency :: IO NoDependency
        noDependency = pure NoDependency

    _ <- withFeatureUsing noDependency $ \loggingDependency -> do

        let loggingLayerIO = (featureStart loggingCardanoFeature)
                                cardanoEnvironment
                                loggingDependency
                                cardanoConfiguration
                                loggingConfiguration

        putTextLn "Starting up logging layer!"
        loggingThreadId <- withFeatureUsing loggingLayerIO $ \loggingLayer -> do

            let networkLayerIO =    (featureStart networkingCardanoFeature)
                                        cardanoEnvironment
                                        loggingLayer
                                        cardanoConfiguration
                                        networkingConfiguration

            putTextLn "Starting up networking layer!"
            _ <- withFeatureUsing networkLayerIO $ \networkLayer -> do

                -- something that depends on network layer!
                --_ <- forever $ threadDelay 1000000 >> (putTextLn "Running node/wallet/whatever!")

                let application :: IO ()
                    application = do
                        _ <- replicateM 5 (threadDelay 1000000 >> putTextLn "Running node/wallet/whatever!")
                        _ <- throwIO UnknownFailureException
                        _ <- replicateM 5 (threadDelay 1000000 >> putTextLn "Running node/wallet/whatever!")
                        pure ()

                --let application :: IO ()
                --    application = replicateM 5 (threadDelay 1000000 >> putTextLn "Running node/wallet/whatever!") >> throwIO UnknownFailureException

                --_ <- application
                -- something we might want to have?
                -- waitCatch?
                catchAny application $ \_ -> putTextLn "Exception occured!"

                -- cleanup
                (featureCleanup networkingCardanoFeature) networkLayer


            -- cleanup
            (featureCleanup loggingCardanoFeature) loggingLayer

        -- some cleanup?
        pure ()

    pure ()

  where
    -- | Util function. Yes, yes, we can import this.
    catchAny :: IO a -> (SomeException -> IO a) -> IO a
    catchAny = catch





