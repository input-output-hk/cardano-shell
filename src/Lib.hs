{-# LANGUAGE ScopedTypeVariables #-}

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

-- forkFinally :: IO a -> (Either SomeException a -> IO ()) -> IO ThreadId
forkFinallyRaise :: IO a -> (a -> IO ()) -> IO ThreadId
forkFinallyRaise action f = forkFinally action $ \(value :: Either SomeException a)-> do

    result <- either (\_ -> E.throwIO UnknownFailureException) pure value

    f result


withThreadUsing :: forall a b. IO a -> ((ThreadId, Either SomeException a) -> IO b) -> IO b
withThreadUsing = \action inner -> do
  var <- newEmptyMVar

  mask $ \restore -> do
    -- In another thread
    threadId    <- forkIO $ try (restore action) >>= putMVar var
    var         <- readMVar var

    let a :: (ThreadId, Either SomeException a)
        a = (threadId, var)

    r       <- restore (inner a) `catchAll` \e -> do
      uninterruptibleCancel a
      throwIO e

    uninterruptibleCancel a
    return r

  where
    catchAll :: forall a b. IO a -> (SomeException -> IO a) -> IO a
    catchAll = catch

    uninterruptibleCancel :: forall a. (ThreadId, Either SomeException a) -> IO ()
    uninterruptibleCancel = uninterruptibleMask_ . cancel

    cancel :: forall a. (ThreadId, Either SomeException a) -> IO ()
    cancel (t, _) = throwTo t FeatureCancelled



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

    _ <- forkFinallyRaise noDependency $ \(loggingDependency :: NoDependency) -> do

        let loggingLayerIO = (featureStart loggingCardanoFeature)
                                cardanoEnvironment
                                loggingDependency
                                cardanoConfiguration
                                loggingConfiguration

        putTextLn "Starting up logging layer!"
        loggingThreadId <- forkFinallyRaise loggingLayerIO $ \loggingLayer -> do

            let networkLayerIO =    (featureStart networkingCardanoFeature)
                                        cardanoEnvironment
                                        loggingLayer
                                        cardanoConfiguration
                                        networkingConfiguration

            putTextLn "Starting up networking layer!"
            _ <- forkFinallyRaise networkLayerIO $ \networkLayer -> do

                -- something that depends on network layer!
                --_ <- forever $ threadDelay 1000000 >> (putTextLn "Running node/wallet/whatever!")

                --let application :: IO ()
                --    application = replicateM 5 (threadDelay 1000000 >> putTextLn "Running node/wallet/whatever!") >> cancel networkLayer

                let application :: IO ()
                    application = replicateM 5 (threadDelay 1000000 >> putTextLn "Running node/wallet/whatever!") >> throwIO UnknownFailureException

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
    -- wait for sync
    threadDelay 10000000

  where
    -- | Util function. Yes, yes, we can import this.
    catchAny :: IO a -> (SomeException -> IO a) -> IO a
    catchAny = catch





