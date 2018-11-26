{-# LANGUAGE ScopedTypeVariables #-}

module Lib where

import Cardano.Prelude

import Types

import Features.Logging
import Features.Networking

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
initializeRunAllFeatures :: IO ()
initializeRunAllFeatures = do
    -- General
    cardanoConfiguration            <-  loadCardanoConfiguration
    cardanoEnvironment              <-  initializeCardanoEnvironment

    (loggingLayer, loggingFeature)  <- createLoggingFeature cardanoEnvironment cardanoConfiguration

    -- networkLayer
    (_           , networkFeature)  <- createNetworkingFeature loggingLayer cardanoEnvironment cardanoConfiguration

    -- A general pattern. The dependency is always in a new thread, and we depend on it,
    -- so when that dependency gets shut down all the other features that depend on it get
    -- shut down as well.
    -- http://hackage.haskell.org/package/async-2.2.1/docs/Control-Concurrent-Async.html#v:withAsync
    -- withAsync :: IO a -> (Async a -> IO b) -> IO b
    _ <- withAsync (featureStart loggingFeature) $ \runningLoggingFeature -> do

        _ <- withAsync (featureStart networkFeature) $ \runningNetworkFeature -> do

            -- ...
            -- More features
            -- ...

            {-
            let application :: IO ()
                application = do
                    _ <- replicateM 5 (threadDelay 1000000 >> putTextLn "Running node/wallet/whatever!")
                    _ <- cancel runningNetworkFeature
                    _ <- replicateM 5 (threadDelay 1000000 >> putTextLn "Running node/wallet/whatever!")
                    pure ()
            _ <- application
            -}

            let application :: IO ()
                application = do
                    _ <- replicateM 5 (threadDelay 1000000 >> putTextLn "Running node/wallet/whatever!")
                    _ <- throwIO UnknownFailureException
                    _ <- replicateM 5 (threadDelay 1000000 >> putTextLn "Running node/wallet/whatever!")
                    pure ()

            -- something we NEED to have!
            catchAny application $ \_ -> putTextLn "Exception occured!" >> cancel runningNetworkFeature -- >> restart feature?

            -- We wait until the feature ends.
            wait runningNetworkFeature

            -- We shutdown the feature.
            featureShutdown networkFeature


        -- We wait until the feature ends.
        wait runningLoggingFeature

        -- We shutdown the feature.
        featureShutdown loggingFeature

    pure ()
  where
    -- | Util function. Yes, yes, we can import this.
    catchAny :: IO a -> (SomeException -> IO a) -> IO a
    catchAny = catch
