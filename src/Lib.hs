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
    -- | ...
    deriving (Eq, Show)

instance Exception GeneralException

--------------------------------------------------------------------------------
-- Feature initialization
--------------------------------------------------------------------------------

-- https://www.seas.upenn.edu/~cis552/11fa/lectures/concurrency.html
-- https://mazzo.li/posts/threads-resources.html

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
    withAsync (pure NoDependency) $ \loggingDependency -> do

        let loggingLayerIO = (featureStart loggingCardanoFeature)
                                cardanoEnvironment
                                loggingDependency
                                cardanoConfiguration
                                loggingConfiguration

        putTextLn "Starting up logging layer!"
        withAsync loggingLayerIO $ \loggingLayer -> do

            let networkLayerIO =    (featureStart networkingCardanoFeature)
                                        cardanoEnvironment
                                        loggingLayer
                                        cardanoConfiguration
                                        networkingConfiguration

            putTextLn "Starting up networking layer!"
            withAsync networkLayerIO $ \networkLayer -> do

                -- something that depends on network layer!
                --_ <- forever $ threadDelay 1000000 >> (putTextLn "Running node/wallet/whatever!")

                --let application :: IO ()
                --    application = replicateM 5 (threadDelay 1000000 >> putTextLn "Running node/wallet/whatever!") >> cancel networkLayer

                let application :: IO ()
                    application = replicateM 5 (threadDelay 1000000 >> putTextLn "Running node/wallet/whatever!") >> throwIO UnknownFailureException

                -- something we might want to have?
                -- waitCatch?
                catchAny application $ \_ -> putTextLn "Exception occured!" >> cancel networkLayer -- >> restart feature?

                -- wait for finish
                networkLayerResult  <- wait networkLayer

                -- cleanup
                (featureCleanup networkingCardanoFeature) networkLayerResult


            -- wait for finish
            loggingLayerResult  <- wait loggingLayer

            -- cleanup
            (featureCleanup loggingCardanoFeature) loggingLayerResult



        -- wait for finish
        --loggingDependencyResult <- wait loggingDependency
        _ <- wait loggingDependency


        -- some cleanup?
        pure ()

  where
    -- | Util function. Yes, yes, we can import this.
    catchAny :: IO a -> (SomeException -> IO a) -> IO a
    catchAny = catch





