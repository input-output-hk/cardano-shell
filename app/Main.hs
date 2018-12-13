module Main (main) where

import           Cardano.Prelude

import           Cardano.Shell.Features.Logging (createLoggingFeature)
import           Cardano.Shell.Features.Networking (createNetworkingFeature)

import           Cardano.Shell.Lib
import           Cardano.Shell.Types

main :: IO ()
main = do

    -- General
    cardanoConfiguration            <-  loadCardanoConfiguration
    cardanoEnvironment              <-  initializeCardanoEnvironment

    -- And example of an application that goes haywire.
    let application :: IO ()
        application = do
            _ <- replicateM 5 (threadDelay 1000000 >> putTextLn "Running node/wallet/whatever!")
            _ <- throwIO UnknownFailureException
            _ <- replicateM 5 (threadDelay 1000000 >> putTextLn "Running node/wallet/whatever!")
            pure ()

    let cardanoApplication :: CardanoApplication
        cardanoApplication = CardanoApplication application

    -- Here we initialize all the features.
    cardanoFeatures <- initializeAllFeatures cardanoConfiguration cardanoEnvironment

    -- Here we run them.
    runCardanoApplicationWithFeatures Development cardanoFeatures cardanoApplication

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

