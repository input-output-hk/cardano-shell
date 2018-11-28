module Main where

import           Cardano.Prelude

import           Cardano.Shell.Lib

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


