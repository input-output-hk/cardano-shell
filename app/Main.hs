{-# LANGUAGE RecordWildCards #-}

module Main (main) where

import           Cardano.Prelude

import           Cardano.Shell.Features.Logging (LoggingCLIArguments,
                                                 LoggingLayer (..),
                                                 createLoggingFeature,
                                                 loggingParser)
import           Cardano.Shell.Features.Networking (createNetworkingFeature)

import           Cardano.Shell.Constants.Types (CardanoConfiguration (..),
                                                Core (..))
import           Cardano.Shell.Constants.CLI (configCoreCLIParser)
import           Cardano.Shell.Lib
import           Cardano.Shell.Presets (mainnetConfiguration)
import           Cardano.Shell.Types

import           Options.Applicative


-- | The product type of all command line arguments.
-- All here being - from all the features.
data CLIArguments = CLIArguments !LoggingCLIArguments !Core

main :: IO ()
main = do

    -- General
    cardanoConfiguration            <-  pure mainnetConfiguration
    cardanoEnvironment              <-  initializeCardanoEnvironment

    -- We check that the application is not already running.
    -- _ <- checkIfApplicationIsRunning cardanoConfiguration

    -- And example of an application that goes haywire.
    let application :: LoggingLayer -> IO ()
        application loggingLayer = do

            let logTrace   = llBasicTrace loggingLayer
            let logNotice  = llLogNotice  loggingLayer
            let appendName = llAppendName loggingLayer

            logNotice logTrace "Hello from logging layer ..."
            let logTrace' = appendName "cardano-shell" logTrace
            logNotice logTrace' "Hello #2 from logging layer ..."

            _ <- replicateM 5 (threadDelay 1000000 >> putTextLn "Running node/wallet/whatever!")
            _ <- throwIO UnknownFailureException
            _ <- replicateM 5 (threadDelay 1000000 >> putTextLn "Running node/wallet/whatever!")

            pure ()

    let cardanoApplication :: LoggingLayer -> CardanoApplication
        cardanoApplication = CardanoApplication . application

    -- Here we initialize all the features.
    (cardanoFeatures, loggingLayer) <- initializeAllFeatures cardanoConfiguration cardanoEnvironment

    -- Here we run them.
    runCardanoApplicationWithFeatures Development cardanoFeatures $ cardanoApplication loggingLayer

--------------------------------------------------------------------------------
-- Feature initialization
--------------------------------------------------------------------------------

-- Let's presume that we have the order of the features like this:
-- 1. logging
-- 2. networking
-- 3. blockchain
-- 4. ledger
-- 5. wallet?

-- The important bit here is that @LoggingLayer@ and @LoggingCardanoFeature@ don't know anything
-- about networking, the same way that @NetworkLayer@ and @NetworkingCardanoFeature@ doesn't know
-- anything about blockchain, and so on.
-- The same can be said about the configuration.
-- In summary, the two things that the team implementing these should know is it's configuration and it's
-- result, which is a layer (a list of functions that we provide via the record function interface).
-- So they live in separate modules, contain only what they need and are private. Their implementation can be changed
-- anytime.
-- Another interesting thing is that we stack the effects ONLY when we use a function from
-- another layer, and we don't get all the effects, just the ones the function contains.
initializeAllFeatures :: CardanoConfiguration -> CardanoEnvironment -> IO ([CardanoFeature], LoggingLayer)
initializeAllFeatures cardanoConfiguration cardanoEnvironment = do

    -- Here we parse the __CLI__ arguments for the actual application.
    CLIArguments loggingCLIArguments coreConfig <- execParser parserWithInfo

    -- TODO(KS): Looks like we might need to include lenses at some point?
    let cardanoConfiguration' = cardanoConfiguration { ccCore = ccCore cardanoConfiguration <> pure coreConfig }

    -- Here we initialize all the features
    (loggingLayer, loggingFeature)  <- createLoggingFeature cardanoEnvironment cardanoConfiguration' loggingCLIArguments

    (_           , networkFeature)  <- createNetworkingFeature loggingLayer cardanoEnvironment cardanoConfiguration'

    -- Here we return all the features.
    let allCardanoFeatures :: [CardanoFeature]
        allCardanoFeatures =
            [ loggingFeature
            , networkFeature
            ]

    pure (allCardanoFeatures, loggingLayer)
  where
    -- | Top level parser with info.
    parserWithInfo :: ParserInfo CLIArguments
    parserWithInfo = info (commandLineParser <**> helper)
        (  fullDesc
        <> progDesc "Logging Feature"
        <> header "cardano-shell: logging feature"
        )

    -- | The product parser for all the CLI arguments.
    commandLineParser :: Parser CLIArguments
    commandLineParser = CLIArguments
        <$> loggingParser
        <*> configCoreCLIParser
