{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE Rank2Types    #-}

module Cardano.Shell.Features.Logging
    ( createLoggingFeature
    , LoggingLayer (..)
    )
where

import           Cardano.Prelude hiding (trace)

import           Cardano.BM.Configuration.Static (defaultConfigStdout)
import           Cardano.BM.Setup (setupTrace)
import           Cardano.BM.Trace (Trace)
import qualified Cardano.BM.Trace as Trace

import           Control.Exception.Safe (MonadThrow)

import           Cardano.Shell.Types (CardanoConfiguration, CardanoEnvironment,
                                      CardanoFeature (..),
                                      CardanoFeatureInit (..),
                                      NoDependency (..))

--------------------------------------------------------------------------------
-- Loggging feature
--------------------------------------------------------------------------------

--------------------------------
-- Configuration
--------------------------------

data LoggingParameters = LoggingParameters
    { configFp :: Text
    } deriving (Show, Eq)

--------------------------------
-- Layer
--------------------------------

-- | The LoggingLayer interface that we can expose.
-- We want to do this since we want to be able to mock out any function tied to logging.
--
-- The good side of this is that _each function has it's own effects_ and that is ideal for tracking
-- the functions effects and constraining the user (programmer) of those function to use specific effects in them.
-- https://github.com/input-output-hk/cardano-sl/blob/develop/util/src/Pos/Util/Log/LogSafe.hs
data LoggingLayer = LoggingLayer
    { startTrace  :: forall m. (MonadIO m) => Trace m
    , logDebug    :: forall m. (MonadIO m) => Trace m -> Text -> m ()
    , logInfo     :: forall m. (MonadIO m) => Trace m -> Text -> m ()
    , logNotice   :: forall m. (MonadIO m) => Trace m -> Text -> m ()
    , logWarning  :: forall m. (MonadIO m) => Trace m -> Text -> m ()
    , logError    :: forall m. (MonadIO m) => Trace m -> Text -> m ()
    , appendName  :: forall m. (MonadIO m) => Text -> Trace m -> m (Trace m)
    , mockNonIO   :: forall m. (MonadThrow m) => m ()
    }

--------------------------------
-- Feature
--------------------------------

type LoggingCardanoFeature = CardanoFeatureInit NoDependency LoggingParameters LoggingLayer

createLoggingFeature :: CardanoEnvironment -> CardanoConfiguration -> IO (LoggingLayer, CardanoFeature)
createLoggingFeature cardanoEnvironment cardanoConfiguration = do
    -- we parse any additional configuration if there is any
    -- We don't know where the user wants to fetch the additional configuration from, it could be from
    -- the filesystem, so we give him the most flexible/powerful context, @IO@.
    loggingConfiguration    <-  pure $ LoggingParameters "./config/logging.yaml"

    -- we construct the layer
    loggingLayer            <- (featureInit loggingCardanoFeatureInit)
                               cardanoEnvironment
                               NoDependency
                               cardanoConfiguration
                               loggingConfiguration

    -- we construct the cardano feature
    let cardanoFeature      = loggingCardanoFeature loggingCardanoFeatureInit loggingLayer

    -- we return both
    pure (loggingLayer, cardanoFeature)

loggingCardanoFeatureInit :: LoggingCardanoFeature
loggingCardanoFeatureInit = CardanoFeatureInit
    { featureType    = "LoggingMonitoringFeature"
    , featureInit    = initLogging
    , featureCleanup = cleanupLogging
    }
  where
    initLogging :: CardanoEnvironment -> NoDependency -> CardanoConfiguration -> LoggingParameters -> IO LoggingLayer
    initLogging _ _ _ _ = do
        cfg <- defaultConfigStdout
        (ctx, baseTrace) <- setupTrace (Right cfg) "simple"
        pure $ LoggingLayer
                { startTrace  = (ctx, Trace.natTrace liftIO baseTrace)
                , logDebug    = Trace.logDebug
                , logInfo     = Trace.logInfo
                , logNotice   = Trace.logNotice
                , logWarning  = Trace.logWarning
                , logError    = Trace.logError
                , appendName  = Trace.appendName
                , mockNonIO   = pure ()
                }
    cleanupLogging :: LoggingLayer -> IO ()
    cleanupLogging _ = pure ()

loggingCardanoFeature :: LoggingCardanoFeature -> LoggingLayer -> CardanoFeature
loggingCardanoFeature loggingCardanoFeature' loggingLayer = CardanoFeature
    { featureName       = featureType loggingCardanoFeature'
    , featureStart      = liftIO $ do
        --putTextLn "Starting up loggingCardanoFeature!"
        void $ pure loggingLayer -- or whatever it means for YOU (a specific team)
    , featureShutdown   = liftIO $ do
        --putTextLn "Shutting down loggingCardanoFeature!"
        (featureCleanup loggingCardanoFeature') loggingLayer
    }
