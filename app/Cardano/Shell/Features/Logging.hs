{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE Rank2Types        #-}

module Cardano.Shell.Features.Logging
    ( LoggingLayer (..)
    , createLoggingFeature
    , Trace
    ) where

import           Cardano.Prelude hiding (trace)

import           Cardano.BM.Configuration.Static (defaultConfigStdout)
import           Cardano.BM.Setup (setupTrace)
import           Cardano.BM.Trace (Trace)
import qualified Cardano.BM.Trace as Trace

import           Cardano.Shell.Types (NoDependency (..), CardanoConfiguration (..), CardanoEnvironment, CardanoFeature (..), CardanoFeatureInit (..))

--------------------------------------------------------------------------------
-- Loggging feature
--------------------------------------------------------------------------------

--------------------------------
-- Configuration
--------------------------------

data LoggingParameters = LoggingParameters
    { configFp :: FilePath
    , prefixFp :: FilePath
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
    { llStartTrace :: forall m. (MonadIO m) => Trace m
    , llLogDebug   :: forall m. (MonadIO m) => Trace m -> Text -> m ()
    , llLogInfo    :: forall m. (MonadIO m) => Trace m -> Text -> m ()
    , llLogNotice  :: forall m. (MonadIO m) => Trace m -> Text -> m ()
    , llLogWarning :: forall m. (MonadIO m) => Trace m -> Text -> m ()
    , llLogError   :: forall m. (MonadIO m) => Trace m -> Text -> m ()
    , llAppendName :: forall m. (MonadIO m) => Text -> Trace m -> m (Trace m)
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
    loggingConfiguration    <-  pure $ LoggingParameters
                                    (ccLogConfig cardanoConfiguration)
                                    (ccLogPath cardanoConfiguration)

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
    initLogging _ _ _ _logparams = do
        cfg <- defaultConfigStdout  -- TODO initialize from 'configFp logparams'
        baseTrace <- setupTrace (Right cfg) "simple"
        pure $ LoggingLayer
                { llStartTrace  = Trace.natTrace liftIO baseTrace
                , llLogDebug    = Trace.logDebug
                , llLogInfo     = Trace.logInfo
                , llLogNotice   = Trace.logNotice
                , llLogWarning  = Trace.logWarning
                , llLogError    = Trace.logError
                , llAppendName  = Trace.appendName
                }
    cleanupLogging :: LoggingLayer -> IO ()
    cleanupLogging _ = pure ()  -- TODO

loggingCardanoFeature :: LoggingCardanoFeature -> LoggingLayer -> CardanoFeature
loggingCardanoFeature loggingCardanoFeature' loggingLayer = CardanoFeature
    { featureName       = featureType loggingCardanoFeature'
    , featureStart      = liftIO $ do
        void $ pure loggingLayer
    , featureShutdown   = liftIO $ do
        (featureCleanup loggingCardanoFeature') loggingLayer
    }
