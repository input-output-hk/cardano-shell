{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE Rank2Types    #-}

module Cardano.Shell.Features.Logging where

import           Cardano.Prelude

import           Cardano.BM.BaseTrace (natTrace)
import           Cardano.BM.Configuration.Static (defaultConfigStdout)
import           Cardano.BM.Data.SubTrace (SubTrace)
import           Cardano.BM.Setup (setupTrace)
import           Cardano.BM.Trace (Trace, logDebug, logInfo, subTrace)

import           Control.Exception.Safe (MonadThrow)

import           Cardano.Shell.Types (CardanoConfiguration, CardanoEnvironment,
                                      CardanoFeature (..),
                                      CardanoFeatureInit (..),
                                      NoDependency (..))

--------------------------------------------------------------------------------
-- Loggging feature
--------------------------------------------------------------------------------

--------------------------------
-- Exceptions
--------------------------------

data LoggingException
    = MissingLogFileException
    deriving (Eq, Show)

instance Exception LoggingException

--------------------------------
-- Configuration
--------------------------------

-- Ideas picked up from https://github.com/input-output-hk/cardano-sl/blob/develop/util/src/Pos/Util/Log/LoggerConfig.hs

data RotationParameters = RotationParameters
    { _rpLogLimitBytes :: !Word64  -- ^ max size of file in bytes
    , _rpMaxAgeHours   :: !Word    -- ^ hours
    , _rpKeepFilesNum  :: !Word    -- ^ number of files to keep
    } deriving (Generic, Show, Eq)


testRotationParameters :: RotationParameters
testRotationParameters = RotationParameters
    { _rpLogLimitBytes = 10
    , _rpMaxAgeHours   = 3
    , _rpKeepFilesNum  = 5
    }

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
    { iolTrace    :: forall m. (MonadIO m) => Trace m -- How can we change this in runtime? MVar?
    , iolLogDebug :: forall m. (MonadIO m) => Trace m -> Text -> m ()
    , iolLogInfo  :: forall m. (MonadIO m) => Trace m -> Text -> m ()
    , iolSubTrace :: forall m. (MonadIO m) => Text -> Trace m -> m (SubTrace, Trace m)
    , iolNonIo    :: forall m. (MonadThrow m) => m ()
    }

--------------------------------
-- Feature
--------------------------------

type LoggingCardanoFeature = CardanoFeatureInit NoDependency RotationParameters LoggingLayer

createLoggingFeature :: CardanoEnvironment -> CardanoConfiguration -> IO (LoggingLayer, CardanoFeature)
createLoggingFeature cardanoEnvironment cardanoConfiguration = do
    -- we parse any additional configuration if there is any
    -- We don't know where the user wants to fetch the additional configuration from, it could be from
    -- the filesystem, so we give him the most flexible/powerful context, @IO@.
    loggingConfiguration    <-  pure testRotationParameters

    -- we construct the layer
    loggingLayer            <- (featureInit loggingCardanoFeatureInit) cardanoEnvironment NoDependency cardanoConfiguration loggingConfiguration

    -- we construct the cardano feature
    let cardanoFeature      = loggingCardanoFeature loggingCardanoFeatureInit loggingLayer

    -- we return both
    pure (loggingLayer, cardanoFeature)

loggingCardanoFeatureInit :: LoggingCardanoFeature
loggingCardanoFeatureInit = CardanoFeatureInit
    { featureType                   = "LoggingMonitoringFeature"
    , featureInit                   = featureInit'
    , featureCleanup                = featureCleanup'
    }
  where
    featureInit' :: CardanoEnvironment -> NoDependency -> CardanoConfiguration -> RotationParameters -> IO LoggingLayer
    featureInit' = actualLoggingFeature
      where
        actualLoggingFeature :: CardanoEnvironment -> NoDependency -> CardanoConfiguration -> RotationParameters -> IO LoggingLayer
        actualLoggingFeature _ _ _ _ = do
            cfg <- defaultConfigStdout
            (ctx, baseTrace) <- setupTrace (Right cfg) "simple"
            pure $ LoggingLayer
                    { iolTrace    = (ctx, natTrace liftIO baseTrace)
                    , iolLogDebug = logDebug
                    , iolLogInfo  = logInfo
                    , iolSubTrace = subTrace
                    , iolNonIo    = pure ()
                    }

    featureCleanup' :: LoggingLayer -> IO ()
    featureCleanup' _ = pure () --putTextLn "Shutting down logging feature!" -- save a file, for example

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
