{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE DeriveGeneric #-}

module Features.Logging where

import Cardano.Prelude

import Control.Exception.Safe

import Types


--------------------------------------------------------------------------------
-- Loggging feature
--------------------------------------------------------------------------------

--------------------------------
-- Exceptions
--------------------------------

data LoggingException
    = MissingLogFileException
    -- | ...
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

-- | The LogginLayer interface that we can expose.
-- We want to do this since we want to be able to mock out any function tied to logging.
--
-- The good side of this is that _each function has it's own effects_ and that is ideal for tracking
-- the functions effects and constraining the user (programmer) of those function to use specific effects in them.
-- https://github.com/input-output-hk/cardano-sl/blob/develop/util/src/Pos/Util/Log/LogSafe.hs
data LoggingLayer = LoggingLayer
    { iolLogDebug   :: forall m. (MonadIO m) => Text -> m ()
    , iolLogInfo    :: forall m. (MonadIO m) => Text -> m ()
    , iolNonIo      :: forall m. (MonadThrow m) => m ()
    }

testLoggingLayer :: LoggingLayer
testLoggingLayer = LoggingLayer
    { iolLogDebug               = liftIO . putTextLn
    , iolLogInfo                = liftIO . putTextLn
    , iolNonIo                  = pure ()
    }

--------------------------------
-- Feature
--------------------------------

type LoggingCardanoFeature = CardanoFeature NoDependency RotationParameters LoggingLayer

loggingCardanoFeature :: LoggingCardanoFeature
loggingCardanoFeature = CardanoFeature
    { featureType                   = LoggingMonitoringFeature
    , featureParseConfiguration     = pure testRotationParameters
    , featureStart                  = featureStart'
    , featureCleanup                = featureCleanup'
    }
  where
    featureStart' :: CardanoEnvironment -> NoDependency -> CardanoConfiguration -> RotationParameters -> IO LoggingLayer
    featureStart' = actualLoggingFeature

    featureCleanup' :: LoggingLayer -> IO ()
    featureCleanup' _ = putTextLn "Shutting down logging feature!" -- save a file, for example

actualLoggingFeature :: CardanoEnvironment -> NoDependency -> CardanoConfiguration -> RotationParameters -> IO LoggingLayer
actualLoggingFeature _ _ _ _ = pure testLoggingLayer

