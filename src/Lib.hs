{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Lib where

import Cardano.Prelude

--import Control.Exception
import Data.Aeson.Types
import qualified Katip as Katip
import qualified System.Metrics as Ekg

-- | Cardano configuration
data CardanoConfiguration = CardanoConfiguration
    { scfgLogPath   :: !FilePath
    , scfgDBPath    :: !FilePath
    , scfgSomeParam :: !Int
    }

-- | The common runtime environment for all features in the server.
-- All features have access to this environment.
data CardanoEnvironment = CardanoEnvironment
    { serverLogEnv      :: Katip.LogEnv
    , serverEkgStore    :: Ekg.Store
     -- ...
    }

-- | The feature types we can have in the project.
data FeatureType
    = LoggingMonitoringFeature
    | NetworkingFeature
    | BlockchainFeature
    | LedgerFeature
    | WalletFeature
    deriving (Eq, Show)

-- | The option to not have any additional dependency for the @CardanoFeature@.
data NoDependency = NoDependency
    deriving (Eq, Show)

-- | The option to not have any additional configuration for the @CardanoFeature@.
data NoConfiguration = NoConfiguration
    deriving (Eq, Show)

-- | Cardano feature initialization.
-- We are saying "you have the responsibility to make sure you use the right context!".
data CardanoFeature dependency configuration layer = CardanoFeature
    { featureType                   :: !FeatureType
    -- ^ The type of the feature that we use.
    , featureParseConfiguration     :: IO configuration
    -- ^ We don't know where the user wants to fetch the additional configuration from, it could be from
    -- the filesystem, so we give him the most flexible/powerful context, @IO@.
    , featureStart                  :: CardanoEnvironment -> dependency -> CardanoConfiguration -> configuration -> layer
    -- ^ Again, we are not sure how is the user going to run the actual feature,
    -- so we provide him with the most flexible/powerful context we have, @IO@.
    -- Notice the arrangement of the parameters - specific, general, specific, general, result.
    , featureCleanup                :: layer -> IO ()
    -- ^ If the user wants to clean up the resources after the module has completed running,
    -- there is an option to do so.
    }

--------------------------------------------------------------------------------
-- Loggging feature
--------------------------------------------------------------------------------


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
-- The bad side of this is that we unfiy _all functions on m_, which is not a good idea.
-- https://github.com/input-output-hk/cardano-sl/blob/develop/util/src/Pos/Util/Log/LogSafe.hs
data LoggingLayer m = LoggingLayer
    { iolLogDebug   :: Text     -> m ()
    , iolLogInfo    :: Text     -> m ()
    }

loggingLayer :: (MonadIO m) => LoggingLayer m
loggingLayer = LoggingLayer
    { iolLogDebug               = liftIO . putTextLn
    , iolLogInfo                = liftIO . putTextLn
    }

--------------------------------
-- Feature
--------------------------------

type LoggingCardanoFeature m = CardanoFeature NoDependency RotationParameters (LoggingLayer m)

loggingCardanoFeature :: forall m. (MonadIO m) => LoggingCardanoFeature m
loggingCardanoFeature = CardanoFeature
    { featureType                   = LoggingMonitoringFeature
    , featureParseConfiguration     = pure testRotationParameters
    , featureStart                  = featureStart'
    , featureCleanup                = featureCleanup'
    }
  where
    featureStart' :: CardanoEnvironment -> NoDependency -> CardanoConfiguration -> RotationParameters -> LoggingLayer m
    featureStart' cardanoEnvironment _ cardanoConfiguration rotationParameters = loggingLayer

    featureCleanup' :: (LoggingLayer m) -> IO ()
    featureCleanup' _ = pure () -- save a file, for example


--------------------------------------------------------------------------------
-- Networking feature
--------------------------------------------------------------------------------

--------------------------------
-- Configuration
--------------------------------

-- https://github.com/input-output-hk/cardano-sl/blob/develop/networking/src/Node.hs

type Message = Text

newtype NodeId = NodeId
    { getNodeId :: Int
    } deriving (Eq, Show)

-- TODO(ks): Add some configuration from somewhere?

--------------------------------
-- Layer
--------------------------------

data NetworkLayer m = NetworkLayer
    { sendToNodes   :: NodeId -> m Message
    , readFromNodes :: NodeId -> m Message -- yes, it's pointless
    }

testNetworkLayer :: forall m. (MonadIO m) => NetworkLayer m
testNetworkLayer = NetworkLayer
    { sendToNodes       = \_ -> pure "SEND"
    , readFromNodes     = \_ -> pure "READ"
    }

--------------------------------
-- Feature
--------------------------------

type NetworkingCardanoFeature m = CardanoFeature (LoggingLayer m) Text (NetworkLayer m)

networkingCardanoFeature :: forall m. (MonadIO m) => NetworkingCardanoFeature m
networkingCardanoFeature = CardanoFeature
    { featureType                   = NetworkingFeature
    , featureParseConfiguration     = readFile "./shell.nix"
    , featureStart                  = featureStart'
    , featureCleanup                = featureCleanup'
    }
  where
    featureStart' :: CardanoEnvironment -> LoggingLayer m -> CardanoConfiguration -> Text -> (NetworkLayer m)
    featureStart' cardanoEnvironment loggingLayer cardanoConfiguration _ = testNetworkLayer

    featureCleanup' :: (NetworkLayer m) -> IO ()
    featureCleanup' filePath = pure () -- save a file, for example


