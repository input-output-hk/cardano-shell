{-# LANGUAGE Rank2Types #-}

module Features.Networking where

import Cardano.Prelude

import Control.Exception.Safe

--import Control.Concurrent.Classy
--import Control.Concurrent.Classy.Async

import Types
import Features.Logging

--------------------------------------------------------------------------------
-- Networking feature
--------------------------------------------------------------------------------

-- This module depends only on the logging feature.

--------------------------------
-- Exceptions
--------------------------------

data NetworkingException
    = UnknownPeerException
    -- | ...
    deriving (Eq, Show)

instance Exception NetworkingException

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

data NetworkLayer = NetworkLayer
    { sendToNodes   :: forall m. (MonadIO m)                => NodeId -> m Message
    , readFromNodes :: forall m. (MonadIO m, MonadThrow m)  => NodeId -> m Message -- yes, it's pointless
    }

testNetworkLayer :: LoggingLayer -> NetworkLayer
testNetworkLayer loggingLayer = NetworkLayer
    { sendToNodes       = \_ -> pure "SEND"
    , readFromNodes     = \_ -> iolNonIo loggingLayer >> pure "READ"
    }

--------------------------------
-- Feature
--------------------------------

type NetworkingCardanoFeature = CardanoFeature LoggingLayer Text NetworkLayer

networkingCardanoFeature :: NetworkingCardanoFeature
networkingCardanoFeature = CardanoFeature
    { featureType                   = NetworkingFeature
    , featureParseConfiguration     = readFile "./shell.nix"
    , featureStart                  = featureStart'
    , featureCleanup                = featureCleanup'
    }
  where
    featureStart' :: CardanoEnvironment -> LoggingLayer -> CardanoConfiguration -> Text -> IO NetworkLayer
    featureStart' = actualNetworkFeature

    featureCleanup' :: NetworkLayer -> IO ()
    featureCleanup' _ = putTextLn "Shutting down networking feature!" -- close all connections, for example

-- MonadConc m => m a -> m (Async m a)
-- :: forall m. (MonadConc m, MonadIO m) => CardanoEnvironment -> Async LoggingLayer -> CardanoConfiguration -> Text -> m (Async m NetworkLayer)
actualNetworkFeature :: CardanoEnvironment -> LoggingLayer -> CardanoConfiguration -> Text -> IO NetworkLayer
actualNetworkFeature _ asyncLoggingLayer _ _ = do
    putTextLn "Starting up networking feature!"
    pure $ testNetworkLayer asyncLoggingLayer



