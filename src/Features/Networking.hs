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

type NetworkingCardanoFeature = CardanoFeatureInit LoggingLayer Text NetworkLayer


createNetworkingFeature :: LoggingLayer -> CardanoEnvironment -> CardanoConfiguration -> IO (NetworkLayer, CardanoFeature)
createNetworkingFeature loggingLayer cardanoEnvironment cardanoConfiguration = do
    -- we parse any additional configuration if there is any
    -- We don't know where the user wants to fetch the additional configuration from, it could be from
    -- the filesystem, so we give him the most flexible/powerful context, @IO@.
    networkingConfiguration <-  pure "THIS IS AN EXAMPLE OF A CONFIGURATION!"

    -- we construct the layer
    networkingLayer         <- (featureInit networkingCardanoFeatureInit) cardanoEnvironment loggingLayer cardanoConfiguration networkingConfiguration

    -- we construct the cardano feature
    let cardanoFeature      = networkingCardanoFeature networkingCardanoFeatureInit networkingLayer

    -- we return both
    pure (networkingLayer, cardanoFeature)


networkingCardanoFeatureInit :: NetworkingCardanoFeature
networkingCardanoFeatureInit = CardanoFeatureInit
    { featureType                   = NetworkingFeature
    , featureInit                   = featureStart'
    , featureCleanup                = featureCleanup'
    }
  where
    featureStart' :: CardanoEnvironment -> LoggingLayer -> CardanoConfiguration -> Text -> IO NetworkLayer
    featureStart' = actualNetworkFeature
      where
        actualNetworkFeature :: CardanoEnvironment -> LoggingLayer -> CardanoConfiguration -> Text -> IO NetworkLayer
        actualNetworkFeature _ loggingLayer _ _ = do
            putTextLn "Starting up networking!"
            pure $ testNetworkLayer loggingLayer

    featureCleanup' :: NetworkLayer -> IO ()
    featureCleanup' _ = putTextLn "Shutting down networking feature!" -- close all connections, for example


networkingCardanoFeature :: NetworkingCardanoFeature -> NetworkLayer -> CardanoFeature
networkingCardanoFeature networkingCardanoFeature' networkingLayer = CardanoFeature
    { featureName       = show $ featureType networkingCardanoFeature'
    , featureStart      = do
        putTextLn "Starting up networkingCardanoFeature!"
        void $ pure networkingLayer -- or whatever it means for YOU (a specific team)
    , featureShutdown   = do
        putTextLn "Shutting down networkingCardanoFeature!"
        (featureCleanup networkingCardanoFeature') networkingLayer
    }


