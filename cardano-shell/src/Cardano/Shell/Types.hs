{-# LANGUAGE Rank2Types #-}

module Cardano.Shell.Types
    ( CardanoFeature (..)
    , CardanoFeatureInit (..)
    , NoDependency (..)
    , ApplicationEnvironment (..)
    , CardanoApplication (..)
    , applicationProductionMode
    ) where

import           Cardano.Prelude

import           Control.Concurrent.Classy (MonadConc)

-- | The top level module we use to run the key functions.
newtype CardanoApplication = CardanoApplication { runCardanoApplication :: IO () }

-- | The application environment.
data ApplicationEnvironment
    = Development
    | Production
    deriving (Eq, Show)

-- | A simple function to inform us.
applicationProductionMode :: ApplicationEnvironment -> Bool
applicationProductionMode Production = True
applicationProductionMode _          = False

-- | The option to not have any additional dependency for the @CardanoFeature@.
data NoDependency = NoDependency
    deriving (Eq, Show)

-- | The option to not have any additional configuration for the @CardanoFeature@.
data NoConfiguration = NoConfiguration
    deriving (Eq, Show)

-- | Cardano feature initialization.
-- We are saying "you have the responsibility to make sure you use the right context!".
data CardanoFeatureInit env dependency cardanoConfiguration featureConfiguration layer = CardanoFeatureInit
    { featureType                   :: !Text
    -- ^ The type of the feature that we use.
    , featureInit                   :: env -> dependency -> cardanoConfiguration -> featureConfiguration -> IO layer
    -- ^ Again, we are not sure how is the user going to run the actual feature,
    -- so we provide him with the most flexible/powerful context we have, @IO@.
    -- Notice the arrangement of the parameters - specific, general, specific, general, result.
    , featureCleanup                :: layer -> IO ()
    -- ^ If the user wants to clean up the resources after the module has completed running,
    -- there is an option to do so.
    }

-- | The interface for the running feature, the high-level interface we use for running it.
data CardanoFeature = CardanoFeature
    { featureName     :: Text
    -- ^ The name of the feature.
    , featureStart    :: forall m. (MonadIO m, MonadConc m) => m ()
    -- ^ What we call when we start the feature.
    , featureShutdown :: forall m. (MonadIO m, MonadConc m) => m ()
    -- ^ What we call when we shut down the feature.
    }
