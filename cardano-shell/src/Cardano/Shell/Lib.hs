{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Cardano.Shell.Lib
    ( GeneralException (..)
    , CardanoApplication (..)
    , runCardanoApplicationWithFeatures
    ) where

import           Cardano.Prelude hiding (async, cancel, (%))
import           Prelude (Show (..))

import           Control.Concurrent.Classy.Async (async, cancel)
import qualified Control.Concurrent.Classy.Async as CA

import           Formatting (bprint, build, formatToString, stext, (%))
import           Formatting.Buildable (Buildable (..))

import           Cardano.Shell.Types (CardanoApplication (..),
                                      CardanoFeature (..))

--------------------------------------------------------------------------------
-- General exceptions
--------------------------------------------------------------------------------

data GeneralException
    = UnknownFailureException -- the "catch-all"
    | FileNotFoundException FilePath
    | ConfigurationError Text
    deriving (Eq)

instance Exception GeneralException

instance Buildable GeneralException where
    build UnknownFailureException               = bprint ("Something went wrong and we don't know what.")
    build (FileNotFoundException filePath)      = bprint ("File not found on path '"%stext%"'.") (strConv Lenient filePath)
    build (ConfigurationError etext)            = bprint ("Configuration error: "%stext%".") etext

-- | Instance so we can see helpful error messages when something goes wrong.
instance Show GeneralException where
    show = formatToString Formatting.build

--------------------------------------------------------------------------------
-- Feature initialization
--------------------------------------------------------------------------------

-- Here we run all the features.
-- A general pattern. The dependency is always in a new thread, and we depend on it,
-- so when that dependency gets shut down all the other features that depend on it get
-- shut down as well.
runCardanoApplicationWithFeatures
    :: forall m. MonadIO m
    => [CardanoFeature]
    -> CardanoApplication
    -> m ()
runCardanoApplicationWithFeatures cardanoFeatures cardanoApplication = do

    -- We start all the new features.
    asyncCardanoFeatures <- mapM (liftIO . async . featureStart) cardanoFeatures

    -- Here we run the actual application.
    -- We presume that the control-flow is now in the hands of that function.
    -- An example of top-level-last-resort-error-handling-strategy.
    liftIO $ runCardanoApplication cardanoApplication `finally`
        cancelShutdownFeatures asyncCardanoFeatures

  where
    -- | The cancel and shutdown of all the features.
    cancelShutdownFeatures :: [CA.Async IO a] -> IO ()
    cancelShutdownFeatures asyncCardanoFeatures = do
        -- When we reach this point, we cancel all the features.
        _ <- mapM cancel (reverse asyncCardanoFeatures)

        -- Then we cleanup all the features if we need to do so.
        _ <- mapM featureShutdown (reverse cardanoFeatures)

        -- Closing
        pure ()

