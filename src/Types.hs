{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Types where

import Cardano.Prelude

--import qualified Katip as Katip
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
    { serverLogEnv      :: Text --Katip.LogEnv
    , serverEkgStore    :: Ekg.Store
     -- ...
    }

-- | Initalise 'ServerEnv'
initializeCardanoEnvironment :: IO CardanoEnvironment
initializeCardanoEnvironment = do
  --  logenv   <- Katip.initLogEnv (...) (...)
    ekgStore <- Ekg.newStore
    return CardanoEnvironment {serverLogEnv = "To implement", serverEkgStore = ekgStore}

loadCardanoConfiguration :: IO CardanoConfiguration
loadCardanoConfiguration = do
    pure $ CardanoConfiguration mempty mempty 0


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
    , featureStart                  :: CardanoEnvironment -> dependency -> CardanoConfiguration -> configuration -> IO layer
    -- ^ Again, we are not sure how is the user going to run the actual feature,
    -- so we provide him with the most flexible/powerful context we have, @IO@.
    -- Notice the arrangement of the parameters - specific, general, specific, general, result.
    -- The dependency is an @Async@, since it's _always run in another thread_.
    , featureCleanup                :: layer -> IO ()
    -- ^ If the user wants to clean up the resources after the module has completed running,
    -- there is an option to do so.
    }

--------------------------------------------------------------------------------
-- General exceptions
--------------------------------------------------------------------------------

data GeneralException
    = UnknownFailureException -- the "catch-all"
    | FeatureCancelled
    | MissingResourceException
    | FileNotFoundException
    -- | ...
    deriving (Eq, Show)

instance Exception GeneralException

--------------------------------------------------------------------------------
-- Feature
--------------------------------------------------------------------------------

-- | A feature layer with the corresponding feature @ThreadId@.
data Feature a = Feature ThreadId a
    deriving (Eq, Show)

-- | The construction same as/very similar to @Async@ which allows us to cancel specific threads/features.
withFeatureUsing :: forall a b. IO a -> (a -> IO b) -> IO b
withFeatureUsing = \action inner -> do
  var <- newEmptyMVar

  mask $ \restore -> do
    -- In another thread, we don't know the type of exception beforehand.
    threadId    <- forkIO $ try @SomeException (restore action) >>= putMVar var
    var         <- readMVar var

    -- If there is an error when building the feature.
    result      <- either (\_ -> throwIO UnknownFailureException) pure var

    let constructedFeature :: Feature a
        constructedFeature = Feature threadId result

    r           <- restore (inner result) `catchAll` \e -> do
      uninterruptibleCancel constructedFeature
      throwIO e

    uninterruptibleCancel constructedFeature
    return r

  where
    catchAll :: forall a b. IO a -> (SomeException -> IO a) -> IO a
    catchAll = catch

    uninterruptibleCancel :: forall a. Feature a -> IO ()
    uninterruptibleCancel = uninterruptibleMask_ . featureCancel

featureCancel :: forall a. Feature a -> IO ()
featureCancel (Feature t _) = throwTo t FeatureCancelled



