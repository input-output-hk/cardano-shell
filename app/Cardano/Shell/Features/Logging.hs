{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE Rank2Types          #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Cardano.Shell.Features.Logging
    ( LoggingLayer (..)
    , createLoggingFeature
    -- re-exports
    , Trace
    , Configuration
    , LoggerName
    , Severity (..)
    , mkLOMeta
    , LOMeta (..)
    , LOContent (..)
    ) where

import           Control.Exception.Safe (MonadCatch)
import qualified Control.Monad.STM as STM
import           Cardano.Prelude hiding (trace)
import           Options.Applicative

import           Cardano.BM.Configuration (Configuration)
import qualified Cardano.BM.Configuration as Config
import           Cardano.BM.Data.LogItem (LoggerName, LOMeta (..),
                     LOContent (..), mkLOMeta)
import           Cardano.BM.Data.Severity (Severity (..))
import qualified Cardano.BM.Observer.Monadic as Monadic
import qualified Cardano.BM.Observer.STM as Stm
import           Cardano.BM.Setup (setupTrace_, shutdown)
import           Cardano.BM.Trace (Trace)
import qualified Cardano.BM.Trace as Trace

import           Cardano.Shell.Types (CardanoEnvironment, CardanoFeature (..),
                                      CardanoFeatureInit (..),
                                      NoDependency (..))

import           Cardano.Shell.Constants.Types (CardanoConfiguration)

--------------------------------------------------------------------------------
-- Loggging feature
--------------------------------------------------------------------------------

--------------------------------
-- Configuration
--------------------------------

data LoggingParameters = LoggingParameters
    { lpConfiguration :: Configuration
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
    { llBasicTrace      :: forall m . MonadIO m => Trace m Text
    , llLogDebug        :: forall m a. (MonadIO m, Show a) => Trace m a  -> a -> m ()
    , llLogInfo         :: forall m a. (MonadIO m, Show a) => Trace m a  -> a -> m ()
    , llLogNotice       :: forall m a. (MonadIO m, Show a) => Trace m a  -> a -> m ()
    , llLogWarning      :: forall m a. (MonadIO m, Show a) => Trace m a  -> a -> m ()
    , llLogError        :: forall m a. (MonadIO m, Show a) => Trace m a  -> a -> m ()
    , llAppendName      :: forall m a. (MonadIO m, Show a) => LoggerName -> Trace m a -> m (Trace m a)
    , llBracketMonadIO  :: forall a t. (Show a) => Trace IO a -> Severity -> Text -> IO t -> IO t
    , llBracketMonadM   :: forall a m t. (MonadCatch m, MonadIO m, Show a) => Trace m a -> Severity -> Text -> m t -> m t
    , llBracketMonadX   :: forall m a t. (MonadIO m, Show a) => Trace m a -> Severity -> Text -> m t -> m t
    , llBracketStmIO    :: forall a t. (Show a) => Trace IO a -> Severity -> Text -> STM.STM t -> IO t
    , llBracketStmLogIO :: forall a t. (Show a) => Trace IO a -> Severity -> Text -> STM.STM (t,[(LOMeta, LOContent a)]) -> IO t
    }

--------------------------------
-- Feature
--------------------------------

type LoggingCardanoFeature = CardanoFeatureInit NoDependency LoggingParameters LoggingLayer

-- parser
data LogOptions = LogOptions
    { logconfigfile :: FilePath
    }

parser :: Parser LogOptions
parser = LogOptions
      <$> strOption
          ( long "log-config"
         <> metavar "LOGCONFIG"
         <> value ""
         <> help "configuration file for logging" )

parser_opts :: ParserInfo LogOptions
parser_opts = info (parser <**> helper)
    ( fullDesc
    <> progDesc "Logging Feature"
    <> header "cardano-shell: logging feature" )

createLoggingFeature :: CardanoEnvironment -> CardanoConfiguration -> IO (LoggingLayer, CardanoFeature)
createLoggingFeature cardanoEnvironment cardanoConfiguration = do
    -- we parse any additional configuration if there is any
    -- We don't know where the user wants to fetch the additional configuration from, it could be from
    -- the filesystem, so we give him the most flexible/powerful context, @IO@.
    -- loggingConfiguration    <-  LoggingParameters <$> (Config.setup $ ccLogConfig cardanoConfiguration)
    configopts <- execParser parser_opts
    loggingConfiguration    <-  LoggingParameters <$> (Config.setup $ logconfigfile configopts)

    -- we construct the layer
    logCardanoFeat <- loggingCardanoFeatureInit loggingConfiguration

    loggingLayer            <- (featureInit logCardanoFeat)
                               cardanoEnvironment
                               NoDependency
                               cardanoConfiguration
                               loggingConfiguration

    -- we construct the cardano feature
    let cardanoFeature      = createCardanoFeature logCardanoFeat loggingLayer

    -- we return both
    pure (loggingLayer, cardanoFeature)

-- | Initialize `LoggingCardanoFeature`
loggingCardanoFeatureInit :: LoggingParameters -> IO LoggingCardanoFeature
loggingCardanoFeatureInit loggingConfig = do
    let logconfig = lpConfiguration loggingConfig
    (baseTrace, switchBoard) <- setupTrace_ logconfig "cardano"

    let initLogging :: CardanoEnvironment -> NoDependency -> CardanoConfiguration -> LoggingParameters -> IO LoggingLayer
        initLogging _ _ _ _ = do
            pure $ LoggingLayer
                    { llBasicTrace    = Trace.natTrace liftIO baseTrace
                    , llLogDebug      = Trace.logDebug
                    , llLogInfo       = Trace.logInfo
                    , llLogNotice     = Trace.logNotice
                    , llLogWarning    = Trace.logWarning
                    , llLogError      = Trace.logError
                    , llAppendName    = Trace.appendName
                    , llBracketMonadIO = Monadic.bracketObserveIO logconfig
                    , llBracketMonadM = Monadic.bracketObserveM logconfig
                    , llBracketMonadX = Monadic.bracketObserveX logconfig
                    , llBracketStmIO  = Stm.bracketObserveIO logconfig
                    , llBracketStmLogIO = Stm.bracketObserveLogIO logconfig
                    }
    let cleanupLogging :: LoggingLayer -> IO ()
        cleanupLogging _ = shutdown switchBoard

    pure $ CardanoFeatureInit
             { featureType    = "LoggingMonitoringFeature"
             , featureInit    = initLogging
             , featureCleanup = cleanupLogging
             }

-- | Create `CardanoFeature`
createCardanoFeature :: LoggingCardanoFeature -> LoggingLayer -> CardanoFeature
createCardanoFeature loggingCardanoFeature loggingLayer = CardanoFeature
    { featureName       = "LoggingMonitoringFeature"
    , featureStart      = liftIO $ do
        void $ pure loggingLayer
    , featureShutdown   = liftIO $ do
        (featureCleanup loggingCardanoFeature) loggingLayer
    }
