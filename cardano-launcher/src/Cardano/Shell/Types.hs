-- | General types for both the update and the launcher.
module Cardano.Shell.Types
    ( LoggingDependencies (..)
    , nullLogging
    ) where

import           Cardano.Prelude

-- | Dependencies for logging.
data LoggingDependencies = LoggingDependencies
    { logInfo   :: Text -> IO ()
    , logError  :: Text -> IO ()
    , logNotice :: Text -> IO ()
    }

-- | The empty/null logging for purposes where we
-- don't need it (like testing).
nullLogging :: LoggingDependencies
nullLogging = LoggingDependencies
    { logInfo       = \_ -> pure ()
    , logError      = \_ -> pure ()
    , logNotice     = \_ -> pure ()
    }

