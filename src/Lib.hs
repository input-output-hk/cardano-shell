module Lib
    ( CardanoModule (..)
    , someFunc
    ) where

import           Cardano.Prelude

someFunc :: IO ()
someFunc = putText "Test"

-- | The basic configuration structure. It should contain all the required
-- configuration parameters for the modules to work.
data Configuration = Configuration
    { _stuffToConfigure :: !Text
    , _moreStuff        :: !Text
    } deriving (Eq, Show)

-- | A general workflow for any cardano module.
data CardanoModule configuration m = CardanoModule
    { preConfiguration   :: IO ()
    , parseConfiguration :: IO configuration
    , postConfiguration  :: IO ()
    , withConfiguration  :: configuration -> m ()
    , cleanup            :: IO ()
    }

-- withAsync :: IO a -> (Async a -> IO b) -> IO b



