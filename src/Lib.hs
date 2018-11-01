{-# LANGUAGE TemplateHaskell #-}

module Lib
    ( CardanoModule (..)
    , someFunc
    , runCardanoModule
    , runCardanoModuleWithDependency
    ) where

import           Cardano.Prelude

--import           Lens.Micro
--import           Lens.Micro.TH

someFunc :: IO ()
someFunc = putText "Test"

----------------------------------------------------------------------------
-- General architecture
----------------------------------------------------------------------------

-- | The basic configuration structure. It should contain all the required
-- configuration parameters for the modules to work.
-- This is _just an example_ and it's purpose it's just to show how it would work.
data Configuration = Configuration
    { _stuffToConfigure :: !Text
    , _moreStuff        :: !Text
    } deriving (Eq, Show)

-- | If we require options to automatically restart a module.
data ModuleAutoRestart
    = ModuleRestart
    | ModuleNoRestart
    deriving (Eq, Show)

-- waitCatch :: Async a -> IO (Either SomeException a)

-- | A general workflow for any cardano module.
data CardanoModule configuration result = CardanoModule
    { _parseConfiguration   :: IO configuration
    -- ^ A parser for the configuration
    , _initialization       :: IO () -- TODO(ks): add as a type parameter
    -- ^ Initialization if required
    , _moduleRunner         :: Async configuration -> IO result
    -- ^ The actual runner for the module
    , _cleanup              :: IO () -- TODO(ks): remove
    -- ^ Cleanup if neccessary.
    }

-- https://mail.haskell.org/pipermail/haskell/2005-September/016502.html

-- This is an example of how a @CardanoModule@ could work.
runCardanoModule :: CardanoModule Configuration () -> IO ()
runCardanoModule cardanoModule = do

    -- we initialize the module if required
    _initialization cardanoModule

    -- then we run the module after parsing the configuration
    let parsedConfiguration     = _parseConfiguration cardanoModule
    let moduleRunner            = _moduleRunner cardanoModule

    result <- withAsync parsedConfiguration moduleRunner

    -- clean it up
    _       <- _cleanup cardanoModule

    -- return the result
    pure result

-- This is an example of how a @CardanoModule@ could work if it requires
-- a dependency.
-- dependencyModule ~ (LoggingCardanoModule, MonitoringCardanoModule, ...)
runCardanoModuleWithDependency :: dependencyModule -> CardanoModule configuration result -> IO result
runCardanoModuleWithDependency _ cardanoModule = do

    -- if the dependency is another cardano module
    --runCardanoModule logging
    --runCardanoModule monitoring

    -- we initialize the module if required
    _initialization cardanoModule

    -- then we run the module after parsing the configuration
    let parsedConfiguration     = _parseConfiguration cardanoModule
    let moduleRunner            = _moduleRunner cardanoModule

    result  <- withAsync parsedConfiguration moduleRunner

    -- clean it up
    _       <- _cleanup cardanoModule

    -- return the result
    pure result

{-

fix :: (a        -> a       ) -> a
fix :: ((b -> c) -> (b -> c)) -> (b -> c)
fix :: ((b -> c) ->  b -> c ) -> b -> c

mfix :: (a -> m a) -> m a
mfix :: (CardanoModule configuration result -> IO (CardanoModule configuration result)) -> IO (CardanoModule configuration result)

-}

-- | We can structure the construction of the module in phases.
data CardanoShellPhases
    = LoggingPhase
    | MonitoringPhase
    | NetworkPhase
    | BlockchainPhase
    | LedgerPhase
--  | ...
    deriving (Eq, Show)

----------------------------------------------------------------------------
-- Lenses derivation
----------------------------------------------------------------------------

--makeLenses 'Configuration
--makeLenses 'CardanoModule

