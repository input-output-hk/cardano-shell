{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeApplications #-}

module Lib where

import Cardano.Prelude

--import Control.Exception
import Data.Aeson.Types
import qualified Katip as Katip
import qualified System.Metrics as Ekg

-- | Server configuration
data ServerConfig = ServerConfig
    { scfgLogPath   :: !FilePath
    , scfgDBPath    :: !FilePath
    , scfgSomeParam :: !Int
    }

-- | Sever record
data Server = Server
    { serverEnv :: ServerEnv
    , serverFeatures :: [CardanoFeature]
    }

-- | The common runtime environment for all features in the server.
-- All features have access to this environment.
data ServerEnv = ServerEnv
    { serverLogEnv      :: Katip.LogEnv
    , serverEkgStore    :: Ekg.Store
     -- ...
    }

-- | Cardano feature initialization
data CardanoFeatureInit deps feature config = CardanoFeatureInit
    { featureParseConfig    :: ServerConfig -> Parser config -- ??
    , featureInit           :: ServerEnv -> config -> deps -> IO (feature, CardanoFeature)
    }

-- | Datatype that all features must provide
data CardanoFeature = CardanoFeature
    { featureName       :: Text
    , featureStart      :: IO ()
    , featureShutdown   :: IO ()
       -- Any other generic inspection / reporting goes here
    }

--------------------------------------------------------------------------------
-- Running server
--------------------------------------------------------------------------------

-- | Initialise all the features
initialiseCardanoFeatures :: ServerConfig -> ServerEnv -> IO [CardanoFeature]
initialiseCardanoFeatures config env = do
    (foo, fooFeature) <-
        featureInitWithConfig
            config
            env
            featureInitFoo
            () -- no deps for foo

    (bar, barFeature) <-
        featureInitWithConfig
            config
            env
            featureInitBar
            (foo) -- the bar feature depends on foo
   -- ...
   -- ...
    (_, ekgStatsdFeature) <-
        featureInitWithConfig
            config
            env
            featureInitEkgStats
            () -- no feature deps, it only uses the EKG store

    (_, myFeature) <-
        featureInitWithConfig
            config
            env
            featureInitMyFeature
            (foo, bar)

    let allFeatures =
            [ fooFeature
            , barFeature
         -- ...
            , ekgStatsdFeature
            , myFeature
            ]

    return allFeatures

-- | Initalise 'ServerEnv'
initializeServerEnv :: ServerConfig -> IO ServerEnv
initializeServerEnv config = do
  --  logenv   <- Katip.initLogEnv (...) (...)
    ekgStore <- Ekg.newStore
  --  ...
    return ServerEnv {serverLogEnv = undefined, serverEkgStore = ekgStore}

-- | Clean up 'ServerEnv'
shutdownServerEnv :: ServerEnv -> IO ()
shutdownServerEnv ServerEnv {..} = putTextLn "Cleaning up server envs"

-- | Initialise server
initiaiseServer :: ServerConfig -> IO Server
initiaiseServer config = do
    env <- initializeServerEnv config
    features <- initialiseCardanoFeatures config env
    return Server {serverEnv = env, serverFeatures = features}

-- | Shutdown all the features
shutdownServer :: Server -> IO ()
shutdownServer Server {serverEnv, serverFeatures} = do
    mapM_ featureShutdown serverFeatures
    shutdownServerEnv serverEnv

-- | Start an server with starting all the features
startServer :: Server -> IO ()
startServer Server {serverFeatures} = do
    mapM_ featureStart serverFeatures

-- | Run action with given 'ServerConfig'
withServer :: ServerConfig -> (Server -> IO a) -> IO a
withServer config = bracket (initiaiseServer config) shutdownServer

withServerFramework ::
       (ServerConfig -> ServerEnv -> IO [CardanoFeature])
    -> ServerConfig
    -> (Server -> IO a)
    -> IO a
withServerFramework initializeFeatures serverConfig actionWithServer = do
    bracket initialiseServer shutdownServer actionWithServer
  where
    initialiseServer :: IO Server
    initialiseServer = do
        serverEnv <- initializeServerEnv serverConfig
        cardanoFeatures <- initializeFeatures serverConfig serverEnv
        return $ Server serverEnv cardanoFeatures

initialiseMyFeatures :: ServerConfig -> ServerEnv -> IO [CardanoFeature]
initialiseMyFeatures serverConfig serverEnv = do
    (fooFeature, fooCardanoFeature) <- featureInitWithConfig' featureInitFoo ()
    (barFeature, barCardanoFeature) <- featureInitWithConfig' featureInitBar (fooFeature)
    (myFeature, myCardanoFeature)   <- featureInitWithConfig' featureInitMyFeature (fooFeature, barFeature)

    return [fooCardanoFeature, barCardanoFeature, myCardanoFeature]
  where
    featureInitWithConfig' = featureInitWithConfig serverConfig serverEnv

initialiseFooFeatures :: ServerConfig -> ServerEnv -> IO [CardanoFeature]
initialiseFooFeatures serverConfig serverEnv = do
    (_, fooCardanoFeature) <- featureInitWithConfig' featureInitFoo ()
    return [fooCardanoFeature]
  where
    featureInitWithConfig' = featureInitWithConfig serverConfig serverEnv

featureInitWithConfig ::
       ServerConfig
    -> ServerEnv
    -> CardanoFeatureInit deps feature config
    -> deps
    -> IO (feature, CardanoFeature)
featureInitWithConfig config env CardanoFeatureInit {..} deps = do
    featureConfig <-
        case parseEither featureParseConfig config of
            Left e  -> exitFailure
            Right c -> return c

    featureInit env featureConfig deps

-- | Running server
runServer :: IO ()
runServer = do
    let serverConfig = ServerConfig mempty mempty 0
    -- Do everything within bracket in case the program shutdown unexpectedly..
    putTextLn "\nPerforming some computation with Foo features"
    withServerFramework initialiseFooFeatures serverConfig $ \server -> do
        putTextLn "Action was perfomed successfully!"
    putTextLn "\nPerforming some computation with My features"
    withServerFramework initialiseMyFeatures serverConfig $ \server -> do
        putTextLn "Action was perfomed successfully!"

--------------------------------------------------------------------------------
-- CardanoFeatureInits
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- Foo
--------------------------------------------------------------------------------
data FooConfig = FooConfig
    { fooCfgA :: !Text
    , fooCfgB :: !Int
    }

data FooFeature = FooFeature
    { fooA :: Text -> IO ()
    , fooB :: forall a. [a] -> Int
    , fooC :: Integer -> Integer -> Integer
    }

fooConfig :: FooConfig
fooConfig = FooConfig "This is Foo" 1

fooCardanoFeature :: CardanoFeature
fooCardanoFeature =
    CardanoFeature
        { featureName = "Foo"
        , featureStart = putTextLn "Starting Foo"
        , featureShutdown = putTextLn "Shutting down Foo"
        }

featureInitFoo :: CardanoFeatureInit () FooFeature FooConfig
featureInitFoo =
    CardanoFeatureInit
        { featureParseConfig = \_ -> return fooConfig
        , featureInit = mkFooFeature
        }

mkFooFeature :: ServerEnv -> FooConfig -> () -> IO (FooFeature, CardanoFeature)
mkFooFeature serverEnv config _ = do
    return (fooFeature, fooCardanoFeature)
  where
    fooFeature :: FooFeature
    fooFeature =
        FooFeature
            { fooA = \str -> putTextLn $ "Using Foo feature: " <> str
            , fooB = length
            , fooC = (+)
            }

--------------------------------------------------------------------------------
-- Bar
--------------------------------------------------------------------------------
data BarFeature = BarFeature
    { barA :: Text -> IO ()
    , barB :: Int -> Bool
    , barC :: Text -> Bool
    }

data BarConfig = BarConfig
    { barCfgA :: !Text
    , barCfgB :: !Int
    }

barConfig :: BarConfig
barConfig = BarConfig "This is bar" 10

barCardanoFeature :: CardanoFeature
barCardanoFeature =
    CardanoFeature
        { featureName = "Bar"
        , featureStart = putTextLn "Starting Bar"
        , featureShutdown = putTextLn "Shutting down Bar"
        }

featureInitBar :: CardanoFeatureInit FooFeature BarFeature BarConfig
featureInitBar =
    CardanoFeatureInit
        { featureParseConfig = \_ -> return barConfig
        , featureInit = mkBarFeature
        }

mkBarFeature ::
       ServerEnv -> BarConfig -> FooFeature -> IO (BarFeature, CardanoFeature)
mkBarFeature serverEnv config foo = do
    fooA foo $ "Doing bar stuff"
    return (barFeature, barCardanoFeature)
  where
    barFeature :: BarFeature
    barFeature =
        BarFeature
            { barA = \str -> putTextLn $ "Using Bar feature: " <> str
            , barB = (> 10)
            , barC = (== "Blockchain")
            }

--------------------------------------------------------------------------------
-- EkgStats
--------------------------------------------------------------------------------
data EkgStatsFeature = EkgStatsFeature
    { ekgA :: FilePath -> Int
    , ekgB :: Text -> Text -> Text
    }

data EkgStateConfig = EkgStateConfig
    { ekgCfgA :: !Text
    , ekgCfgB :: !Int
    }

ekgStatsCardanoFeature :: CardanoFeature
ekgStatsCardanoFeature =
    CardanoFeature
        { featureName = "EkgState"
        , featureStart = putTextLn "Starting EkgState"
        , featureShutdown = putTextLn "Shutting down EkgState"
        }

ekgStateConfig :: EkgStateConfig
ekgStateConfig = EkgStateConfig "This is ekgState " 100

featureInitEkgStats :: CardanoFeatureInit () EkgStatsFeature EkgStateConfig
featureInitEkgStats =
    CardanoFeatureInit
        { featureParseConfig = \_ -> return ekgStateConfig
        , featureInit = mkEkgStatsFeature
        }

mkEkgStatsFeature ::
       ServerEnv -> EkgStateConfig -> () -> IO (EkgStatsFeature, CardanoFeature)
mkEkgStatsFeature serverEnv config _ =
    return (ekgStatsFeature, ekgStatsCardanoFeature)
  where
    ekgStatsFeature :: EkgStatsFeature
    ekgStatsFeature = EkgStatsFeature {ekgA = genericLength, ekgB = (<>)}

--------------------------------------------------------------------------------
-- MyFeature
--------------------------------------------------------------------------------
data MyFeature = MyFeature
    { myA :: Text -> IO ()
    , myB :: Int -> Int
    }

data MyConfig = MyConfig
    { mcfgA :: !Text
    , mcfgB :: !Int
    }

myConfig :: MyConfig
myConfig = MyConfig "This is MyFeature" 1000

featureInitMyFeature ::
       CardanoFeatureInit (FooFeature, BarFeature) MyFeature MyConfig
featureInitMyFeature =
    CardanoFeatureInit
        { featureParseConfig = \_ -> return myConfig
        , featureInit = mkMyFeatureInit
        }

mkMyFeatureInit ::
       ServerEnv
    -> MyConfig
    -> (FooFeature, BarFeature)
    -> IO (MyFeature, CardanoFeature)
mkMyFeatureInit serverEnv config (fooCfg, barCfg) = do
    myFeature <- mkMyFeature config fooCfg barCfg
    return (myFeature, myCardanoFeature)
  where
    mkMyFeature :: MyConfig -> FooFeature -> BarFeature -> IO MyFeature
    mkMyFeature config foo bar = do
        fooA foo (mcfgA config)
        barA bar (show $ mcfgB config)
        return $
            MyFeature
                { myA = \str -> putTextLn $ "Using my feature: " <> str
                , myB = \num -> num + mcfgB config
                }
    myCardanoFeature :: CardanoFeature
    myCardanoFeature =
        CardanoFeature
            { featureName = "MyFeature"
            , featureStart = putTextLn "Starting MyFeature"
            , featureShutdown = putTextLn "Shutting down MyFeature"
            }

-- *Main Lib> runServer
-- Performing some computation with Foo features
-- Action was perfomed successfully!
-- Shutting down Foo
-- Cleaning up server envs
-- Performing some computation with My features
-- Using Foo feature: Doing bar stuff
-- Using Foo feature: This is MyFeature
-- Using Bar feature: 1000
-- Action was perfomed successfully!
-- Shutting down Foo
-- Shutting down Bar
-- Shutting down MyFeature
-- Cleaning up server envs
