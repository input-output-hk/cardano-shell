{-# LANGUAGE OverloadedStrings #-}

module Cardano.Shell.Environment
  ( SubstitutionError(..)
  , substituteEnvVars
  , getLauncherOption'
  ) where

import           Cardano.Prelude

import           Cardano.Shell.Launcher (LauncherOptions)
import           Cardano.Shell.Template (substituteA)
import           Data.Aeson (Result (..), Value (..), fromJSON)
import           Data.Yaml (decodeFileEither)
import           System.Environment (lookupEnv, setEnv)

-- This is a example of how you can decode yaml and perform env var substitution
-- | Parse `yaml` file, perform env var substitution, return @LauncherOptions@
-- if successful
getLauncherOption' :: FilePath -> IO (Either SubstitutionError LauncherOptions)
getLauncherOption' yamlPath = do
  setEnv "XDG_DATA_HOME" "Foo"
  setEnv "DAEDALUS_CONFIG" "Bar"
  eSubstituted <- runExceptT $ do
    decodedVal <- withExceptT (\e -> FailedToDecodeFile (show e)) $ 
      ExceptT $ decodeFileEither yamlPath
    substituted <- substituteEnvVars decodedVal
    return substituted
  case eSubstituted of
    Left err -> return . Left $ err
    Right sub -> case fromJSON sub of
        Error _ -> return . Left $ FailedToParseLauncherOption
        Success decoded -> return . Right $ decoded

-- | Substitute envrionment variable with value of its name.
--
-- @
-- runExceptT $ substituteEnvVarsText "Hello ${user}"
-- Right "Hello hiroto"
-- @
substituteEnvVarsText :: Text -> ExceptT SubstitutionError IO Text
substituteEnvVarsText text = toStrict <$> (substituteA text expandVariable)

-- type ContextA f = Text -> f Text
-- | Return the value of the environment variable @var@, or throw error if there
-- is no such value.
expandVariable :: Text -> ExceptT SubstitutionError IO Text
expandVariable var = do
    mValue <- liftIO $ lookupEnv (toS var)
    case mValue of
        Nothing    -> throwError $ FailedToLookupEnv var
        Just value -> return $ toS value

data SubstitutionError 
  = FailedToLookupEnv Text
  -- ^ Failed to lookup environment variable
  | FailedToDecodeFile Text
  -- ^ Failed to read/decode yaml file
  | FailedToParseLauncherOption
  -- ^ Failed to convert @Value@ into @LauncherOptions@
  deriving (Eq, Show)

-- | Given an Aeson 'Value', parse and substitute environment variables in all
-- 'String' objects.
substituteEnvVars :: Value -> ExceptT SubstitutionError IO Value
substituteEnvVars (String text) = String <$> substituteEnvVarsText text
substituteEnvVars (Array xs)    = Array  <$> traverse substituteEnvVars xs -- Traversing through array
substituteEnvVars (Object o)    = Object <$> traverse substituteEnvVars o -- Traversing through object
substituteEnvVars x             = return x
