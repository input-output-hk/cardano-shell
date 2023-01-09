{-| This module test that @substituteEnvVars@ works as expected
|-}

{-# LANGUAGE LambdaCase #-}

module EnvironmentSpec
    ( envSubstitutionSpec
    ) where

import           Cardano.Prelude
import qualified Data.HashMap.Strict as HM
import qualified Data.Vector as V
import qualified Data.Yaml as Y
import           System.Environment (setEnv, unsetEnv)
import           Test.Hspec (Spec)
import           Test.Hspec.QuickCheck (modifyMaxSuccess, prop)
import           Test.QuickCheck (Arbitrary (..), Gen, arbitraryASCIIChar,
                                  arbitraryPrintableChar, elements, listOf,
                                  listOf1, oneof, suchThat)
import           Test.QuickCheck.Monadic (assert, monadicIO, run)

import           Cardano.Shell.Environment (SubstitutionError (..),
                                            substituteEnvVars)

-- | Random Yaml object
newtype RandomValue = RandomValue Y.Value
    deriving Show

-- | Pair of environment variable and its value
data EnvValue = EnvValue !Text !Text
    deriving Show

instance Arbitrary RandomValue where
    arbitrary = RandomValue <$> genValue
        where
            genValue :: Gen Y.Value
            genValue = oneof
                [ genObject
                , genString
                , genArray
                ]

            genString :: Gen Y.Value
            genString = Y.String <$> genText

            genObject :: Gen Y.Value
            genObject = (Y.Object . HM.fromList) <$> listOf1 genKeyValue

            genArray :: Gen Y.Value
            genArray = (Y.Array . V.fromList) <$> listOf1 genString

            genKeyValue :: Gen (Text, Y.Value)
            genKeyValue = do
                randomField <- genText
                randomValue <- genString
                return $ (randomField, randomValue)

            genText :: Gen Text
            genText = toS <$> listOf
                (arbitraryPrintableChar `suchThat` (`notElem` ['$', '{', '}']))

instance Arbitrary EnvValue where
    arbitrary = EnvValue <$> randomVar <*> randomValue
      where
        randomVar = toS <$> listOf1 (elements $ ['A' .. 'Z'] <> ['0' .. '9'] <> ['_'])
        randomValue = toS <$> listOf1 (arbitraryASCIIChar `suchThat` isAlphaNum)

-- | Given a @EnvValue@, create a pair of yaml object, one with identifier text
-- and other is expected result. This would be used to compare if substitution
-- was done properly
mkPairs :: EnvValue -> Y.Value -> (Y.Value, Y.Value)
mkPairs (EnvValue var value) yamlObject =
    let yamlObjectVar = appendText ("${" <> var <> "}") yamlObject
        yamlObjectValue = appendText value yamlObject
    in (yamlObjectVar, yamlObjectValue)
  where
    -- Append Text to the String value
    appendText :: Text -> Y.Value -> Y.Value
    appendText text = \case
        Y.Object object -> Y.Object $ fmap (appendText text) object
        Y.String string -> Y.String $ text <> string
        Y.Array array -> Y.Array $ fmap (appendText text) array
        others -> others

envSubstitutionSpec :: Spec
envSubstitutionSpec = modifyMaxSuccess (const 1000) $ do
    prop "Should be able to perform env var substitution" $
        \(envvalue@(EnvValue var value), (RandomValue yamlObject)) -> monadicIO $ do
        let (sub, expectedResult) = mkPairs envvalue yamlObject
        subbed <- run $ do
            subbed <- withEnv (toS var) (toS value) (runExceptT (substituteEnvVars sub))
            return subbed
        assert $ subbed == (Right expectedResult)

    prop "Should throw error due to env var missing" $
        \(envvalue@(EnvValue var _value), (RandomValue yamlObject)) -> monadicIO $ do
        let (sub, _expectedResult) = mkPairs envvalue yamlObject
        eSubbed <- run $ do
            unsetEnv (toS var)
            runExceptT (substituteEnvVars sub)
        assert $ eSubbed == (Left $ FailedToLookupEnv var)
  where
    withEnv :: Text -> Text -> IO a -> IO a
    withEnv var value action = bracket
        (setEnv (toS var) (toS value))
        (const $ unsetEnv (toS var))
        (const action)
