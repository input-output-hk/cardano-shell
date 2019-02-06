{-# LANGUAGE Rank2Types       #-}
{-# LANGUAGE TypeApplications #-}

module Main where

import           Cardano.Prelude

import           Control.Concurrent.Classy (MonadConc)
import           Control.Exception.Safe (throwM)
import           DhallConfigSpec (dhallConfigSpec, mkConfigSpec)

import           Test.DejaFu (abortsNever, deadlocksNever, exceptionsNever)
import           Test.Hspec (Spec, describe, hspec)
import           Test.Hspec.Contrib.HUnit (fromHUnitTest)
import           Test.HUnit.DejaFu (testDejafu)
import           Test.QuickCheck (Gen, arbitraryASCIIChar, choose, frequency,
                                  generate, listOf1, oneof)

import           Cardano.Shell.Lib (AllFeaturesInitFunction,
                                    GeneralException (..), runApplication)
import           Cardano.Shell.Types (CardanoFeature (..))

-- | Entry point for tests.
main :: IO ()
main = hspec $ do
    describe "App should have no concurrency issues" validConcurrencySpec
    describe "Dhall configurations" dhallConfigSpec
    describe "Cardano configurations" mkConfigSpec

-- | A valid concurrency specification.
validConcurrencySpec :: Spec
validConcurrencySpec = do

    describe "runCardanoApplicationWithFeaturesConcurrencySunnyDay" $ do
        fromHUnitTest $ testDejafu "Assert it never abort" abortsNever runApplicationSunnyDay
        fromHUnitTest $ testDejafu "Assert it never deadlocks" deadlocksNever runApplicationSunnyDay
        fromHUnitTest $ testDejafu "Assert it doesn't raise exceptions" exceptionsNever runApplicationSunnyDay

    describe "runCardanoApplicationWithFeaturesConcurrencyExceptional" $ do
        fromHUnitTest $ testDejafu "Assert it never abort" abortsNever runApplicationExceptional
        fromHUnitTest $ testDejafu "Assert it never deadlocks" deadlocksNever runApplicationExceptional
        fromHUnitTest $ testDejafu "Assert it doesn't raise exceptions" exceptionsNever runApplicationExceptional

  where

    -- | What happens when the application terminates nicely?
    runApplicationSunnyDay :: forall m. (MonadIO m, MonadConc m) => m ()
    runApplicationSunnyDay = runApplication cardanoFeaturesInit application
      where
        application :: IO ()
        application = pure ()

    -- | What happens when the application terminates exceptionally?
    runApplicationExceptional :: forall m. (MonadIO m, MonadConc m) => m ()
    runApplicationExceptional = runApplication cardanoFeaturesInit application
      where

        application :: IO ()
        application = void $ throwM @IO <$> arbitraryGeneralException
        -- ^ helping the compiler with TypeApplications
          where
            arbitraryGeneralException :: IO GeneralException
            arbitraryGeneralException = generate . oneof $
                [ pure UnknownFailureException
                , pure ApplicationAlreadyRunningException
                ]

    -- | We actually need to improve this and add arbitrary @CardanoFeature@s
    -- and add concurrency primitives of appropriate depth to check we have it working.
    -- It used to work with the test features that were moved into the executable since
    -- we wanted to split the project.
    cardanoFeaturesInit :: AllFeaturesInitFunction
    cardanoFeaturesInit = \_ _ ->
        -- We have to be careful about the number of features here.
        replicateM 5 cardanoFeatureGeneratorIO

    -- | @CardanoFeature@ generator.
    cardanoFeatureGeneratorIO :: IO CardanoFeature
    cardanoFeatureGeneratorIO = do
        cardanoFeatureName          <- generate genSafeText

        let cardanoFeatureStart :: forall m. (MonadIO m) => m ()
            cardanoFeatureStart = generateSingleCommand

        let cardanoFeatureShutdown :: forall m. (MonadIO m) => m ()
            cardanoFeatureShutdown  = generateSingleCommand

        pure $ CardanoFeature
            cardanoFeatureName
            cardanoFeatureStart
            cardanoFeatureShutdown
      where
        -- | Generate random ascii string
        genSafeText :: Gen Text
        genSafeText = strConv Lenient <$> listOf1 arbitraryASCIIChar

-- | The function that generates a single command in @IO@.
generateSingleCommand :: (MonadIO m) => m ()
generateSingleCommand = do
    generatedCommand <- liftIO $ generate concurrencyDSLGenerator
    interepretConcurrencyDSL generatedCommand

-- | The function that creates a list of commands in @IO@.
generateListOfCommands :: (MonadIO m) => m ()
generateListOfCommands = do
    generatedCommands <- liftIO . generate . listOf1 $ concurrencyDSLGenerator
    void $ traverse interepretConcurrencyDSL generatedCommands

-- | The interpretation of the DSL result. It's been simplified so we don't need to
-- roam into the type side of the story.
interepretConcurrencyDSL :: forall m. (MonadIO m) => CommandDSL ->  m ()
interepretConcurrencyDSL (SequentialCmd delay)  = liftIO . threadDelay $ delay
interepretConcurrencyDSL (ParallelCmd delay)    = liftIO . void . forkIO . threadDelay $ delay
interepretConcurrencyDSL (AsyncCmd delay)       = liftIO . void . async . threadDelay $ delay

-- | The delay in microseconds.
type MicrosecondsDelay = Int

-- | The DSL used to simulate commands. A very general abstraction is that
-- every command takes some time. For that, we introduce @delay@, we are really not
-- interested in the command itself or what it does.
-- We are modeling it's behaviour and are interested in the timings _only_.
-- We have commands that are sequential, that are parallel and those that are async.
-- We can simulate all three of these with a simple delay on them.
-- Again, the delay signifies an actual execution of the command which takes time.
data CommandDSL
    = SequentialCmd MicrosecondsDelay
    | ParallelCmd MicrosecondsDelay
    | AsyncCmd MicrosecondsDelay
    deriving (Eq, Show)

-- | The DSL generator. It uses specific frequencies so it a bit biased,
-- but I think it's showing a more realistic generation like this.
concurrencyDSLGenerator :: Gen CommandDSL
concurrencyDSLGenerator = frequency
    [ (5, SequentialCmd <$> generateMillisecondDelay)
    , (3, ParallelCmd   <$> generateMillisecondDelay)
    , (2, AsyncCmd      <$> generateMillisecondDelay)
    ]
 where
    -- | A delay from one millisecond to ten milliseconds.
    generateMillisecondDelay :: Gen Int
    generateMillisecondDelay = choose (1, 10)



