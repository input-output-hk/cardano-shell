{-# LANGUAGE Rank2Types #-}

module Main where

import           Cardano.Prelude

import           Control.Concurrent.Classy (MonadConc)
import           DhallConfigSpec (dhallConfigSpec)

import           Test.DejaFu (abortsNever, deadlocksNever, exceptionsNever)
import           Test.Hspec (Spec, describe, hspec)
import           Test.Hspec.Contrib.HUnit (fromHUnitTest)
import           Test.HUnit.DejaFu (testDejafu)

import           Cardano.Shell.Lib (AllFeaturesInitFunction,
                                    GeneralException (..), runApplication)

-- | Entry point for tests.
main :: IO ()
main = hspec $ do
    describe "App should have no concurrency issues" validConcurrencySpec
    describe "Dhall configurations" dhallConfigSpec

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
        application = throwIO UnknownFailureException

    -- | We actually need to improve this and add arbitrary @CardanoFeature@s
    -- and add concurrency primitives of appropriate depth to check we have it working.
    -- It used to work with the test features that were moved into the executable since
    -- we wanted to split the project.
    cardanoFeaturesInit :: AllFeaturesInitFunction
    cardanoFeaturesInit = \_ _ -> pure []



