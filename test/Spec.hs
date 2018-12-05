{-# LANGUAGE Rank2Types #-}

module Main where

import           Cardano.Prelude

import           Control.Concurrent.Classy (MonadConc)

import           Test.Hspec (Spec, hspec, describe)

import           Test.DejaFu (deadlocksNever, exceptionsNever, abortsNever)
import           Test.Hspec.Contrib.HUnit (fromHUnitTest)
import           Test.HUnit.DejaFu (testDejafu)

import           Cardano.Shell.Lib (GeneralException (..), runApplication)

-- | Entry point for tests.
main :: IO ()
main = hspec spec

-- | Specification.
spec :: Spec
spec = do

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
    runApplicationSunnyDay = runApplication application
      where
        application :: IO ()
        application = pure ()

    -- | What happens when the application terminates exceptionally?
    runApplicationExceptional :: forall m. (MonadIO m, MonadConc m) => m ()
    runApplicationExceptional = runApplication application
      where
        application :: IO ()
        application = throwIO UnknownFailureException


