module Main where

import           Cardano.Prelude

import           Test.Hspec (describe, hspec)

import           UpdaterSpec (updaterSpec)

-- | Entry point for tests.
main :: IO ()
main = hspec $ do
    describe "Update system" updaterSpec

