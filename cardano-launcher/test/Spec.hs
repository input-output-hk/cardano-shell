module Main where

import           Cardano.Prelude
import           LauncherSpec (launcherSpec)
import           Test.Hspec (describe, hspec)
import           UpdaterSpec (updaterSpec)

-- | Entry point for tests.
main :: IO ()
main = hspec $ do
    describe "Update spec" updaterSpec
    describe "Launcher spec" launcherSpec

