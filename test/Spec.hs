module Main where

import           Cardano.Prelude

import           Test.Hspec (hspec, describe)

import           DhallConfigSpec (dhallConfigSpec)

main :: IO ()
main = hspec $ do
    describe "Dhall configurations" dhallConfigSpec
