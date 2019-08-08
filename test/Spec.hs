{-# LANGUAGE Rank2Types       #-}
{-# LANGUAGE TypeApplications #-}

module Main where

import           Cardano.Prelude

import           Test.Hspec (describe, hspec)

import           NodeIPCSMSpec (nodeIPCSMSpec)
import           NodeIPCSpec (nodeIPCSpec)
import qualified DaedalusIPCSpec as DaedalusIPC
import           UpdaterSpec (updaterSpec)

-- | Entry point for tests.
main :: IO ()
main = hspec $ do
    describe "NodeIPC state machine" nodeIPCSMSpec
    describe "NodeIPC" nodeIPCSpec
    describe "DaedalusIPC" DaedalusIPC.spec
    describe "Update system" updaterSpec

