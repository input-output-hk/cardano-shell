module NodeIPCSpec
    ( nodeIPCSpec
    ) where

import           Cardano.Prelude

import           Test.Hspec (Spec, describe, it)
import           Test.QuickCheck.Monadic (assert, monadicIO, run)

import           NodeIPC.Example (exampleWithFD, exampleWithProcess)
import           NodeIPC.Lib (MsgOut (..))

nodeIPCSpec :: Spec
nodeIPCSpec =
    describe "Examples" $ do
      describe "exampleWithFD" $
          it "should return Started, Pong" $ monadicIO $ do
              (started, pong) <- run exampleWithFD
              assert $ started == Started
              assert $ pong    == Pong
      describe "exampleWithProcess" $
          it "should return Started, Pong" $ monadicIO $ do
              (started, pong) <- run exampleWithProcess
              assert $ started == Started
              assert $ pong    == Pong
