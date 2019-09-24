module DaedalusIPCSpec
    ( spec
    ) where

import           Cardano.Prelude

import           System.Exit (ExitCode (..))
import           System.Process ( createProcess, proc, waitForProcess)
import           Test.Hspec (Spec, describe, it, shouldReturn)

spec :: Spec
spec = describe "DaedalusIPC" $ do
    it "should reply with the port when asked" $ do
        let port = 42 :: Int
        let testScript = "test/js/mock-daedalus.js"
        (_, _, _, ph) <- createProcess (proc "node" [testScript, show port])
        waitForProcess ph `shouldReturn` ExitSuccess
