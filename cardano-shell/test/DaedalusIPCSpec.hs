module DaedalusIPCSpec
    ( spec
    ) where

import           Cardano.Prelude

import           Test.Hspec (Spec, describe, it, pending)

spec :: Spec
spec = describe "DaedalusIPC" $ do
    it "should reply with the port when asked" $ do
        pending

--spec = describe "DaedalusIPC" $ do
--    it "should reply with the port when asked" $ do
--        let port = 42 :: Int
--        let testScript = "cardano-shell/test/js/mock-daedalus.js"
--        (_, _, _, ph) <- createProcess (proc "node" [testScript, show port])
--        waitForProcess ph `shouldReturn` ExitSuccess
