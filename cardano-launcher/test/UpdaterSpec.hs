{-# LANGUAGE ScopedTypeVariables #-}

module UpdaterSpec where

import           Cardano.Prelude

import           Prelude (String)
import           Test.Hspec (Spec, describe, it)
import           Test.Hspec.QuickCheck (prop)
import           Test.QuickCheck (Arbitrary (..), elements)
import           Test.QuickCheck.Monadic (assert, monadicIO, run)

import           Cardano.Shell.Update.Lib (UpdaterData (..), runUpdater,
                                           runUpdater')

updaterSpec :: Spec
updaterSpec = describe "Update system" $ do
    it "should be successful" $ monadicIO $ do
        exitCode <- run $ runUpdater testUpdaterData
        assert $ exitCode == ExitSuccess

    prop "should return expected error" $ \(exitNum :: ExitNum) -> monadicIO $ do
        exitCode <- run $ runUpdater' (testRunCmd exitNum) testUpdaterData
        assert $ exitCode == (ExitFailure . getExitNum $ exitNum)
-- Won't work on windows
testUpdaterData :: UpdaterData
testUpdaterData =
    UpdaterData
        "./cardano-launcher/test/testUpdater.sh"
        []
        Nothing
        ""

testRunCmd :: ExitNum -> FilePath -> [String] -> FilePath -> IO ExitCode
testRunCmd (ExitNum num) _ _ _ = return $ ExitFailure num

newtype ExitNum = ExitNum {
    getExitNum :: Int
    } deriving Show

-- http://tldp.org/LDP/abs/html/exitcodes.html
instance Arbitrary ExitNum where
    arbitrary = ExitNum <$> elements [1, 2, 126, 127, 128, 130, 255]
