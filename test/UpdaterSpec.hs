{-# LANGUAGE ScopedTypeVariables #-}

module UpdaterSpec where

import           Cardano.Prelude

import           Prelude (String)
import           Test.Hspec (Spec, describe, it)
import           Test.Hspec.QuickCheck (prop)
import           Test.QuickCheck (Arbitrary (..), elements)
import           Test.QuickCheck.Monadic (assert, monadicIO, run)

import           Cardano.Shell.Update.Lib (UpdateError (..), UpdaterData (..),
                                           runUpdater, runUpdater')

updaterSpec :: Spec
updaterSpec = describe "Update system" $ do
    it "should be successful" $ monadicIO $ do
        eExitCode <- run $ runUpdater testUpdaterData
        assert $ eExitCode == (Right ExitSuccess)

    it "should return error when updater is not found" $ monadicIO $ do
        eExitCode <- run $ runUpdater testUpdaterDataNoPath
        assert $ eExitCode == (Left UpdaterDoesNotExist)

    prop "should return expected error" $ \(exitNum :: ExitNum) -> monadicIO $ do
        eExitCode <- run $ runUpdater' (testRunCmd exitNum) testUpdaterData
        assert $ eExitCode == (Left . UpdateFailed . getExitNum $ exitNum)

testUpdaterData :: UpdaterData
testUpdaterData =
    UpdaterData
        "./test/testUpdater.sh"
        []
        ""

testUpdaterDataNoPath :: UpdaterData
testUpdaterDataNoPath =
    UpdaterData
        "This path does not exist"
        []
        ""

testRunCmd :: ExitNum -> FilePath -> [String] -> FilePath -> IO ExitCode
testRunCmd (ExitNum num) _ _ _ = return $ ExitFailure num

newtype ExitNum = ExitNum {
    getExitNum :: Int
    } deriving Show

-- http://tldp.org/LDP/abs/html/exitcodes.html
instance Arbitrary ExitNum where
    arbitrary = ExitNum <$> elements [1, 2, 126, 127, 128, 130, 255]
