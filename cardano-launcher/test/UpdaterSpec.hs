{-# LANGUAGE ScopedTypeVariables #-}

module UpdaterSpec where

import           Cardano.Prelude

import           Prelude (String)
import           Test.Hspec (Spec, describe, it)
import           Test.Hspec.QuickCheck (prop)
import           Test.QuickCheck (Arbitrary (..), elements, (===))
import           Test.QuickCheck.Monadic (assert, monadicIO, run)

import           Cardano.Shell.Types (nullLogging)
import           Cardano.Shell.Update.Lib (RemoveArchiveAfterInstall (..),
                                           UpdateOSPlatform (..),
                                           UpdaterData (..), executeUpdater,
                                           isUpdaterRunOnUnix,
                                           isUpdaterRunOnWin,
                                           runDefaultUpdateProcess, runUpdater,
                                           updaterExistsToBool)


updaterSpec :: Spec
updaterSpec = describe "Update system" $ do
    it "should be successful" $ monadicIO $ do
        exitCode <- run $ runUpdater
            nullLogging
            DoNotRemoveArchiveAfterInstall
            runDefaultUpdateProcess
            testUpdaterData

        run . putTextLn . show $ exitCode
        assert $ exitCode == ExitSuccess

    prop "should return expected error" $ \(exitNum :: ExitNum) -> monadicIO $ do
        exitCode <- run $ runUpdater
            nullLogging
            DoNotRemoveArchiveAfterInstall
            (testRunCmd exitNum)
            testUpdaterData

        assert $ exitCode == (ExitFailure . getExitNum $ exitNum)

    prop "should handle update on WIN" $ \(updaterExists) ->
        updaterExistsToBool updaterExists ===
            isUpdaterRunOnWin (executeUpdater WinOS updaterExists testUpdaterData)

    prop "should handle update on *NIXs" $ \(updaterExists) ->
        updaterExistsToBool updaterExists ===
            isUpdaterRunOnUnix (executeUpdater UnixOS updaterExists testUpdaterData)


-- Won't work on windows
testUpdaterData :: UpdaterData
testUpdaterData =
    UpdaterData
        "bash"
        []
        "./test/testUpdater.sh"

testRunCmd :: ExitNum -> FilePath -> [String] -> IO ExitCode
testRunCmd (ExitNum num) _ _ = return $ ExitFailure num

newtype ExitNum = ExitNum {
    getExitNum :: Int
    } deriving Show

-- http://tldp.org/LDP/abs/html/exitcodes.html
instance Arbitrary ExitNum where
    arbitrary = ExitNum <$> elements [1, 2, 126, 127, 128, 130, 255]


