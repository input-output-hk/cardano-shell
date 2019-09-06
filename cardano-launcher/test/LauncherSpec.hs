{-# LANGUAGE ScopedTypeVariables #-}

module LauncherSpec where

import           Cardano.Prelude

import           Test.Hspec (Spec, describe, it)
import           Test.Hspec.QuickCheck (modifyMaxSuccess, prop)
import           Test.QuickCheck (Arbitrary (..), elements)
import           Test.QuickCheck.Monadic (assert, monadicIO, run)

import           Cardano.Shell.Launcher (DaedalusExitCodes (..),
                                         WalletRunner (..),
                                         UpdateRunner (..),
                                         handleDaedalusExitCode)

-- | The simple launcher spec.
launcherSpec :: Spec
launcherSpec = describe "Launcher system" $ modifyMaxSuccess (const 10000) $ do

    it "should return success" $ monadicIO $ do
        let walletExitCode = ExitCodeSuccess

        exitCode <- run $ handleDaedalusExitCode doNotUse doNotUse walletExitCode
        assert $ exitCode == ExitSuccess

    prop "should return failure" $ \(exitNum :: ExitCodeNumber) -> monadicIO $ do
        let exitCodeNumber = getExitCodeNumber exitNum
        let walletExitCode = ExitCodeOther exitCodeNumber

        exitCode <- run $ handleDaedalusExitCode doNotUse doNotUse walletExitCode
        assert $ exitCode == ExitFailure exitCodeNumber

    it "should restart launcher, normal mode" $ monadicIO $ do
        let walletExitCode      = RestartInGPUNormalMode
        let launcherFunction    = WalletRunner $ pure ExitSuccess

        exitCode <- run $ handleDaedalusExitCode doNotUse launcherFunction walletExitCode
        assert $ exitCode == ExitSuccess

    it "should restart launcher, safe mode" $ monadicIO $ do
        let walletExitCode      = RestartInGPUSafeMode
        let launcherFunction    = WalletRunner $ pure ExitSuccess

        exitCode <- run $ handleDaedalusExitCode doNotUse launcherFunction walletExitCode
        assert $ exitCode == ExitSuccess

    it "should run update, restart launcher, normal mode" $ monadicIO $ do
        let walletExitCode      = RunUpdate
        let updateFunction      = UpdateRunner $ pure ExitSuccess
        let launcherFunction    = WalletRunner $ pure ExitSuccess

        exitCode <- run $ handleDaedalusExitCode updateFunction launcherFunction walletExitCode
        assert $ exitCode == ExitSuccess

  where
    -- | A simple utility function so we don't have to pass panic around.
    doNotUse :: a
    doNotUse = panic "Should not be used!"

newtype ExitCodeNumber = ExitCodeNumber { getExitCodeNumber :: Int }
    deriving (Eq, Show)

-- http://tldp.org/LDP/abs/html/exitcodes.html
instance Arbitrary ExitCodeNumber where
    arbitrary = ExitCodeNumber <$> elements [1, 2, 126, 127, 128, 130, 255]
