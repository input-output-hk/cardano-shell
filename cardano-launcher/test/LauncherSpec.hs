{-# LANGUAGE ScopedTypeVariables #-}

module LauncherSpec where

import           Cardano.Prelude

import           Data.Yaml (ParseException (..), decodeFileEither)
import           Test.Hspec (Spec, describe, it)
import           Test.Hspec.QuickCheck
import           Test.QuickCheck (Arbitrary (..), elements)
import           Test.QuickCheck.Monadic (assert, monadicIO, run)

import           System.Directory (doesFileExist, getCurrentDirectory,
                                   setCurrentDirectory)
import           System.IO.Temp (withSystemTempDirectory)

import           Cardano.Shell.Launcher (DaedalusExitCode (..),
                                         LauncherOptions (..),
                                         RestartRunner (..), UpdateRunner (..),
                                         handleDaedalusExitCode,
                                         setWorkingDirectory)

-- | The simple launcher spec.
launcherSpec :: Spec
launcherSpec = do
    configurationSpec
    launcherSystemSpec
    setWorkingDirectorySpec

-- | The launcher system spec.
launcherSystemSpec :: Spec
launcherSystemSpec =
    describe "Launcher system" $ modifyMaxSuccess (const 10000) $ do

        it "should return success" $ monadicIO $ do
            let walletExitCode = ExitCodeSuccess

            exitCode <- run $ handleDaedalusExitCode doNotUse doNotUse walletExitCode
            assert $ exitCode == ExitCodeSuccess

        prop "should return failure" $ \(exitNum :: ExitCodeNumber) -> monadicIO $ do
            let exitCodeNumber = getExitCodeNumber exitNum
            let walletExitCode = ExitCodeFailure exitCodeNumber

            exitCode <- run $ handleDaedalusExitCode doNotUse doNotUse walletExitCode
            assert $ exitCode == ExitCodeFailure exitCodeNumber

        it "should restart launcher, normal mode" $ monadicIO $ do
            let walletExitCode      = RestartInGPUNormalMode
            let launcherFunction    = RestartRunner $ \_wm -> pure ExitSuccess

            exitCode <- run $ handleDaedalusExitCode doNotUse launcherFunction walletExitCode
            assert $ exitCode == ExitCodeSuccess

        it "should restart launcher, safe mode" $ monadicIO $ do
            let walletExitCode      = RestartInGPUSafeMode
            let launcherFunction    = RestartRunner $ \_wm -> pure ExitSuccess

            exitCode <- run $ handleDaedalusExitCode doNotUse launcherFunction walletExitCode
            assert $ exitCode == ExitCodeSuccess

        it "should run update, restart launcher, normal mode" $ monadicIO $ do
            let walletExitCode      = RunUpdate
            let updateFunction      = UpdateRunner $ pure ExitSuccess
            let launcherFunction    = RestartRunner $ \_wm -> pure ExitSuccess

            exitCode <- run $ handleDaedalusExitCode updateFunction launcherFunction walletExitCode
            assert $ exitCode == ExitCodeSuccess

  where
    -- | A simple utility function so we don't have to pass panic around.
    doNotUse :: a
    doNotUse = panic "Should not be used!"

newtype ExitCodeNumber = ExitCodeNumber { getExitCodeNumber :: Int }
    deriving (Eq, Show)

-- http://tldp.org/LDP/abs/html/exitcodes.html
instance Arbitrary ExitCodeNumber where
    arbitrary = ExitCodeNumber <$> elements [1, 2, 126, 127, 128, 130, 255]

-- | List of files we want to test on
-- These are config files downloaded from Daedalus CI
--
-- Ideally, you want to test with the config file generated from Daedalus CI
-- but setting it up will be very tricky (credentials, etc.)
launcherDatas :: [FilePath]
launcherDatas =
    [ "launcher-config-mainnet.linux.yaml"
    , "launcher-config-staging.linux.yaml"
    , "launcher-config-testnet.linux.yaml"
    , "launcher-config-mainnet.macos64.yaml"
    , "launcher-config-staging.macos64.yaml"
    , "launcher-config-testnet.macos64.yaml"
    ]

-- | Test that given configuration file can be parsed as @LauncherOptions@
testLauncherParsable :: FilePath -> Spec
testLauncherParsable configFilePath = describe "Launcher configuration" $ do

    it "should exist" $ monadicIO $ do

        doesConfigFileExist     <- run $ doesFileExist configFullFilePath
        assert doesConfigFileExist

    it ("should be able to parse configuration file: " <> configFilePath) $ monadicIO $ do

        eParsedConfigFile       <- run $ decodeFileEither configFullFilePath
        assert $ isRight (eParsedConfigFile :: Either ParseException LauncherOptions)

  where
    configFullFilePath :: FilePath
    configFullFilePath = "./configuration/launcher/" <> configFilePath

-- | Launcher spec
configurationSpec :: Spec
configurationSpec = describe "configuration files" $ modifyMaxSuccess (const 1) $
     mapM_ testLauncherParsable launcherDatas

setWorkingDirectorySpec :: Spec
setWorkingDirectorySpec = describe "Set working directory" $ do
    it "Should return true and set working directory to the directory specified" $ monadicIO $ do
        (done, destination, moved) <- run $ bracket
            getCurrentDirectory
            setCurrentDirectory
            (\_ -> do
                withSystemTempDirectory "test" $ \filePath -> do
                    done <- setWorkingDirectory filePath
                    moved <- getCurrentDirectory
                    return (done, filePath, moved)
            )
        assert $ done
        assert $ destination == moved

    it "Should return false if non-existing directory was given" $ monadicIO $ do
        (done, before, after) <- run $ do
            before <- getCurrentDirectory
            done <- setWorkingDirectory "this directory does not exist"
            after <- getCurrentDirectory
            return (done, before, after)
        assert $ not done
        assert $ before == after