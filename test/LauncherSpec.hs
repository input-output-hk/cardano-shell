module LauncherSpec where

import           Cardano.Prelude

import           Data.Yaml (ParseException (..), decodeFileEither)
import           Test.Hspec (Spec, describe, it)
import           Test.Hspec.QuickCheck
import           Test.QuickCheck.Monadic (assert, monadicIO, run)

import           Cardano.Shell.Launcher (LauncherOptions (..))

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
testLauncherParsable configFilePath = it
    ("Should be able to parse configuration file: " <> configFilePath) $ monadicIO $ do
        eParsedConfigFile <- run $ decodeFileEither $ "./configuration/launcher/" <> configFilePath
        assert $ isRight (eParsedConfigFile :: Either ParseException LauncherOptions)

-- | Launcher spec
launcherSpec :: Spec
launcherSpec = describe "configuration files" $ modifyMaxSuccess (const 1) $
     mapM_ testLauncherParsable launcherDatas
