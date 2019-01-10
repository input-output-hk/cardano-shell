{-# LANGUAGE ScopedTypeVariables #-}

module DhallConfigSpec
    ( dhallConfigSpec
    ) where

import           Cardano.Prelude

import           Dhall (Inject (..), Interpret (..), auto, embed, inject, input)
import           Dhall.Core (pretty)
import           Test.Hspec (Spec, describe)
import           Test.Hspec.QuickCheck (modifyMaxSuccess, prop)
import           Test.QuickCheck (Property)
import           Test.QuickCheck.Monadic (assert, monadicIO, run)

import           Cardano.Shell.Configuration.Types (BlockchainConfig,
                                                    ClusterConfig,
                                                    InstallerConfig, Launcher,
                                                    LoggingConfig,
                                                    NetworkConfig, NodeArgs,
                                                    OSConfig, Param,
                                                    WalletConfig)

dhallConfigSpec :: Spec
dhallConfigSpec =
    describe "should be able to perform serialization roundtrip on" $ modifyMaxSuccess (const 200) $ do
        prop "NodeArgs" $
            \(nodeArgs :: NodeArgs) -> testRoundTrip nodeArgs

        prop "Launcher" $
            \(launcher :: Launcher) -> testRoundTrip launcher

        prop "Installer Config" $
            \(installerConfig :: InstallerConfig) -> testRoundTrip installerConfig

        prop "OSConfig" $
            \(osConfig :: OSConfig) -> testRoundTrip osConfig

        prop "ClusterConfig" $
            \(clusterConfig :: ClusterConfig) -> testRoundTrip clusterConfig

        prop "NodeArgs" $
            \(nodeArgs :: NodeArgs) -> testRoundTrip nodeArgs

        prop "Param" $
            \(paths :: Param) -> testRoundTrip paths

        prop "BlockchainConfig" $
           \(blockchainConfig :: BlockchainConfig) -> testRoundTrip blockchainConfig

        prop "LoggingConfig" $
            \(loggingConfig :: LoggingConfig) -> testRoundTrip loggingConfig

        prop "NetworkConfig" $
            \(networkConfig :: NetworkConfig) -> testRoundTrip networkConfig

        prop "WalletConfig" $
            \(walletConfig :: WalletConfig) -> testRoundTrip walletConfig
  where
    testRoundTrip :: (Inject a, Interpret a, Eq a) => a -> Property
    testRoundTrip dhallConfig = monadicIO $ do
        isSameData <- run $ runRoundTrip dhallConfig

        assert isSameData
      where
        runRoundTrip :: (Inject a, Interpret a, Eq a) => a -> IO Bool
        runRoundTrip someData = do
            roundTrippedData <- input auto $ pretty $ embed inject someData
            return $ someData == roundTrippedData
