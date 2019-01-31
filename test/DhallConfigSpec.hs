{-# LANGUAGE ScopedTypeVariables #-}

module DhallConfigSpec
    ( dhallConfigSpec
    , mkConfigSpec
    ) where

import           Cardano.Prelude

import           Control.Exception.Safe (tryAny)
import           Dhall (Inject (..), Interpret (..), auto, embed, inject, input)
import           Dhall.Core (pretty)
import           Test.Hspec (Spec, describe)
import           Test.Hspec.QuickCheck (modifyMaxSuccess, prop)
import           Test.QuickCheck (Property)
import           Test.QuickCheck.Monadic (assert, monadicIO, run)

import           Cardano.Shell.Configuration.Lib (mkBlockchainConfig,
                                                  mkInstallerConfig, mkLauncher,
                                                  mkLoggingConfig,
                                                  mkNetworkConfig, mkOSConfig,
                                                  mkTopology, mkWalletConfig)
import           Cardano.Shell.Configuration.Types (BlockchainConfig, Cluster,
                                                    ClusterConfig,
                                                    InstallerConfig, Launcher,
                                                    LoggingConfig,
                                                    NetworkConfig, NodeArgs, OS,
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

        prop "NetworkConfig" $
            \(networkConfig :: NetworkConfig) -> testRoundTrip networkConfig

        prop "BlockchainConfig" $
            \(blockchainConfig :: BlockchainConfig) -> testRoundTrip blockchainConfig

        prop "WalletConfig" $
            \(walletConfig :: WalletConfig) -> testRoundTrip walletConfig

        prop "LoggingConfig" $
            \(loggingConfig :: LoggingConfig) -> testRoundTrip loggingConfig
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

mkConfigSpec :: Spec
mkConfigSpec = describe "Cardano configurations" $ do
    describe "mkLauncher" $
        prop "should be able to create launcher configuration" $
            \(os :: OS) (cluster :: Cluster) -> monadicIO $ do
                eLauncherConfig <- run $ tryAny $ mkLauncher os cluster
                assert $ isRight eLauncherConfig

    describe "mkTopology" $
        prop "should be able to create topology configuration" $
            \(cluster :: Cluster) -> monadicIO $ do
                eTopologyConfig <- run $ tryAny $ mkTopology cluster
                assert $ isRight eTopologyConfig

    describe "mkOSConfig" $
        prop "should be able to create os configuration" $
            \(os :: OS) (cluster :: Cluster) -> monadicIO $ do
                eOsConfig <- run $ tryAny $ mkOSConfig os cluster
                assert $ isRight eOsConfig

    describe "mkInstallerConfig" $
        prop "should be able to create installer configuration" $
            \(os :: OS) (cluster :: Cluster) -> monadicIO $ do
                eInstallerConfig <- run $ tryAny $ mkInstallerConfig os cluster
                assert $ isRight eInstallerConfig

    describe "mkBlockchainConfig" $
        prop "should be able to create blockchain configuration" $
            \(os :: OS) (cluster :: Cluster) -> monadicIO $ do
                eBlockchainConfig <- run $ tryAny $ mkBlockchainConfig os cluster
                assert $ isRight eBlockchainConfig

    describe "mkLoggingConfig" $
        prop "should be able to create logging configuration" $
            \(os :: OS) (cluster :: Cluster) -> monadicIO $ do
                eLoggingConfig <- run $ tryAny $ mkLoggingConfig os cluster
                assert $ isRight eLoggingConfig

    describe "mkNetworkConfig" $
        prop "should be able to create network configuration" $
            \(os :: OS) (cluster :: Cluster) -> monadicIO $ do
                eNetworkConfig <- run $ tryAny $ mkNetworkConfig os cluster
                assert $ isRight eNetworkConfig

    describe "mkWalletConfig" $
        prop "should be able to create wallet configuration" $
            \(os :: OS) (cluster :: Cluster) -> monadicIO $ do
                eWalletConfig <- run $ tryAny $ mkWalletConfig os cluster
                assert $ isRight eWalletConfig
