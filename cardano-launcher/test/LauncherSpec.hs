{-# LANGUAGE ScopedTypeVariables #-}

module LauncherSpec where

import           Cardano.Prelude

import           Data.Yaml (ParseException (..), Value (..), decodeFileEither,
                            encodeFile)
import           Test.Hspec (Spec, describe, it)
import           Test.Hspec.QuickCheck
import           Test.QuickCheck (Arbitrary (..), elements)
import           Test.QuickCheck.Monadic (assert, monadicIO, run)

import           System.Directory (doesFileExist, getCurrentDirectory,
                                   setCurrentDirectory)
import           System.Environment (setEnv, unsetEnv)
import           System.FilePath ((</>))
import           System.IO.Temp (withSystemTempDirectory)

import           Cardano.Shell.CLI (LauncherOptionPath (..),
                                    decodeLauncherOption, setupEnvVars)
import           Cardano.Shell.Configuration (ConfigurationOptions (..),
                                              LauncherOptions (..),
                                              setWorkingDirectory)
import           Cardano.Shell.Launcher (DaedalusExitCode (..),
                                         RestartRunner (..), TLSError (..),
                                         TLSPath (..), UpdateRunner (..),
                                         generateTlsCertificates,
                                         handleDaedalusExitCode)
import           Cardano.Shell.Launcher.Types (nullLogging)

-- | The simple launcher spec.
launcherSpec :: Spec
launcherSpec = do
    configurationSpec
    launcherSystemSpec
    setWorkingDirectorySpec
    generateTLSCertSpec

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
--
-- TODO(KS): Currently moving the tests to check for the Jormungandr config files
-- since this has (sudden) priority, otherwise we should sync this up for all config
-- files.
launcherDatas :: [FilePath]
launcherDatas =
    [ "jormungandr/launcher-config-qa.linux.yaml"
    , "jormungandr/launcher-config-qa.windows.yaml"
    ]

--    [ "launcher-config-mainnet.linux.yaml"
--    , "launcher-config-staging.linux.yaml"
--    , "launcher-config-testnet.linux.yaml"
--    , "launcher-config-mainnet.macos64.yaml"
--    , "launcher-config-staging.macos64.yaml"
--    , "launcher-config-testnet.macos64.yaml"
--    , "launcher-config.demo.yaml"
--    , "launcher-config-demo.windows.yaml"
--    ]

-- | Test that given configuration file can be parsed as @LauncherOptions@
testLauncherParsable :: FilePath -> Spec
testLauncherParsable configFilePath = describe "Launcher configuration" $ do
    it "should exist" $ monadicIO $ do
        doesConfigFileExist <- run $ doesFileExist (configFullFilePath configFilePath)
        assert doesConfigFileExist

    it ("should be able to parse configuration file: " <> configFilePath) $ monadicIO $ do
        eParsedConfigFile <- run $ decodeFileEither (configFullFilePath configFilePath)
        run $ putTextLn $ show eParsedConfigFile
        assert $ isRight (eParsedConfigFile :: Either ParseException LauncherOptions)

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

configurationSpec :: Spec
configurationSpec = describe "configuration files" $ modifyMaxSuccess (const 1) $ do
    describe "Launcher parser" $ do
        mapM_ testLauncherParsable launcherDatas
    describe "getLauncherOptions" $ do
        mapM_ testGetLauncherOption launcherDatas

        it "should fail due to passing wrong file path" $ monadicIO $ do
            eLauncherOption <- run $ do
                -- Path to the launcher file is incorrect
                let launcherOptionPath = LauncherOptionPath "this will fail"
                withSystemTempDirectory "test-XXXXXX" $ \tmpDir ->
                    withSetEnvs launcherOptionPath tmpDir $ decodeLauncherOption nullLogging launcherOptionPath
            assert $ isLeft eLauncherOption

        it "should fail due to missing env vars" $ monadicIO $ do
            eLauncherOption <- run $ do
                let launcherOptionPath = LauncherOptionPath (configFullFilePath "launcher-config-mainnet.linux.yaml")
                -- Not environment variables are set!
                decodeLauncherOption nullLogging launcherOptionPath
            assert $ isLeft eLauncherOption

        it "should fail due to failing to convert to LauncherOption" $ monadicIO $ do
            eLauncherOption <- run $ do
                withSystemTempDirectory "test-XXXXXX" $ \tmpDir -> do
                    -- Create invalid yaml file
                    let val = String "this is not launcher option"
                    let yamlPath = tmpDir </> "launcher.yaml"
                    encodeFile yamlPath val
                    let launcherOptionPath = LauncherOptionPath yamlPath
                    withSetEnvs launcherOptionPath tmpDir $ decodeLauncherOption nullLogging launcherOptionPath
            assert $ isLeft eLauncherOption

-- | Test that env var substitution works as expected on actual config files
testGetLauncherOption :: FilePath -> Spec
testGetLauncherOption configPath = it ("should be able to perform env substitution on config: " <> configPath) $ monadicIO $ do
    eLauncherOption <- run $ do
        let launcherOptionPath = LauncherOptionPath (configFullFilePath configPath)
        withSystemTempDirectory "test-XXXXXX" $ \tmpDir ->
            withSetEnvs launcherOptionPath tmpDir $ decodeLauncherOption nullLogging launcherOptionPath
    run $ putTextLn $ show eLauncherOption
    assert $ isRight eLauncherOption

configFullFilePath :: FilePath -> FilePath
configFullFilePath configPath = "./configuration/launcher/" <> configPath

-- | Set all the envrionment variables that are needed to perform env var
-- substituion then unset them afterwards
withSetEnvs :: LauncherOptionPath -> FilePath -> IO a -> IO a
withSetEnvs path homePath action =
    bracket
        setEnvs
        (\_ -> unsetEnvs)
        (\_ -> action)
  where
    setEnvs :: IO ()
    setEnvs = do
        -- Scripts that runs the launcher sets DAEDALUS_CONFIG variable
        setEnv "DAEDALUS_CONFIG" "Foo"
        -- Every operating system have HOME variable set
        setEnv "HOME" homePath
        setEnv "APPDATA" homePath
        setupEnvVars path

    unsetEnvs :: IO ()
    unsetEnvs = mapM_ unsetEnv
        [ "DAEDALUS_CONFIG"
        , "HOME"
        , "XDG_DATA_HOME"
        , "DAEDALUS_INSTALL_DIRECTORY"
        , "LAUNCHER_CONFIG"
        ]

generateTLSCertSpec :: Spec
generateTLSCertSpec = describe "TLS certificate generation" $ modifyMaxSuccess (const 1) $ do
    it "should generate tls certificates as expected" $ monadicIO $ do
        (eTLS, filesExist) <- run $ withSystemTempDirectory "tls-test" $ \tmpDir -> do
            let tlsPath = TLSPath $ tmpDir
            eTLS <- generateTlsCertificates nullLogging defaultConfigurationOptions tlsPath
            filesExist <- and <$> mapM doesFileExist (tlsFiles tmpDir)
            return (eTLS, filesExist)
        assert $ isRight eTLS
        assert filesExist

    it "should throw error when TLS path doesn't exist" $ monadicIO $ do
        let invalidTLSPath = TLSPath $ "this directory does not exist"
        eTLS <- run $ generateTlsCertificates nullLogging defaultConfigurationOptions invalidTLSPath
        assert $ eTLS == Left (TLSDirectoryNotFound "this directory does not exist")

    it "should throw error when invalid config file path was given" $ monadicIO $ do
        let invalidConfigPath = "This path doesn't exist"
        (eTLS, filesExist) <- run $ withSystemTempDirectory "tls-test" $ \tmpDir -> do
            let tlsPath = TLSPath $ tmpDir
            let invalidConfigurationOption = defaultConfigurationOptions { cfoFilePath = invalidConfigPath }
            eTLS <- generateTlsCertificates nullLogging invalidConfigurationOption tlsPath
            filesExist <- and <$> mapM doesFileExist (tlsFiles tmpDir)
            return (eTLS, filesExist)
        assert $ eTLS == Left (CertConfigNotFound invalidConfigPath)
        assert $ not filesExist

    it "should throw error when invalid key was given" $ monadicIO $ do
        let invalidKey = "This is invalid key"
        (eTLS, filesExist) <- run $ withSystemTempDirectory "tls-test" $ \tmpDir -> do
            let tlsPath = TLSPath $ tmpDir
            let invalidConfigurationOption = defaultConfigurationOptions { cfoKey = invalidKey}
            eTLS <- generateTlsCertificates nullLogging invalidConfigurationOption tlsPath
            filesExist <- and <$> mapM doesFileExist (tlsFiles tmpDir)
            return (eTLS, filesExist)
        assert $ eTLS == Left (InvalidKey invalidKey)
        assert $ not filesExist
  where

    defaultConfigurationOptions :: ConfigurationOptions
    defaultConfigurationOptions = ConfigurationOptions {
        cfoFilePath = "./configuration/cert-configuration.yaml",
        cfoKey = "dev",
        cfoSystemStart = Nothing,
        cfoSeed = Nothing
    }

    tlsFiles :: FilePath -> [FilePath]
    tlsFiles path =

        let clientFiles :: [FilePath]
            clientFiles = map (\file -> path </> "client" </> file)
                ["ca.crt", "client.crt", "client.key", "client.pem"]

            serverFiles :: [FilePath]
            serverFiles = map (\file -> path </> "server" </> file)
                ["ca.crt", "server.crt", "server.key", "server.pem"]

        in clientFiles <> serverFiles
