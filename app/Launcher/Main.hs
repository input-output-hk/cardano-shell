{-# LANGUAGE CPP        #-}
{-# LANGUAGE LambdaCase #-}

module Main where

import           Cardano.Prelude

import           System.Directory
import           System.FilePath

import           Formatting (bprint, build, string)
import           Formatting.Buildable (Buildable (..))

import Control.Exception.Safe

{-

-- TODO(KS): Move this to another module.
-}

import           Cardano.X509.Configuration
import           Data.X509.Extra

import qualified System.Process as Process

#ifndef mingw32_HOST_OS
import           System.Posix.Signals (sigKILL, signalProcess)
import qualified System.Process.Internals as Process
#else
import qualified System.Win32.Process as Process
#endif

main :: IO ()
main = return ()


newtype X509ToolPath = X509ToolPath { getX509ToolPath :: FilePath }
    deriving (Eq, Show)

newtype TLSPath = TLSPath { getTLSFilePath :: FilePath }
    deriving (Eq, Show)




createProc :: Process.StdStream -> FilePath -> [Text] -> Process.CreateProcess
createProc stdStream path args =
    (Process.proc path (map toS args))
            { Process.std_in = Process.CreatePipe
            , Process.std_out = stdStream
            , Process.std_err = stdStream
            }

data LauncherExceptions
    = CannotGenerateTLS
    deriving (Eq, Show)


instance Exception LauncherExceptions

instance Buildable LauncherExceptions where
    build = \case
        CannotGenerateTLS -> bprint "Couldn't generate TLS certificates; Daedalus wallet won't work without TLS. Please check your configuration and make sure you aren't already running an instance of Daedalus wallet."



--data ExternalDependencies = ExternalDependencies
logInfo :: Text -> IO ()
logInfo = putTextLn

logError :: Text -> IO ()
logError = putTextLn

-- | Generation of the TLS certificates.
generateTlsCertificates :: X509ToolPath -> TLSPath -> IO ()
generateTlsCertificates (X509ToolPath x509ToolPath) (TLSPath tlsPath) = do

    let outDirectories :: DirConfiguration -- ^ Output directories configuration
        outDirectories = panic "!"

    let configKey :: ConfigurationKey -- ^ Configuration key within the config file
        configKey = panic "!"

    let configFile :: FilePath
        configFile = panic "!"

    tlsConfig <-
        decodeConfigFile configKey configFile

    (caDesc, descs) <-
        fromConfiguration tlsConfig outDirectories genRSA256KeyPair <$> genRSA256KeyPair

    let caName =
            certFilename caDesc

    let (serverHost, serverPort) = ("", "")
            --(NonEmpty.head $ serverAltNames $ tlsServer tlsConfig, "")

    (caKey, caCert) <-
        genCertificate caDesc

    case certOutDir caDesc of
        Nothing  -> return ()
        Just dir -> writeCredentials (dir </> caName) (caKey, caCert)

    forM_ descs $ \desc -> do
        (key, cert) <- genCertificate desc
        failIfReasons =<< validateCertificate
            caCert
            (certChecks desc)
            (serverHost, serverPort)
            cert
        writeCredentials (certOutDir desc </> certFilename desc) (key, cert)
        writeCertificate (certOutDir desc </> caName) caCert

    -- WTF?
    --alreadyExists <- and <$> mapM (liftIO . doesFileExist) [tlsPath]

    --let tlsServer = tlsPath </> "server"
    --let tlsClient = tlsPath </> "client"

    --unless alreadyExists $ do
    --    logInfo $ "Generating new TLS certificates in " <> show tlsPath

    --    let process = createProc Process.Inherit x509ToolPath
    --            [ "--server-out-dir"     , show tlsServer
    --            , "--clients-out-dir"    , show tlsClient
    --            , "--configuration-file" , show cfoFilePath
    --            , "--configuration-key"  , cfoKey
    --            ]

    --    exitCode <- liftIO $ do
    --        createDirectoryIfMissing True tlsServer
    --        createDirectoryIfMissing True tlsClient
    --        phvar <- newEmptyMVar
    --        system' phvar process mempty ECertGen

    --    when (exitCode /= ExitSuccess) $ do
    --        logError "Couldn't generate TLS certificates for Wallet"
    --        liftIO . throwM $ CannotGenerateTLS
