{-# LANGUAGE OverloadedStrings, RecordWildCards, LambdaCase, ScopedTypeVariables #-}

import Turtle hiding (option)
import Prelude hiding (FilePath)
import qualified Filesystem.Path.CurrentOS as FP
import Control.Monad.Trans.Maybe
import Control.Exception
import qualified Data.Text as T
import Safe
import System.Exit (exitWith)
import Options.Applicative

data BuildkiteEnv = BuildkiteEnv
  { bkBuildNum :: Int
  , bkPipeline :: Text
  , bkBranch   :: Text
  } deriving (Show)

data CICacheConfig = CICacheConfig
  { ccMaxSize    :: Maybe Text
  , ccBucket     :: Text
  , ccRegion     :: Maybe Text
  , ccPrefix     :: Text
  , ccBranch     :: Text
  , ccBaseBranch :: Text
  } deriving (Show)

data RebuildOpts = RebuildOpts
  { optBuildDirectory :: Maybe FilePath
  , optBaseBranch :: Text
  } deriving (Show)

rebuildOpts :: Parser RebuildOpts
rebuildOpts = RebuildOpts <$> optional buildDir <*> baseBranch
  where
    buildDir = option (FP.decodeString <$> str) (long "build-dir" <> metavar "DIR" <> help "Copy sources to directory before building")
    baseBranch = option str ( long "base-branch" <> value "master" <> showDefault <> help "Fallback base branch for cache-s3" )

parseOpts :: IO RebuildOpts
parseOpts = execParser opts
  where opts = info (rebuildOpts <**> helper)
          ( fullDesc <> progDesc "Build cardano-sl project with stack in Buildkite" )

main :: IO ()
main = do
  RebuildOpts{..} <- parseOpts
  awsCreds
  bk <- getBuildkiteEnv
  maybe (pure ()) setupBuildDirectory optBuildDirectory
  cacheConfig <- getCacheConfig bk optBaseBranch
  cacheDownloadStep cacheConfig
  buildResult <- buildStep
  cacheUploadStep cacheConfig
  exitWith buildResult

buildStep :: IO ExitCode
buildStep = do
  echo "+++ Build and test"
  build .&&. test
  where
    cfg = ["--dump-logs", "--color", "always"]
    stackBuild args = run "stack" $ cfg ++ ["build", "--fast"] ++ args
    buildArgs = ["--bench", "--no-run-benchmarks", "--no-haddock-deps"]
    buildAndTest = stackBuild $ ["--tests"] ++ buildArgs
    build = stackBuild $ ["--no-run-tests"] ++ buildArgs
    test = stackBuild ["--test", "--jobs", "1"]

-- buildkite agents have S3 creds installed, but under different names
awsCreds :: IO ()
awsCreds = mapM_ (uncurry copy) things
  where
    copy src dst = need src >>= maybe (pure ()) (export dst)
    things = [ ( "BUILDKITE_S3_ACCESS_KEY_ID"
               , "AWS_ACCESS_KEY_ID")
             , ( "BUILDKITE_S3_SECRET_ACCESS_KEY"
               , "AWS_SECRET_ACCESS_KEY")
             , ( "BUILDKITE_S3_DEFAULT_REGION"
               , "AWS_DEFAULT_REGION")
             ]

getBuildkiteEnv :: IO (Maybe BuildkiteEnv)
getBuildkiteEnv = runMaybeT $ do
  bkBuildNum <- MaybeT $ needRead "BUILDKITE_BUILD_NUMBER"
  bkPipeline <- MaybeT $ need "BUILDKITE_PIPELINE_SLUG"
  bkBranch   <- MaybeT $ need "BUILDKITE_BRANCH"
  pure BuildkiteEnv{..}

needRead :: Read a => Text -> IO (Maybe a)
needRead v = (>>= readMay) . fmap T.unpack <$> need v

getCacheConfig :: Maybe BuildkiteEnv -> Text -> IO (Either Text CICacheConfig)
getCacheConfig Nothing _ = pure (Left "BUILDKITE_* environment variables are not set")
getCacheConfig (Just BuildkiteEnv{..}) ccBaseBranch = do
  ccMaxSize <- need "CACHE_S3_MAX_SIZE"
  ccRegion <- need "AWS_REGION"
  need "S3_BUCKET" >>= \case
    Just ccBucket -> pure (Right CICacheConfig{ccBranch=bkBranch, ccPrefix=bkPipeline, ..})
    Nothing -> pure (Left "S3_BUCKET environment variable is not set")

cacheDownloadStep :: Either Text CICacheConfig -> IO ()
cacheDownloadStep cacheConfig = do
  echo "--- CI Cache Download"
  case cacheConfig of
    Right cfg -> restoreCICache cfg `catch`
      \ (ex :: IOException) -> do
        eprintf ("Failed to download CI cache: "%w%"\nContinuing anyway...\n") ex
    Left ex -> eprintf ("Not using CI cache because "%s%"\n") ex

cacheUploadStep :: Either Text CICacheConfig -> IO ()
cacheUploadStep cacheConfig = do
  echo "--- CI Cache Upload"
  case cacheConfig of
    Right cfg -> saveCICache cfg `catch`
      \ (ex :: IOException) -> do
        eprintf ("Failed to upload CI cache: "%w%"\n") ex
    Left _ -> printf "CI cache not configured.\n"

restoreCICache :: CICacheConfig -> IO ()
restoreCICache cfg = do
  -- cacheS3 cfg (Just $ ccBaseBranch cfg) "restore stack"
  cacheS3 cfg (Just $ ccBaseBranch cfg) "restore stack work"

saveCICache :: CICacheConfig -> IO ()
saveCICache cfg = do
  -- cacheS3 cfg Nothing "save stack"
  cacheS3 cfg Nothing "save stack work"

cacheS3 :: CICacheConfig -> Maybe Text -> Text -> IO ()
cacheS3 CICacheConfig{..} baseBranch cmd = void $ run "cache-s3" args
  where
    args = ml maxSize ++ ml regionArg ++
           [ format ("--bucket="%s) ccBucket
           , format ("--prefix="%s) ccPrefix
           , format ("--git-branch="%s) ccBranch
           , "--suffix=linux"
           , "-v"
           , "info"
           ] ++ cmds ++ ml baseBranchArg
    baseBranchArg = format ("--base-branch="%s) <$> baseBranch
    maxSize = format ("--max-size="%s) <$> ccMaxSize
    regionArg = format ("--region="%s) <$> ccRegion
    cmds = ("-c":T.words cmd)
    ml = maybe [] pure

-- cache-s3 needs a build directory that is the same across all
-- buildkite agents. The build directory option can be used to ensure
-- this is the case.
setupBuildDirectory :: FilePath -> IO ()
setupBuildDirectory buildDir = do
  exists <- testpath buildDir
  when exists $ do
    printf ("Removing old build directory "%fp%"\n") buildDir
    rmtree buildDir
  src <- pwd
  printf ("Copying source tree "%fp%" -> "%fp%"\n") src buildDir
  cptree src buildDir
  cd buildDir

run :: Text -> [Text] -> IO ExitCode
run cmd args = do
  printf (s%" "%s%"\n") cmd (T.unwords args)
  res <- proc cmd args empty
  case res of
    ExitSuccess -> pure ()
    ExitFailure code -> eprintf ("error: Command exited with code "%d%"!\nContinuing...\n") code
  pure res
