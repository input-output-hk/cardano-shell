module NodeIPC.Message
    ( sendMessage
    , readMessage
    , MessageException
    ) where

import           Cardano.Prelude

import           Control.Exception.Safe (MonadThrow, throwM)
import           Data.Aeson (FromJSON, ToJSON, eitherDecode, encode)
import           Data.Binary.Get (getWord32le, getWord64le, runGet)
import           Data.Binary.Put (putLazyByteString, putWord32le, putWord64le,
                                  runPut)
import qualified Data.ByteString.Lazy as BSL
import qualified Data.ByteString.Lazy.Char8 as BSLC
import           Distribution.System (OS (Windows), buildOS)
import           System.IO (hFlush, hGetLine)

import qualified Prelude as P (Show (..))

data MessageException
    = DecodeFail BSL.ByteString

instance Show MessageException where
    show (DecodeFail blob) = "Failed to decode given blob: " <> toS blob

instance Exception MessageException

sendMessage :: (MonadIO m, ToJSON msg) => Handle -> msg -> m ()
sendMessage portHandle cmd = liftIO $ send portHandle $ encode cmd

readMessage :: (MonadIO m, MonadThrow m, FromJSON msg) => Handle -> m msg
readMessage portHandle = do
    encodedMessage <- if buildOS == Windows
        then do
            (_, _, blob) <- liftIO $ windowsReadMessage
          --  logInfo $ "int is: " <> (show [int1, int2]) <> " and blob is: " <> (show blob)
            return blob
        else
            liftIO $ linuxReadMessage
    eitherM
        (\_ -> throwM $ DecodeFail encodedMessage)
        return
        (return $ eitherDecode encodedMessage)
  where
    windowsReadMessage :: IO (Word32, Word32, BSL.ByteString)
    windowsReadMessage = do
        int1 <- readInt32 portHandle
        int2 <- readInt32 portHandle
        size <- readInt64 portHandle
        blob <- BSL.hGet portHandle $ fromIntegral size
        return (int1, int2, blob)

    linuxReadMessage :: IO BSL.ByteString
    linuxReadMessage = do
        line <- hGetLine portHandle
        return $ BSLC.pack line

send :: Handle -> BSL.ByteString -> IO ()
send portHandle blob = do
    if buildOS == Windows
        then sendWindowsMessage 1 0 (blob <> "\n") -- What's with 1 and 0?
        else sendLinuxMessage blob
    hFlush portHandle
  where
    sendWindowsMessage :: Word32 -> Word32 -> BSL.ByteString -> IO ()
    sendWindowsMessage int1 int2 blob' =
        BSLC.hPut portHandle $ runPut $ mconcat 
            [ putWord32le int1
            , putWord32le int2
            , putWord64le $ fromIntegral $ BSL.length blob'
            , putLazyByteString blob'
            ]
    sendLinuxMessage :: BSL.ByteString -> IO ()
    sendLinuxMessage = BSLC.hPutStrLn portHandle

readInt64 :: Handle -> IO Word64
readInt64 hnd = do
    bs <- BSL.hGet hnd 8
    pure $ runGet getWord64le bs

readInt32 :: Handle -> IO Word32
readInt32 hnd = do
    bs <- BSL.hGet hnd 4
    pure $ runGet getWord32le bs

-- | Monadic generalisation of 'either'.
eitherM :: Monad m => (a -> m c) -> (b -> m c) -> m (Either a b) -> m c
eitherM l r x = either l r =<< x
