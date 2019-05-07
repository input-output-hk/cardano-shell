{-# LANGUAGE LambdaCase #-}

{-| This module introduces, low-level message handler that is used to communicate
between Daedalus and Cardano-node
-}

module Cardano.Shell.NodeIPC.Message
    ( sendMessage
    , sendMessageByteString
    , readMessage
    , MessageException(..)
    , ReadHandle(..)
    , WriteHandle(..)
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

-- | Exception
data MessageException
    = DecodeFail BSL.ByteString

instance Show MessageException where
    show (DecodeFail blob) = "Failed to decode given blob: " <> toS blob

instance Exception MessageException

-- | Read-only handle
newtype ReadHandle = ReadHandle
    { getReadHandle :: Handle
    }

-- | Write-only handle
newtype WriteHandle = WriteHandle
    { getWriteHandle :: Handle
    }

-- | Send JSON message with given 'WriteHandle'
sendMessage :: (MonadIO m, ToJSON msg) => WriteHandle -> msg -> m ()
sendMessage writeHandle cmd = sendMessageByteString writeHandle (encode cmd)

sendMessageByteString :: (MonadIO m) => WriteHandle -> BSL.ByteString -> m ()
sendMessageByteString (WriteHandle hndl) byteString = liftIO $ do
    send buildOS $ byteString
    hFlush hndl
  where
    send :: OS -> BSL.ByteString -> IO ()
    send Windows blob = sendWindowsMessage 1 0 (blob <> "\n") -- What's with 1 and 0?
    send _       blob = sendLinuxMessage blob

    sendWindowsMessage :: Word32 -> Word32 -> BSL.ByteString -> IO ()
    sendWindowsMessage int1 int2 blob' =
        BSLC.hPut hndl $ runPut $ mconcat
            [ putWord32le int1
            , putWord32le int2
            , putWord64le $ fromIntegral $ BSL.length blob'
            , putLazyByteString blob'
            ]
    sendLinuxMessage :: BSL.ByteString -> IO ()
    sendLinuxMessage = BSLC.hPutStrLn hndl





-- | Read JSON message with given 'ReadHandle'
readMessage :: (MonadIO m, MonadThrow m, FromJSON msg) => ReadHandle -> m msg
readMessage (ReadHandle hndl) = do
    encodedMessage <- liftIO $ readMessageFromHandle buildOS
    either
        (\_ -> throwM $ DecodeFail encodedMessage)
        return
        (eitherDecode encodedMessage)
  where
    readMessageFromHandle :: OS -> IO BSL.ByteString
    readMessageFromHandle = \case
        Windows -> windowsReadMessage
        _       -> linuxReadMessage

    windowsReadMessage :: IO BSL.ByteString
    windowsReadMessage = do
        _ <- readInt32 hndl
        _ <- readInt32 hndl
        size <- readInt64 hndl
        BSL.hGet hndl $ fromIntegral size

    linuxReadMessage :: IO BSL.ByteString
    linuxReadMessage = do
        line <- hGetLine hndl
        return $ BSLC.pack line

    readInt64 :: Handle -> IO Word64
    readInt64 hnd = do
        bs <- BSL.hGet hnd 8
        pure $ runGet getWord64le bs

    readInt32 :: Handle -> IO Word32
    readInt32 hnd = do
        bs <- BSL.hGet hnd 4
        pure $ runGet getWord32le bs
