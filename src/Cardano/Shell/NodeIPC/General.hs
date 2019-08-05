{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Copyright: © 2018-2019 IOHK
-- License: MIT
--
-- NodeJS @child_process()@ IPC message protocol.
--
-- See <https://nodejs.org/api/child_process.html#child_process_child_process_spawn_command_args_options>
-- for more information about the message protocol.

module Cardano.Shell.NodeIPC.General
    ( NodeChannel
    , NodeChannelError(..)
    , NodeChannelFinished(..)
    , setupNodeChannel
    , runNodeChannel
    ) where

import           Cardano.Prelude

import           Control.Concurrent.Async (concurrently_, race)
import           Control.Concurrent.MVar (MVar, newEmptyMVar, putMVar, takeMVar)
import           Control.Exception (IOException, catch, tryJust)
import           Control.Monad (forever)
import           Data.Aeson (FromJSON (..), ToJSON (..), eitherDecode, encode)
import           Data.Bifunctor (first)
import           Data.Binary.Get (getWord32le, getWord64le, runGet)
import           Data.Binary.Put (putLazyByteString, putWord32le, putWord64le,
                                  runPut)
import           Data.Functor (($>))
import           Data.Maybe (fromMaybe)
import           Data.Text (Text)
import           Data.Word (Word32, Word64)
import           GHC.IO.Handle.FD (fdToHandle)
import           System.Environment (lookupEnv)
import           System.Info (os)
import           System.IO (Handle, hFlush, hGetLine, hSetNewlineMode,
                            noNewlineTranslation)
import           System.IO.Error (IOError, userError)
import           Text.Read (readEither)

import qualified Data.ByteString.Lazy as BL
import qualified Data.ByteString.Lazy.Char8 as L8
import qualified Data.Text as T

-- | Possible reasons why the node channel can't be set up.
data NodeChannelError
    = NodeChannelDisabled
      -- ^ This process has not been started as a nodejs @'ipc'@ child_process.
    | NodeChannelBadFD Text
      -- ^ The @NODE_CHANNEL_FD@ environment variable has an incorrect value.
    deriving (Show, Eq)

-- | The only way a node channel finishes on its own is if there is some error
-- reading or writing to its file descriptor.
newtype NodeChannelFinished = NodeChannelFinished IOError

-- | A h to the NodeJS parent process.
newtype NodeChannel = NodeChannel Handle

-- | Parse the @NODE_CHANNEL_FD@ variable, if it's set, and returns a h for
-- communicating with the parent process.
setupNodeChannel :: IO (Either NodeChannelError NodeChannel)
setupNodeChannel = (fromMaybe "" <$> lookupEnv "NODE_CHANNEL_FD") >>= \case
    "" -> pure (Left NodeChannelDisabled)
    var -> case readEither var of
        Left err -> pure . Left . NodeChannelBadFD $
           "unable to parse NODE_CHANNEL_FD: " <> T.pack err
        Right fd -> tryJust handleBadFd (NodeChannel <$> fdToHandle fd)
  where
    handleBadFd :: IOException -> Maybe NodeChannelError
    handleBadFd = Just . NodeChannelBadFD . T.pack . show

-- | Communicate with a parent process using a NodeJS-specific protocol. This
-- process must have been spawned with one of @stdio@ array entries set to
-- @'ipc'@.
runNodeChannel
    :: (FromJSON msgin, ToJSON msgout)
    => (Either Text msgin -> IO (Maybe msgout))
       -- ^ Handler for messages coming from the parent process. Left values are
       -- for JSON parse errors. The handler can optionally return a reply
       -- message.
    -> ((msgout -> IO ()) -> IO a)
       -- ^ Action to run with the channel. It is passed a function for sending
       -- messages to the parent process.
    -> NodeChannel
       -- ^ Channel provided by 'setupNodeChannel'
    -> IO (Either NodeChannelFinished a)
runNodeChannel onMsg handleMsg (NodeChannel h) = do
    chan <- newEmptyMVar
    let ipc = ipcListener h chan onMsg
        action' = handleMsg (putMVar chan)
    race ipc action'

----------------------------------------------------------------------------
-- Protocol Implementation

ipcListener
    :: forall msgin msgout. (FromJSON msgin, ToJSON msgout)
    => Handle
    -> MVar msgout
    -> (Either Text msgin -> IO (Maybe msgout))
    -> IO NodeChannelFinished
ipcListener h chan onMsg = NodeChannelFinished <$> do
    hSetNewlineMode h noNewlineTranslation
    (concurrently_ replyLoop sendLoop $> unexpected) `catch` pure
  where
    sendLoop, replyLoop :: IO ()
    replyLoop = forever (recvMsg >>= onMsg >>= maybeSend)
    sendLoop = forever (takeMVar chan >>= sendMsg)

    recvMsg :: IO (Either Text msgin)
    recvMsg = first T.pack . eitherDecode <$> readMessage h

    sendMsg :: msgout -> IO ()
    sendMsg = sendMessage h . encode

    maybeSend :: Maybe msgout -> IO ()
    maybeSend = maybe (pure ()) (putMVar chan)

    unexpected = userError "ipcListener: unreachable code"

readMessage :: Handle -> IO BL.ByteString
readMessage = if isWindows then readMessageWindows else readMessagePosix

readMessageWindows :: Handle -> IO BL.ByteString
readMessageWindows h = do
    _int1 <- readInt32 h
    _int2 <- readInt32 h
    size <- readInt64 h
    -- logInfo $ "int is: " <> (show [_int1, _int2]) <> " and blob is: " <> (show blob)
    BL.hGet h $ fromIntegral size
  where
    readInt64 :: Handle -> IO Word64
    readInt64 hnd = do
        bs <- BL.hGet hnd 8
        pure $ runGet getWord64le bs

    readInt32 :: Handle -> IO Word32
    readInt32 hnd = do
        bs <- BL.hGet hnd 4
        pure $ runGet getWord32le bs

readMessagePosix :: Handle -> IO BL.ByteString
readMessagePosix = fmap L8.pack . hGetLine

sendMessage :: Handle -> BL.ByteString -> IO ()
sendMessage h msg = send h msg >> hFlush h
  where
    send = if isWindows then sendMessageWindows else sendMessagePosix

sendMessageWindows :: Handle -> BL.ByteString -> IO ()
sendMessageWindows = sendMessageWindows' 1 0

sendMessageWindows' :: Word32 -> Word32 -> Handle -> BL.ByteString -> IO ()
sendMessageWindows' int1 int2 h blob =
    L8.hPut h $ runPut $ mconcat parts
  where
    blob' = blob <> "\n"
    parts =
        [ putWord32le int1
        , putWord32le int2
        , putWord64le $ fromIntegral $ BL.length blob'
        , putLazyByteString blob'
        ]

sendMessagePosix :: Handle -> BL.ByteString -> IO ()
sendMessagePosix = L8.hPutStrLn

----------------------------------------------------------------------------
-- Helpers

isWindows :: Bool
isWindows = os == "windows"
