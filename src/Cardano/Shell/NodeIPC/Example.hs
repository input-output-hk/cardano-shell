{-| This module provides an example of how NodeIPC works.
--
--
-- We want server/client to read only the messages that each should care about
-- In order to realize this, we need two proccesses with each of them providing
-- read/write handle.
--
-- These processes will then pass each others handle respectively and use it to
-- communicate with each other.
--
-- Server will take client's write handle and server's read handle.
--
-- Client will take server's write handle and client's read handle.
--
-- This allows the two proccesses to send the message to the other while
-- reading the response that other had sent.
-}
module Cardano.Shell.NodeIPC.Example
    ( exampleWithFD
    , exampleWithProcess
    -- * For testing
    , getReadWriteHandles
    ) where

import           Cardano.Prelude

import           Data.Aeson (ToJSON)
import           System.IO (BufferMode (..), hSetBuffering)
import           System.Process (createPipe, shell, withCreateProcess)

import           Cardano.Shell.NodeIPC.Lib (MsgIn (..), MsgOut (..), Port (..),
                                            ProtocolDuration (..), startIPC)
import           Cardano.Shell.NodeIPC.Message (ReadHandle (..),
                                                WriteHandle (..), readMessage,
                                                sendMessage)

-- | Create a pipe for interprocess communication and return a
-- ('ReadHandle', 'WriteHandle') Handle pair.
getReadWriteHandles :: IO (ReadHandle, WriteHandle)
getReadWriteHandles = do
    (readHndl, writeHndl) <- createPipe
    hSetBuffering readHndl LineBuffering
    hSetBuffering writeHndl LineBuffering
    let readHandle  = ReadHandle readHndl
    let writeHandle = WriteHandle writeHndl
    return (readHandle, writeHandle)

--------------------------------------------------------------------------------
-- Testing
--------------------------------------------------------------------------------

nodePort :: Port
nodePort = Port 8090

-- | Example using file descriptor
exampleWithFD :: IO (MsgOut, MsgOut)
exampleWithFD = do

    (clientReadHandle, clientWriteHandle) <- getReadWriteHandles

    (_, responses) <-
        ipcServer clientWriteHandle Ping
        `concurrently`
        receieveMessages clientReadHandle

    return responses

-- | Example of an IPC using process
exampleWithProcess :: IO (MsgOut, MsgOut)
exampleWithProcess = do
    (clientReadHandle, clientWriteHandle) <- getReadWriteHandles

    -- Create a child process that acts as an server
    withCreateProcess (shell "some shell") $ \_ _ _ _ ->
        ipcServer clientWriteHandle Ping

    receieveMessages clientReadHandle

-- | IPC server
ipcServer :: (ToJSON msg) => WriteHandle -> msg -> IO ()
ipcServer clientWriteHandle msgin = do
    (serverReadHandle, serverWriteHandle) <- getReadWriteHandles
    -- Send message to server
    sendMessage serverWriteHandle msgin
    startIPC SingleMessage serverReadHandle clientWriteHandle nodePort

-- | Read message wigh given 'ReadHandle'
receieveMessages :: ReadHandle -> IO (MsgOut, MsgOut)
receieveMessages clientReadHandle = do
    let readClientMessage :: IO MsgOut
        readClientMessage = readMessage clientReadHandle

    started <- readClientMessage
    pong    <- readClientMessage -- Pong
    return (started, pong)
