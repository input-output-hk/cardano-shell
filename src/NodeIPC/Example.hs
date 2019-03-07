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
module NodeIPC.Example
    ( exampleWithFD
    , exampleWithProcess
    -- * For testing
    , getReadWriteHandles
    ) where

import           Cardano.Prelude

import           System.IO (BufferMode (..), hSetBuffering)
import           System.Posix.Process (exitImmediately, forkProcess)
import           System.Process (createPipe)

import           NodeIPC.Lib (MsgIn (..), MsgOut (..), Port (..),
                              startNodeJsIPC)
import           NodeIPC.Message (ReadHandle (..), WriteHandle (..),
                                  readMessage, sendMessage)

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

-- | Example using file descriptor
exampleWithFD :: IO (MsgOut, MsgOut)
exampleWithFD = do

    (clientReadHandle, clientWriteHandle) <- getReadWriteHandles
    (serverReadHandle, serverWriteHandle) <- getReadWriteHandles

    -- Start the server
    let nodePort = Port 8090
    void $ async $ startNodeJsIPC serverReadHandle clientWriteHandle nodePort

    -- Use these functions so you don't pass the wrong handle by mistake
    let readClientMessage :: IO MsgOut
        readClientMessage = readMessage clientReadHandle

    let sendServer :: MsgIn -> IO ()
        sendServer = sendMessage serverWriteHandle

    -- Communication starts here
    started <- readClientMessage
    sendServer Ping
    pong    <- readClientMessage -- Pong
    return (started, pong)

-- | Example of an IPC using process
exampleWithProcess :: IO (MsgOut, MsgOut)
exampleWithProcess = do
    (clientReadHandle, clientWriteHandle) <- getReadWriteHandles

    -- Create a child process that acts as an server
    -- Can't apply bracket pattern therefore vulnerable to async exception 
    -- (e.g crash the program in the middle of process)
    void $ forkProcess $ do
        (serverReadHandle, serverWriteHandle) <- getReadWriteHandles
        -- Send message to server
        sendMessage serverWriteHandle Ping
        let nodePort = Port 8090
        startNodeJsIPC serverReadHandle clientWriteHandle nodePort
        exitImmediately ExitSuccess

    let readClientMessage :: IO MsgOut
        readClientMessage = readMessage clientReadHandle

    -- Recieve the messages
    started <- readClientMessage -- Start
    pong    <- readClientMessage -- Pong
    return (started, pong)