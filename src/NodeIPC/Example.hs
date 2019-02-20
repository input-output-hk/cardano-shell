{-| This module provides an example of how NodeIPC works.
-}
module NodeIPC.Example where

import           Cardano.Prelude

import           GHC.IO.Handle.FD (fdToHandle)
import           Prelude (String)
import           System.IO (BufferMode (..), hGetLine, hSetBuffering)
import           System.Posix.Process (forkProcess)
import           System.Process (createPipeFd)

import           NodeIPC.Lib (MsgIn (..), MsgOut (..), Port (..),
                              startNodeJsIPC)
import           NodeIPC.Message (ReadHandle (..), WriteHandle (..),
                                  readMessage, sendMessage)

getReadWriteHandles :: IO (ReadHandle, WriteHandle)
getReadWriteHandles = do
    (readFd, writeFd) <- createPipeFd
    writeHndl         <- fdToHandle writeFd
    readHndl          <- fdToHandle readFd
    hSetBuffering readHndl LineBuffering
    hSetBuffering writeHndl LineBuffering

    let readHandle  = ReadHandle readHndl
    let writeHandle = WriteHandle writeHndl
    return (readHandle, writeHandle)

--------------------------------------------------------------------------------
-- Testing
--------------------------------------------------------------------------------

-- | Example using file descriptor
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
exampleWithFD :: IO (MsgOut, MsgOut)
exampleWithFD = do

    (clientReadHandle, clientWriteHandle) <- getReadWriteHandles
    (serverReadHandle, serverWriteHandle) <- getReadWriteHandles

    -- Start the server
    let nodePort = Port 8090
    startNodeJsIPC serverReadHandle clientWriteHandle nodePort

    -- Use these functions so you don't pass the wrong handle by mistake
    let readClientMessage :: IO MsgOut
        readClientMessage = readMessage clientReadHandle

    let sendServer :: MsgIn -> IO ()
        sendServer = sendMessage serverWriteHandle

    -- Communication starts here
    started <- readClientMessage
    sendServer Ping
    pong <- readClientMessage -- Pong
    return (started, pong)

exampleWithProcess :: IO (MsgOut, MsgOut)
exampleWithProcess = do
    (clientReadHandle, clientWriteHandle) <- getReadWriteHandles

    processId <- forkProcess $ do
        (readFd, writeFd) <- createPipeFd
        readHndl          <- fdToHandle readFd
        hSetBuffering readHndl LineBuffering
        let readHandle  = ReadHandle readHndl

        -- Pass fd to parent
        sendToParent clientWriteHandle $ show writeFd

        let nodePort = Port 8090
        startNodeJsIPC readHandle clientWriteHandle nodePort


    -- Use these functions so you don't pass the wrong handle by mistake
    let readClientMessage :: IO MsgOut
        readClientMessage = readMessage clientReadHandle

    -- Recieve fd from child
    sfd <- recieveFromChild clientReadHandle

    -- Error thrown here.
    serverWriteHandle <- either
        (\_  -> throwIO FdReadException)
        (\fd -> WriteHandle <$> fdToHandle fd) -- Bad file descriptor
        (readEither sfd)

    print serverWriteHandle

    -- Communication starts here
    started <- readClientMessage
    sendMessage serverWriteHandle Ping
    pong <- readClientMessage -- Pong
    return (started, pong)
  where
    sendToParent :: WriteHandle -> String -> IO ()
    sendToParent (WriteHandle hndl) = hPutStrLn hndl
    recieveFromChild :: ReadHandle -> IO String
    recieveFromChild (ReadHandle hndl) = hGetLine hndl

data IPCException = FdReadException
    deriving Show

instance Exception IPCException
