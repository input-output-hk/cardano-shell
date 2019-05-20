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

import           Cardano.Shell.NodeIPC.Lib (MsgIn (..), MsgOut (..), Port (..),
                                            ProtocolDuration (..), startIPC)
import           Cardano.Shell.NodeIPC.Message (ReadHandle (..),
                                                WriteHandle (..), readMessage,
                                                sendMessage)
import           GHC.IO.Handle.FD (fdToHandle)
import           System.Environment (setEnv, unsetEnv)
import           System.IO (BufferMode (..), hClose, hSetBuffering)
import           System.Process (createPipe, createPipeFd, proc,
                                 withCreateProcess)

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

    (_, responses) <- do
        (serverReadHandle, serverWriteHandle) <- getReadWriteHandles
        -- Send message to server
        sendMessage serverWriteHandle Ping
        startIPC SingleMessage serverReadHandle clientWriteHandle nodePort
        `concurrently`
        receieveMessages clientReadHandle

    return responses

-- | Example of an IPC using process
-- This will be the server, which sends @MsgIn@ messages to the client.
-- The client is executed via @stack exec node-ipc haskell some-message@
exampleWithProcess :: IO (MsgOut, MsgOut)
exampleWithProcess = bracket acquire restore action
  where
    acquire :: IO (ReadHandle, Handle)
    acquire = do
        (rFd, wFd) <- createPipeFd
        setEnv "FD_WRITE_HANDLE" (show wFd)
        readHandle  <- ReadHandle <$> fdToHandle rFd
        -- Since closeFd only exists in 'unix' library,
        -- the only way to close this Fd is to convert it into Handle and apply
        -- hClose to it
        writeHandle <- fdToHandle wFd
        return (readHandle, writeHandle)

    restore :: (ReadHandle, Handle) -> IO ()
    restore ((ReadHandle rHandle), wHandle) = do
        hClose rHandle
        hClose wHandle
        unsetEnv "FD_WRITE_HANDLE"

    action :: (ReadHandle, Handle) -> IO (MsgOut, MsgOut)
    action (readHandle, _) = do
        withCreateProcess (proc "stack" ["exec", "node-ipc", "haskell", "ping"]) $
            \_ _ _ _ -> receieveMessages readHandle


-- | Read message wigh given 'ReadHandle'
receieveMessages :: ReadHandle -> IO (MsgOut, MsgOut)
receieveMessages clientReadHandle = do
    let readClientMessage :: IO MsgOut
        readClientMessage = readMessage clientReadHandle
    started <- readClientMessage -- Started
    pong    <- readClientMessage -- Pong
    return (started, pong)
