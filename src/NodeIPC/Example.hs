{-| This module provides an example of how NodeIPC works.
-}
module NodeIPC.Example where

import           Cardano.Prelude

import           System.IO (BufferMode (..), hSetBuffering)

import           NodeIPC.Lib (MsgIn (..), MsgOut (..), Port (..),
                              startNodeJsIPC)
import           NodeIPC.Message (readMessage, sendMessage)

import           GHC.IO.Handle.FD (fdToHandle)
import           System.Process (createPipeFd)


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

    -- Create file descriptor for client side
    (readFd, writeFd)   <- createPipeFd
    clientWriteHandle   <- fdToHandle writeFd
    clientReadHandle    <- fdToHandle readFd

    -- Create file descriptor for server side
    (sReadFd, sWriteFd) <- createPipeFd
    serverWriteHandle   <- fdToHandle sWriteFd
    serverReadHandle    <- fdToHandle sReadFd

    mapM_ (\h -> hSetBuffering h LineBuffering) 
        [ clientWriteHandle
        , clientReadHandle
        , serverWriteHandle
        , serverReadHandle
        ]

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