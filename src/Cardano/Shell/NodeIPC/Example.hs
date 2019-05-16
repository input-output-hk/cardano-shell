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

import           Network.Socket (AddrInfo (..), AddrInfoFlag (..), Socket,
                                 SocketOption (..), SocketType (..), accept,
                                 bind, close, defaultHints, fdSocket,
                                 getAddrInfo, listen, setCloseOnExecIfNeeded,
                                 setSocketOption, socket, socketToHandle,
                                 withSocketsDo)
import           System.IO (BufferMode (..), hIsOpen, hSetBuffering)
import           System.Process (CreateProcess (..), StdStream (..), createPipe,
                                 proc, withCreateProcess)

import           Cardano.Shell.NodeIPC.Lib (MsgIn (..), MsgOut (..), Port (..),
                                            ProtocolDuration (..), startIPC)
import           Cardano.Shell.NodeIPC.Message (ReadHandle (..),
                                                WriteHandle (..), readMessage,
                                                sendMessage)
import           Prelude (String)

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

serverPort :: String
serverPort = "8765"

-- | Example of an IPC using nc process
exampleWithProcess :: IO (MsgOut, MsgOut)
exampleWithProcess = do
    -- Test fails dues server not being launched before used.
    -- MVar is used to lock the main process until the server is ready
    isReady <- newEmptyMVar
    withAsync (startNodeServer isReady) $ \as -> do
        void $ takeMVar isReady
        withCreateProcess (proc "nc" ["localhost", serverPort])
            { std_out = CreatePipe
            , std_in  = CreatePipe
            } $ \(Just hin) (Just hout) _ _ -> do
                hSetBuffering hout LineBuffering
                hSetBuffering hin LineBuffering
                let readHandle = ReadHandle hout
                let writeHandle = WriteHandle hin
                sendMessage writeHandle Ping
                receieveMessages readHandle
        `finally`
        cancel as
  where
    -- Start NodeIPC server
    -- From: http://hackage.haskell.org/package/network-3.0.1.0/docs/Network-Socket.html
    startNodeServer :: MVar () -> IO ()
    startNodeServer isReady = withSocketsDo $
        bracket (listenOn isReady serverPort) close server

    listenOn :: MVar () -> String -> IO Socket
    listenOn isReady port = do
        let hints = defaultHints
                { addrFlags = [AI_PASSIVE]
                , addrSocketType = Stream
                }
        addr:_ <- getAddrInfo (Just hints) Nothing (Just port)
        sock <- socket (addrFamily addr) (addrSocketType addr) (addrProtocol addr)
        setSocketOption sock ReuseAddr 1
        let fd = fdSocket sock
        setCloseOnExecIfNeeded fd
        bind sock (addrAddress addr)
        listen sock 10
        putMVar isReady () -- Server is ready, flipping the switch
        return sock

    server :: Socket -> IO ()
    server sock = do
        (conn, _) <- accept sock
        h         <- socketToHandle conn ReadWriteMode
        hSetBuffering h LineBuffering
        void $ forkFinally
            (do
                startIPC SingleMessage (ReadHandle h) (WriteHandle h) nodePort
            )
            (\_ -> close conn)

-- | Read message wigh given 'ReadHandle'
receieveMessages :: ReadHandle -> IO (MsgOut, MsgOut)
receieveMessages clientReadHandle = do
    let readClientMessage :: IO MsgOut
        readClientMessage = readMessage clientReadHandle

    started <- readClientMessage
    pong    <- readClientMessage -- Pong
    return (started, pong)
