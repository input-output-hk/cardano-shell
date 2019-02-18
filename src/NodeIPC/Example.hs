module NodeIPC.Example where

import           Cardano.Prelude

import           Network.Socket (AddrInfo (..), AddrInfoFlag (..), Socket,
                                 SocketOption (..), SocketType (..), accept,
                                 bind, close, defaultHints, fdSocket,
                                 getAddrInfo, listen, setCloseOnExecIfNeeded,
                                 setSocketOption, socket, socketToHandle,
                                 withSocketsDo)
import           System.Environment (setEnv, unsetEnv)
import           System.IO (BufferMode (..), hClose, hGetLine, hSetBuffering, isEOF)
import           System.Process (StdStream (..), proc, std_in, std_out,
                                 withCreateProcess)

import           NodeIPC.Lib (MsgIn (..), MsgOut (..), Port (..), getIPCHandle,
                              startNodeJsIPC)
import           NodeIPC.Message (readMessage, sendMessage)

import           System.Process
import           System.Posix.Process
import           GHC.IO.Handle.FD

import           Prelude (String)

--------------------------------------------------------------------------------
-- Testing
--------------------------------------------------------------------------------

serverPort :: String
serverPort = "8765"

-- | Launch NodeIPC server and interact with it using netcat
exampleWithNetwork :: IO (MsgOut, MsgOut)
exampleWithNetwork = do
    processId                   <- getProcessID

    --(readHandle, writeHandle)   <- createPipe

    (readFd, writeFd)           <- createPipeFd

    writeHandle                 <- fdToHandle writeFd
    readHandle                  <- fdToHandle readFd

    -- this is a simple example, apply to server
    --async $
    --    forever $ do
    --        result <- readMessage readHandle
    --        --line <- hGetLine readHandle
    --        putTextLn $ "GOT - " <> result

    -- server example
    let nodePort = Port 8090
    startNodeJsIPC readHandle nodePort

    putTextLn $ "READ   FD - " <> show readFd
    putTextLn $ "WRITE  FD - " <> show writeFd

    let processFd = "/proc/" <> show processId <> "/fd/"
    let processWriteFd = processFd <> show writeFd

    let echoMessageToProc :: String
        echoMessageToProc = "echo \"Ping\" > " <> processWriteFd

    putStrLn $ "ls " <> processFd
    putStrLn $ echoMessageToProc -- yes, you can do this manually

    -- this is to show that it works using from "inside"
    forever $ do
        threadDelay 1000000
        sendMessage writeHandle Ping

    --(_, _, _, pId) <- createProcess (shell "echo Ping") { std_out = UseHandle writeHandle }

    pure (Pong, Pong)

-- Start NodeIPC server
-- From: http://hackage.haskell.org/package/network-3.0.1.0/docs/Network-Socket.html
startNodeServer :: Handle -> IO ()
startNodeServer inputHandle =
    withSocketsDo $ bracket (listenOn serverPort) close server
  where
    listenOn :: String -> IO Socket
    listenOn port = do
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
        return sock

    server :: Socket -> IO ()
    server sock = do
        --(conn, _) <- accept sock
        --h         <- socketToHandle conn ReadWriteMode
        let h = inputHandle
        hSetBuffering h LineBuffering
        let nodePort = Port 8090
        void $ forkFinally (startNodeJsIPC h nodePort) (\_ -> pure ()) --close conn)
