module NodeIPC.Example where

import           Cardano.Prelude

import           Network.Socket (AddrInfo (..), AddrInfoFlag (..), Socket,
                                 SocketOption (..), SocketType (..), accept,
                                 bind, close, defaultHints, fdSocket,
                                 getAddrInfo, listen, setCloseOnExecIfNeeded,
                                 setSocketOption, socket, socketToHandle,
                                 withSocketsDo)
import           System.Environment (setEnv, unsetEnv)
import           System.IO (BufferMode (..), hClose, hSetBuffering)
import           System.Process (StdStream (..), proc, std_in, std_out,
                                 withCreateProcess)

import           NodeIPC.Lib (MsgIn (..), MsgOut (..), Port (..), getIPCHandle,
                              startNodeJsIPC)
import           NodeIPC.Message (readMessage, sendMessage)

import           Prelude (String)

--------------------------------------------------------------------------------
-- Testing
--------------------------------------------------------------------------------

serverPort :: String
serverPort = "8765"

-- | Launch NodeIPC server and interact with it using netcat
exampleWithNetwork :: IO (MsgOut, MsgOut)
exampleWithNetwork = do
    async startNodeServer
    withCreateProcess (proc "nc" ["localhost", serverPort])
        { std_out = CreatePipe
        , std_in  = CreatePipe
        } $ \(Just hin) (Just hout) _ _ -> do
            hSetBuffering hout LineBuffering
            start <- readMessage hout -- Started
            sendMessage hin QueryPort
            reply <- readMessage hout -- ReplyPort
            return (start, reply)

-- Start NodeIPC server
-- From: http://hackage.haskell.org/package/network-3.0.1.0/docs/Network-Socket.html
startNodeServer :: IO ()
startNodeServer = withSocketsDo $ bracket (listenOn serverPort) close server
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
        (conn, _) <- accept sock
        h         <- socketToHandle conn ReadWriteMode
        hSetBuffering h LineBuffering
        let nodePort = Port 8090
        void $ forkFinally (startNodeJsIPC h nodePort) (\_ -> close conn)
