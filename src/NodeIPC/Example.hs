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
import           System.Process hiding (getPid)
import           System.Process.Internals

import           NodeIPC.Lib (MsgIn (..), MsgOut (..), Port (..), getIPCHandle,
                              startNodeJsIPC)
import           NodeIPC.Message (readMessage, sendMessage)

import           Prelude (String, error)

import           System.Posix.Process

--------------------------------------------------------------------------------
-- Testing
--------------------------------------------------------------------------------

getPid ph = withProcessHandle ph go
  where
    go ph_ = case ph_ of
               OpenHandle x   -> return $ Just x
               ClosedHandle _ -> return Nothing

serverPort :: String
serverPort = "8765"

example2 :: IO ()
example2 = do
    async startNodeServer
    -- (_,_,_,ph) <- createProcess $ shell "echo $$;sleep 1000" -- prints process id -- NEED TO KEEP THIS ALIVE
    realProcessId <- getProcessID
    putTextLn $ "real process id: " <> show realProcessId
    -- mSomething <- getPid ph
    -- let realProcessId = case mSomething of
    --                         Nothing -> error "Nothing was found"
    --                         Just x  -> x
    putTextLn $ "echo \"Ping\" > /proc/" <> show realProcessId <> "/fd/0"
    threadDelay $ 1 * 10000000000
    -- void $ createProcess
    --     (proc "echo" ["\"Ping\"", ">", ("/proc/" <> show realProcessId <> "/fd/0")])
    --     { std_out = CreatePipe
    --     , std_in  = CreatePipe
    --     }
    -- echo "shows on the tty but bypasses cat" > /proc/{readlProcessId}/fd/0
    return ()

-- Dbus, message queue, domain sockets
-- annonymous pipes

-- hGetLine to communicate

-- system D: monitoring/service manager
-- go devops/website, c library

-- inheriting annoymous pipes
-- try stdin stdout
-- cant do logging

-- nodejs: named pipes in windows
-- unix: unix domain socket


-- | Launch NodeIPC server and interact with it using netcat
exampleWithNetwork :: IO (MsgOut, MsgOut)
exampleWithNetwork = do
    async startNodeServer
    withCreateProcess (proc "nc" ["localhost", serverPort]) -- ??
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
