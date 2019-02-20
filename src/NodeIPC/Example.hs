module NodeIPC.Example where

import           Cardano.Prelude

import           System.IO (BufferMode (..), hSetBuffering)

import           NodeIPC.Lib (MsgIn (..), MsgOut (..), Port (..),
                              startNodeJsIPC)
import           NodeIPC.Message (readMessage, sendMessage)

import           GHC.IO.Handle.FD (fdToHandle)
import           System.Posix.Process (getProcessID)
import           System.Process (createPipeFd)

import           Prelude (String)

--------------------------------------------------------------------------------
-- Testing
--------------------------------------------------------------------------------

-- | Example using file descriptor
exampleWithFD :: IO MsgOut
exampleWithFD = do
    processId                   <- getProcessID

    (readFd, writeFd)           <- createPipeFd

    writeHandle                 <- fdToHandle writeFd
    readHandle                  <- fdToHandle readFd

    hSetBuffering writeHandle LineBuffering
    hSetBuffering readHandle LineBuffering

    let nodePort = Port 8090
    startNodeJsIPC readHandle writeHandle nodePort

    putTextLn $ "READ   FD - " <> show readFd
    putTextLn $ "WRITE  FD - " <> show writeFd

    let processFd = "/proc/" <> show processId <> "/fd/"
    let processWriteFd = processFd <> show writeFd

    let echoMessageToProc :: String
        echoMessageToProc = "echo \"Ping\" > " <> processWriteFd

    putStrLn $ "ls " <> processFd
    putStrLn $ echoMessageToProc -- yes, you can do this manually

    -- this is to show that it works using from "inside"
    -- forever $ do
    --     threadDelay 1000000
    --     sendMessage writeHandle Ping

    -- Communication starts here
    sendMessage writeHandle Ping
    readMessage readHandle -- Pong


    -- this is a simple example, apply to server
    --async $
    --    forever $ do
    --        result <- readMessage readHandle
    --        --line <- hGetLine readHandle
    --        putTextLn $ "GOT - " <> result
