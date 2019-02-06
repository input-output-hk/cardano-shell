module NodeIPC.Test where

import           Cardano.Prelude

import           System.Environment (setEnv, unsetEnv)
import           System.IO (hClose)

import           NodeIPC.Lib
import           NodeIPC.Message

--------------------------------------------------------------------------------
-- Testing
--------------------------------------------------------------------------------

testIPC :: IO MsgOut
testIPC = do
    let port = Port 8090
    setEnv "NODE_CHANNEL_FD" "1" -- ???
    bracket
        (do
            ipcHandle <- getIPCHandle
            process   <- async $ startNodeJsIPC port
            return (ipcHandle, process)
        )
        (\(ipcHandle, process) -> do
            hClose ipcHandle
            cancel process
            unsetEnv "NODE_CHANNEL_FD"
        )
        (\(ipcHandle, _) -> do
            sendMessage ipcHandle Ping
            -- Should be Pong
            liftIO $ readMessage ipcHandle
        )
