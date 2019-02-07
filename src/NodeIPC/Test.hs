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
    setEnv "NODE_CHANNEL_FD" "0" -- ???
    bracket acquire restore action
  where
    acquire :: IO Handle
    acquire = do
        let port = Port 8090
        ipcHandle <- getIPCHandle
        startNodeJsIPC ipcHandle port
        return ipcHandle

    restore :: Handle -> IO ()
    restore ipcHandle = do
        hClose ipcHandle
        unsetEnv "NODE_CHANNEL_FD"

    action :: Handle -> IO MsgOut
    action ipcHandle = do
        sendMessage ipcHandle Ping
        -- Should be Pong
        liftIO $ readMessage ipcHandle