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
    setEnv "NODE_CHANNEL_FD" "1" -- ???
    bracket acquire restore action
  where
    acquire :: IO (Handle, Async ())
    acquire = do
        let port = Port 8090
        ipcHandle <- getIPCHandle
        process   <- async $ startNodeJsIPC port
        return (ipcHandle, process)

    restore :: (Handle, Async()) -> IO ()
    restore (ipcHandle, process) = do
        hClose ipcHandle
        cancel process
        unsetEnv "NODE_CHANNEL_FD"

    action :: (Handle, Async ()) -> IO MsgOut
    action (ipcHandle, _) = do
        sendMessage ipcHandle Ping
        -- Should be Pong
        liftIO $ readMessage ipcHandle