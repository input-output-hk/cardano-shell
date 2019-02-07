module NodeIPC.Test where

import           Cardano.Prelude

import           System.Environment (setEnv, unsetEnv)
import           System.IO (hClose)

import           NodeIPC.Lib
import           NodeIPC.Message

import           Prelude (String)
--------------------------------------------------------------------------------
-- Testing
--------------------------------------------------------------------------------

testIPCWithEnv :: IO MsgOut
testIPCWithEnv = testIPC setEnv unsetEnv getIPCHandle

type SetEnvFunc   = String -> String -> IO ()
type UnsetEnvFunc = String -> IO ()

testIPC :: SetEnvFunc -> UnsetEnvFunc -> IO Handle -> IO MsgOut
testIPC setEnvFunc unsetEnvFunc handleFunc = do
    setEnvFunc "NODE_CHANNEL_FD" "0" -- ???
    bracket acquire restore action
  where
    acquire :: IO Handle
    acquire = do
        let port = Port 8090
        ipcHandle <- handleFunc
        startNodeJsIPC ipcHandle port
        return ipcHandle

    restore :: Handle -> IO ()
    restore ipcHandle = do
        hClose ipcHandle
        unsetEnvFunc "NODE_CHANNEL_FD"

    action :: Handle -> IO MsgOut
    action ipcHandle = do
        threadDelay (1 * 10 * 100000)
        sendMessage ipcHandle Ping
        -- Should be Pong
        readMessage ipcHandle
