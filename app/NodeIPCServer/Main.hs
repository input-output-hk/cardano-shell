{-# LANGUAGE OverloadedStrings #-}

module Main
    ( main
    ) where

import           Cardano.Prelude

import           Cardano.Shell.NodeIPC (Port (..), ProtocolDuration (..),
                                        ReadHandle (..), WriteHandle (..),
                                        getHandleFromEnv, startIPC,
                                        startNodeJsIPC)
import           System.IO (BufferMode (..), hClose, hSetBuffering)

port :: Port
port = Port 8090

-- | Launches the IPC server, the one responses to the message from the client.
--
-- Client will pass its handle via environment variable @FD_WRITE_HANDLE@.
-- The server will decodes the handle, then launches IPC listener.
-- It then respond to the client with the handle it has been given.
--
-- Because of this, the client must the be the one to execute this function (see @exampleWithProcess@).
-- Call this function directly (ex. @stack exec node-ipc haskell@) will throw an error
-- since there wouldn't be an handle that server will be able to use to communicate with
-- the client.
main :: IO ()
main = do
    (cmd:_) <- getArgs
    case cmd of
        "js"      -> startNodeJsIPC SingleMessage port
        "haskell" -> bracket acquire restore action
        _         -> return ()
  where
    acquire :: IO Handle
    acquire = do
        clientWHandle <- getHandleFromEnv "FD_WRITE_HANDLE"
        hSetBuffering clientWHandle LineBuffering
        return clientWHandle

    restore :: Handle -> IO ()
    restore = hClose

    action :: Handle -> IO ()
    action clientWHandle = do
        let clientWriteHandle = WriteHandle clientWHandle
        let serverReadHandle  = ReadHandle stdin
        startIPC SingleMessage serverReadHandle clientWriteHandle port

