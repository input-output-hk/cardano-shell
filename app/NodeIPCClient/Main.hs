{-| This executable act as an client of an IPC protocol
|-}

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

-- | Launches the IPC client, the one responses to the message from the server.
--
-- Server will pass its handle via environment variable.
-- The client will then decodes the handle and launches IPC listener.
-- It then respond to the server with the handle it has been given.
--
-- Because of this, the server must the be the one to execute this function (see @exampleWithProcess@).
-- Calling this function directly (ex. @stack exec node-ipc haskell@) will throw an error
-- since there wouldn't be an handle that client will be able to use to communicate with
-- the server.
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
        -- Lookup the Handle that the server has set
        serverWHandle <- getHandleFromEnv "FD_WRITE_HANDLE"
        hSetBuffering serverWHandle LineBuffering
        return serverWHandle

    restore :: Handle -> IO ()
    restore = hClose

    action :: Handle -> IO ()
    action serverWHandle = do
        let serverWriteHandle = WriteHandle serverWHandle
        let serverReadHandle  = ReadHandle stdin
        startIPC SingleMessage serverReadHandle serverWriteHandle port

