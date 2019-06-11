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
                                        startNodeJsIPC, NodeIPCError)
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
main :: IO (Either NodeIPCError ())
main = do
    (cmd:_) <- getArgs
    case cmd of
        "js"      -> Right <$> void (startNodeJsIPC SingleMessage port)
        "haskell" -> either
            (return . Left)
            action
            =<<
            (getHandleFromEnv "NODE_CHANNEL_FD")
        _         -> return . Right $ ()
  where
    action :: Handle -> IO (Either NodeIPCError ())
    action serverWHandle = do
        hSetBuffering serverWHandle LineBuffering
        let serverWriteHandle = WriteHandle serverWHandle
        let serverReadHandle  = ReadHandle stdin
        startIPC SingleMessage serverReadHandle serverWriteHandle port
        `finally`
        hClose serverWHandle

