{-# LANGUAGE OverloadedStrings #-}

-- Rename to Client
module Client
    ( main
    ) where

import           Cardano.Prelude

import           Cardano.Shell.NodeIPC (MsgIn (..),
                                        Port (..), ProtocolDuration (..),
                                        ReadHandle (..), WriteHandle (..),
                                        sendMessage, startIPC, startNodeJsIPC)
import           GHC.IO.Handle.FD (fdToHandle)
import           Prelude (String, error)
import           System.Environment
import           System.IO (BufferMode (..), hClose, hSetBuffering)
import           System.Process (createPipe)

port :: Port
port = Port 8090

-- | The client of the IPC protocol
--
-- Server will pass its handle via environment variable @FD_WRITE_HANDLE@. The client
-- will then recieves the handle, then launches IPC listener.
-- The listener will then respond to the server depending on the message that the server
-- have sent.
--
-- Because of this, the server must the be the one to execute this function. 
-- Call this function directly (ex. @stack exec node-ipc haskell ping@) will throw an error
-- since there wouldn't be an handle that client will be able to use to communicate with
-- the server.
main :: IO ()
main = do
    (cmd:msg:_) <- getArgs
    case cmd of
        "js"      -> startNodeJsIPC SingleMessage port
        "haskell" -> do
            msgIn <- decodeMessage msg
            bracket acquire restore (action msgIn)
        _         -> return ()
  where
    acquire :: IO (Handle, Handle, Handle)
    acquire = do
        clientWHandle <- getHandleFromEnv "FD_WRITE_HANDLE"
        hSetBuffering clientWHandle LineBuffering
        (serverRHandle , serverWHandle) <- createPipe
        return (clientWHandle, serverRHandle, serverWHandle)

    restore :: (Handle, Handle, Handle) -> IO ()
    restore (clientWHandle, serverRHandle, serverWHandle) = do
        hClose clientWHandle
        hClose serverRHandle
        hClose serverWHandle

    action :: MsgIn -> (Handle, Handle, Handle) -> IO ()
    action msgin (clientWHandle, serverRHandle, serverWHandle) = do
        let clientWriteHandle = WriteHandle clientWHandle
        let serverReadHandle  = ReadHandle serverRHandle
        sendMessage (WriteHandle serverWHandle) msgin
        startIPC SingleMessage serverReadHandle clientWriteHandle port

    getHandleFromEnv :: String -> IO Handle
    getHandleFromEnv envName = do
        mFdstring <- lookupEnv envName
        case mFdstring of
            Nothing -> error $ "Unable to find fd: " <> envName
            Just fdstring -> case readEither fdstring of
                Left err -> error $ "Could not parse file descriptor: " <> toS err
                Right fd -> liftIO $ fdToHandle fd

    -- Decodes argument @msg@
    -- Cannot use @decodeEither@ from @Data.Aeson@ since the actual encoded meesage
    -- cannot be used as an arugment (ex. encoded Ping will be @{"Ping":[]}@)
    decodeMessage :: String -> IO MsgIn
    decodeMessage "ping"      = return Ping
    decodeMessage "queryport" = return QueryPort
    decodeMessage _           = error "Unknown message"
