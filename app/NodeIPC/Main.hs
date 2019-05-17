{-# LANGUAGE OverloadedStrings #-}

module Main
    ( main
    ) where

import           Cardano.Prelude

import           Cardano.Shell.NodeIPC (MsgIn (..), NodeIPCException (..),
                                        Port (..), ProtocolDuration (..),
                                        ReadHandle (..), WriteHandle (..),
                                        sendMessage, startIPC, startNodeJsIPC)
import           Control.Exception.Safe (throwM)
import           GHC.IO.Handle.FD (fdToHandle)
import           Prelude (String, error)
import           System.Environment
import           System.IO (BufferMode (..), hClose, hSetBuffering)
import           System.Process (createPipe)

port :: Port
port = Port 8090

main :: IO ()
main = do
    (cmd:_) <- getArgs
    case cmd of
        "js"      -> startNodeJsIPC SingleMessage port
        "haskell" -> bracket acquire restore action
        _         -> return ()
  where
    acquire :: IO (Handle, Handle, Handle)
    acquire = do
        clientWHandle <- getHandle "FD_WRITE_HANDLE"
        hSetBuffering clientWHandle LineBuffering
        (serverRHandle , serverWHandle) <- createPipe
        return (clientWHandle, serverRHandle, serverWHandle)

    restore :: (Handle, Handle, Handle) -> IO ()
    restore (clientWHandle, serverRHandle, serverWHandle) = do
        hClose clientWHandle
        hClose serverRHandle
        hClose serverWHandle

    action :: (Handle, Handle, Handle) -> IO ()
    action (clientWHandle, serverRHandle, serverWHandle) = do
        let clientWriteHandle = WriteHandle clientWHandle
        let serverReadHandle  = ReadHandle serverRHandle
        sendMessage (WriteHandle serverWHandle) Ping
        startIPC SingleMessage serverReadHandle clientWriteHandle port

    getHandle :: String -> IO Handle
    getHandle envName = do
        mFdstring <- lookupEnv envName
        case mFdstring of
            Nothing -> error $ "Unable to find fd: " <> envName
            Just fdstring -> case readEither fdstring of
                Left err -> throwM $ UnableToParseNodeChannel $ toS err
                Right fd -> liftIO $ fdToHandle fd
