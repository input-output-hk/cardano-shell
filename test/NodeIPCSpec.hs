{-| Module testing Node IPC
-}

{-# LANGUAGE ScopedTypeVariables #-}

module NodeIPCSpec
    ( nodeIPCSpec
    ) where

import           Cardano.Prelude

import           Data.Aeson (FromJSON, ToJSON, encode)
import           System.IO.Error (eofErrorType, mkIOError)
import           Test.Hspec (Spec, describe, it)
import           Test.Hspec.QuickCheck (prop)
import           Test.QuickCheck (Property)
import           Test.QuickCheck.Monadic (assert, monadicIO, run)

import           NodeIPC.Example (exampleWithProcess, getReadWriteHandles)
import           NodeIPC.Lib (MsgIn (..), MsgOut (..), NodeIPCException (..),
                              Port (..), startNodeJsIPC)
import           NodeIPC.Message

-- | Test spec for node IPC
nodeIPCSpec :: Spec
nodeIPCSpec = do
    describe "Message passing" $ do
        describe "sendMessage/readMessage" $ do
            prop "should be able to send MsgIn messages using handle pairs" $
                \(randomMsg :: MsgIn) -> testMessage randomMsg
            prop "should be able to send MsgOut messages using handle pairs" $
                \(randomMsg :: MsgOut) -> testMessage randomMsg
            prop "should throw MessageException when incorrect message is sent" $
            -- Send random MsgOut, but try to decode it as MsgIn which would fail
                \(randomMsg :: MsgOut) -> monadicIO $ do
                    eResult <- run $ try $ do
                        (readHndl, writeHndl) <- getReadWriteHandles
                        sendMessage writeHndl randomMsg
                        readMessage readHndl :: (IO MsgIn)
                    assert $ isLeft (eResult :: Either MessageException MsgIn)

    describe "startNodeJsIPC" $ do
        it "should return Started and Pong when client sends message 'Ping'" $ monadicIO $ do
            (started, pong) <- run $ do
                let port = Port 8090
                testStartNodeIPC port Ping
            assert $ started == Started
            assert $ pong    == Pong

        prop "should return Started and ReplyPort when client sends message 'QueryPort'" $
            \(randomPort :: Port) -> monadicIO $ do
            (started, replyPort) <- run $ do
                testStartNodeIPC randomPort QueryPort
            let portNum = getPort randomPort
            assert $ started   == Started
            assert $ replyPort == (ReplyPort portNum)

        prop "should throw exception when incorrect message is sent" $
        -- Sending MsgOut would fail since it expects 'MsgIn' to be sent
            \(randomMsg :: MsgOut) (randomPort :: Port) -> monadicIO $ do
                (started, parseError) <- run $ do
                    testStartNodeIPC randomPort randomMsg
                let errorMessage = "Failed to decode given blob: " <> toS (encode randomMsg)
                assert $ started    == Started
                assert $ parseError == (ParseError errorMessage)

        it "should throw NodeIPCException when IOError is being thrown" $ monadicIO $ do
            eResult <- run $ try $ do
                let port = Port 8000
                (clientReadHandle, clientWriteHandle) <- getReadWriteHandles
                (serverReadHandle, _)                 <- getReadWriteHandles

                -- Start the server
                as <- async $ startNodeJsIPC serverReadHandle clientWriteHandle port
                (_ :: MsgOut) <- readMessage clientReadHandle
                -- Create IOError and cancel the thread with it
                let hndl    = getReadHandle serverReadHandle
                let ioerror = mkIOError eofErrorType "Failed with eofe" (Just hndl) Nothing
                cancelWith as ioerror
                wait as
            assert $ isLeft (eResult :: Either NodeIPCException ())

        describe "Process" $ do
            it "should return Started, Pong" $ monadicIO $ do
                (started, pong) <- run exampleWithProcess
                assert $ started == Started
                assert $ pong    == Pong

-- | Test if given message can be send and recieved using 'sendMessage', 'readMessage'
testMessage :: (FromJSON msg, ToJSON msg, Eq msg) => msg -> Property
testMessage msg = monadicIO $ do
    response <- run $ do
        (readHndl, writeHndl) <- getReadWriteHandles
        sendMessage writeHndl msg
        readMessage readHndl

    assert $ response == msg

-- | Test 'startNodeJsIPC'
testStartNodeIPC :: forall msg. (ToJSON msg) => Port -> msg -> IO (MsgOut, MsgOut)
testStartNodeIPC port msg = do
    (clientReadHandle, clientWriteHandle) <- getReadWriteHandles
    (serverReadHandle, serverWriteHandle) <- getReadWriteHandles

    -- Start the server
    void $ async $ startNodeJsIPC serverReadHandle clientWriteHandle port

    -- Use these functions so you don't pass the wrong handle by mistake
    let readClientMessage :: IO MsgOut
        readClientMessage = readMessage clientReadHandle

    let sendServer :: msg -> IO ()
        sendServer = sendMessage serverWriteHandle

    -- Communication starts here
    started <- readClientMessage
    sendServer msg
    response <- readClientMessage
    return (started, response)
