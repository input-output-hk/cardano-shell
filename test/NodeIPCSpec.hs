{-| Module testing Node IPC
-}

{-# LANGUAGE ScopedTypeVariables #-}

module NodeIPCSpec
    ( nodeIPCSpec
    ) where

import           Cardano.Prelude

import           Data.Aeson (FromJSON, ToJSON, encode)
import           GHC.IO.Handle (hIsOpen)
import           System.IO (hClose)
import           System.IO.Error (eofErrorType, mkIOError)
import           Test.Hspec (Spec, describe, it)
import           Test.Hspec.QuickCheck (prop)
import           Test.QuickCheck (Property)
import           Test.QuickCheck.Monadic (assert, monadicIO, run)

import           Cardano.Shell.NodeIPC (MessageException,
                                        MessageSendFailure (..), MsgIn (..),
                                        MsgOut (..), NodeIPCError (..),
                                        Port (..), ProtocolDuration (..),
                                        ReadHandle (..), WriteHandle (..),
                                        getReadWriteHandles, isHandleClosed,
                                        isIPCError,
                                        isNodeChannelCannotBeFound,
                                        isUnreadableHandle, isUnwritableHandle,
                                        readMessage, sendMessage, startIPC,
                                        startNodeJsIPC, testStartNodeIPC)

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

    describe "startIPC" $ do
        it "should return Started and Pong when client sends message 'Ping'" $ monadicIO $ do
            (started, pong) <- run $ do
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

        prop "should return Started and ShutdownInitiated when client sends message 'Shutdown'" $ monadicIO $ do
            result <- run $ try $ testStartNodeIPC port Shutdown
            assert $ isLeft (result :: Either ExitCode (MsgOut, MsgOut))
            --assert $ started == Started
            --assert $ pong    == ShutdownInitiated

        describe "Exceptions" $ do
            prop "should throw exception when incorrect message is sent" $
            -- Sending MsgOut would fail since it expects 'MsgIn' to be sent
                \(randomMsg :: MsgOut) -> monadicIO $ do
                    (started, parseError) <- run $ do
                        testStartNodeIPC port randomMsg
                    let errorMessage = "Failed to decode given blob: " <> toS (encode randomMsg)
                    assert $ started    == Started
                    assert $ parseError == (MessageOutFailure $ ParseError errorMessage)

            it "should throw NodeIPCError when closed handle is given" $ monadicIO $ do
                eResult <- run $ do
                    (readHandle, writeHandle) <- getReadWriteHandles
                    closedReadHandle <- (\(ReadHandle hndl) -> hClose hndl >> return (ReadHandle hndl)) readHandle
                    startIPC SingleMessage closedReadHandle writeHandle port
                assert $ isLeft (eResult :: Either NodeIPCError ())
                whenLeft eResult $ \exception -> assert $ isHandleClosed exception

            it "should throw NodeIPCError when unreadable handle is given" $ monadicIO $ do
                eResult <- run $ do
                    (readHandle, writeHandle) <- getReadWriteHandles
                    let (unReadableHandle, _) = swapHandles readHandle writeHandle
                    startIPC SingleMessage unReadableHandle writeHandle port
                assert $ isLeft (eResult :: Either NodeIPCError ())
                whenLeft eResult $ \exception -> assert $ isUnreadableHandle exception

            it "should throw NodeIPCError when unwritable handle is given" $ monadicIO $ do
                eResult <- run $ do
                    (readHandle, writeHandle) <- getReadWriteHandles
                    let (_, unWritableHandle) = swapHandles readHandle writeHandle
                    startIPC SingleMessage readHandle unWritableHandle port
                assert $ isLeft (eResult :: Either NodeIPCError ())
                whenLeft eResult $ \exception -> assert $ isUnwritableHandle exception

        describe "Resource cleanup" $ do
            it "should throw NodeIPCError when IOError is being thrown" $ monadicIO $ do
                eResult <- run $ do
                    (as, _, _) <- ipcTest
                    let ioerror = mkIOError eofErrorType "Failed with eofe" Nothing Nothing
                    cancelWith as ioerror
                    wait as
                assert $ isLeft (eResult :: Either NodeIPCError ())
                whenLeft eResult $ \exception -> assert $ isIPCError exception

            it "should close used handles when exception is being thrown" $ monadicIO $ do
                handlesClosed <- run $ do
                    (as, readHandle, writeHandle) <- ipcTest
                    let ioerror = mkIOError eofErrorType "Failed with eofe" Nothing Nothing
                    cancelWith as ioerror
                    areHandlesClosed readHandle writeHandle
                assert handlesClosed

            prop "should close used handles when the process is finished" $
                \(msg :: MsgIn) -> monadicIO $ do
                    handlesClosed <- run $ do
                        (clientReadHandle, clientWriteHandle) <- getReadWriteHandles
                        (serverReadHandle, serverWriteHandle) <- getReadWriteHandles
                        as <- async $ startIPC SingleMessage serverReadHandle clientWriteHandle port
                        let readClientMessage = readMessage clientReadHandle
                            sendServer        = sendMessage serverWriteHandle
                        _ <- readClientMessage
                        sendServer msg
                        (_ :: MsgOut) <- readClientMessage
                        _  <- wait as
                        areHandlesClosed serverReadHandle clientWriteHandle
                    assert handlesClosed

    describe "startNodeJsIPC" $
        it "should throw NodeIPCError when it is not spawned by NodeJS process" $ monadicIO $ do
            eResult <- run $ startNodeJsIPC SingleMessage port
            assert $ isLeft (eResult :: Either NodeIPCError ())
            whenLeft eResult $ \exception -> assert $ isNodeChannelCannotBeFound exception
  where
    port :: Port
    port = Port 8090

    swapHandles :: ReadHandle -> WriteHandle -> (ReadHandle, WriteHandle)
    swapHandles (ReadHandle rHandle) (WriteHandle wHandle) = (ReadHandle wHandle, WriteHandle rHandle)

    -- Check whether both handles are closed
    areHandlesClosed :: ReadHandle -> WriteHandle -> IO Bool
    areHandlesClosed (ReadHandle readHandle) (WriteHandle writeHandle) = do
        readIsOpen  <- hIsOpen readHandle
        writeIsOpen <- hIsOpen writeHandle
        return $ not $ and [readIsOpen, writeIsOpen]

    ipcTest :: IO (Async (Either NodeIPCError ()), ReadHandle, WriteHandle)
    ipcTest = do
        (clientReadHandle, clientWriteHandle) <- getReadWriteHandles
        (serverReadHandle, _)                 <- getReadWriteHandles

        as <- async $ startIPC SingleMessage serverReadHandle clientWriteHandle port
        (_ :: MsgOut) <- readMessage clientReadHandle
        return (as, serverReadHandle, clientWriteHandle)

-- | Test if given message can be send and recieved using 'sendMessage', 'readMessage'
testMessage :: (FromJSON msg, ToJSON msg, Eq msg) => msg -> Property
testMessage msg = monadicIO $ do
    response <- run $ do
        (readHndl, writeHndl) <- getReadWriteHandles
        sendMessage writeHndl msg
        readMessage readHndl

    assert $ response == msg


whenLeft :: Applicative m => Either a b -> (a -> m ()) -> m ()
whenLeft (Left x) f = f x
whenLeft _        _ = pure ()
