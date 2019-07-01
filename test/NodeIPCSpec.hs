{-| Module testing Node IPC
-}

{-# LANGUAGE LambdaCase          #-}
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
import           Test.Hspec.QuickCheck (modifyMaxSuccess, prop)
import           Test.QuickCheck (Property)
import           Test.QuickCheck.Monadic (assert, monadicIO, run)

import           Cardano.Shell.NodeIPC (ClientHandles (..), MessageException,
                                        MessageSendFailure (..), MsgIn (..),
                                        MsgOut (..), NodeIPCError (..),
                                        Port (..), ProtocolDuration (..),
                                        ReadHandle (..), ServerHandles (..),
                                        WriteHandle (..),
                                        bracketFullDuplexAnonPipesHandles,
                                        clientIPCListener,
                                        createFullDuplexAnonPipesHandles,
                                        getReadWriteHandles, isHandleClosed,
                                        isIPCError, isNodeChannelCannotBeFound,
                                        isUnreadableHandle, isUnwritableHandle,
                                        readMessage, sendMessage,
                                        serverReadWrite, startNodeJsIPC)

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
                    eResult <- run . try $ do
                        (readHndl, writeHndl) <- getReadWriteHandles
                        sendMessage writeHndl randomMsg
                        readMessage readHndl :: (IO MsgIn)
                    assert $ isLeft (eResult :: Either MessageException MsgIn)

    describe "startIPC" $ do
        modifyMaxSuccess (const 1000) $ prop "model based testing" $
            -- Have both MsgIn and MsgOut in order to test failing cases
            \(eMsg :: Either MsgOut MsgIn) (randomPort :: Port) -> monadicIO $ do
                response <- run $ either
                    (testStartNodeIPC randomPort)
                    (testStartNodeIPC randomPort)
                    eMsg
                assert $ response == Right (Started, modelResponse randomPort eMsg)

        prop "should return Started and ShutdownInitiated when client sends message 'Shutdown'" $ monadicIO $ do
            result <- run $ testStartNodeIPC port Shutdown
            assert $ isLeft (result :: (Either NodeIPCError (MsgOut, MsgOut)))
            --assert $ started == Started
            --assert $ pong    == ShutdownInitiated

        describe "Exceptions" $ do
            it "should throw NodeIPCError when closed handle is given" $ monadicIO $ do
                eResult <- run $ bracketFullDuplexAnonPipesHandles $ \(_, clientHandles) -> do
                    (\(ReadHandle hndl) -> hClose hndl) (getClientReadHandle clientHandles)
                    clientIPCListener SingleMessage clientHandles port
                assert $ isLeft (eResult :: Either NodeIPCError ())
                whenLeft eResult $ \exception -> assert $ isHandleClosed exception

            it "should throw NodeIPCError when unreadable handle is given" $ monadicIO $ do
                eResult <- run $ bracketFullDuplexAnonPipesHandles $
                    \(_, (ClientHandles _ (WriteHandle wHndl))) -> do
                        let unReadableHandles = ClientHandles (ReadHandle wHndl) (WriteHandle wHndl)
                        clientIPCListener SingleMessage unReadableHandles port
                assert $ isLeft (eResult :: Either NodeIPCError ())
                whenLeft eResult $ \exception -> assert $ isUnreadableHandle exception

            it "should throw NodeIPCError when unwritable handle is given" $ monadicIO $ do
                eResult <- run $ bracketFullDuplexAnonPipesHandles $
                    \(_, (ClientHandles (ReadHandle rHndl) _)) -> do
                    let unWritableHandle = ClientHandles (ReadHandle rHndl) (WriteHandle rHndl)
                    clientIPCListener SingleMessage unWritableHandle port
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
                    (as, _, clientHandles) <- ipcTest
                    let ioerror = mkIOError eofErrorType "Failed with eofe" Nothing Nothing
                    cancelWith as ioerror
                    areHandlesClosed clientHandles
                assert handlesClosed

            prop "should close used handles when the process is finished" $
                \(msg :: MsgIn) -> monadicIO $ do
                    handlesClosed <- run $ do
                        (as, serverHandles, clientHandles) <- ipcTest
                        let readFromClient :: IO MsgOut
                            readFromClient = readMessage . getServerReadHandle $ serverHandles
                        let sendToClient = sendMessage . getServerWriteHandle $ serverHandles
                        sendToClient msg
                        _ <- readFromClient
                        _ <- wait as
                        areHandlesClosed clientHandles
                    assert handlesClosed

    describe "startNodeJsIPC" $
        it "should throw NodeIPCError when it is not spawned by NodeJS process" $ monadicIO $ do
            eResult <- run $ startNodeJsIPC SingleMessage port
            assert $ isLeft (eResult :: Either NodeIPCError ())
            whenLeft eResult $ \exception -> assert $ isNodeChannelCannotBeFound exception
  where
    port :: Port
    port = Port 8090

    -- Check whether both handles are closed
    areHandlesClosed :: ClientHandles -> IO Bool
    areHandlesClosed (ClientHandles (ReadHandle readHandle) (WriteHandle writeHandle)) = do
        readIsOpen  <- hIsOpen readHandle
        writeIsOpen <- hIsOpen writeHandle
        return $ not $ and [readIsOpen, writeIsOpen]

    ipcTest :: IO (Async (Either NodeIPCError ()), ServerHandles, ClientHandles)
    ipcTest = do
        (serverHandles, clientHandles) <- createFullDuplexAnonPipesHandles
        as <- async $ clientIPCListener SingleMessage clientHandles port
        (_ :: MsgOut) <- readMessage $ getServerReadHandle $ serverHandles
        return (as, serverHandles, clientHandles)

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

-- Try to predict the @MsgOut@ with given @Port@ and @Either MsgOut MsgIn@
modelResponse :: Port -> Either MsgOut MsgIn -> MsgOut
modelResponse (Port portNumber) = \case
    Left msgOut ->
        let errorMessage = "Failed to decode given blob: " <> toS (encode msgOut)
        in MessageOutFailure $ ParseError errorMessage
    Right QueryPort ->
        ReplyPort portNumber
    Right Ping ->
        Pong
    Right Shutdown ->
        ShutdownInitiated
    Right (MessageInFailure f) ->
        MessageOutFailure f

-- | Test 'startIPC'
testStartNodeIPC
    :: (ToJSON msg)
    => Port
    -> msg
    -> IO (Either NodeIPCError (MsgOut, MsgOut))
testStartNodeIPC port msg = bracketFullDuplexAnonPipesHandles $
    \(serverHandles, clientHandles) -> do
        (_, responses) <-
            clientIPCListener SingleMessage clientHandles port
            `concurrently`
            do
                -- Use these functions so you don't pass the wrong handle by mistake
                let readClientMessage :: IO MsgOut
                    readClientMessage = readMessage $ getServerReadHandle $ serverHandles
                started  <- readClientMessage
                eResponse <- serverReadWrite serverHandles msg
                case eResponse of
                    Left err       -> return . Left $ err
                    Right response -> return . Right $ (started, response)
        return responses
