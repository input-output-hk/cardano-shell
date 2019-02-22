{-| Module testing Node IPC
-}

{-# LANGUAGE ScopedTypeVariables #-}

module NodeIPCSpec
    ( nodeIPCSpec
    ) where

import           Cardano.Prelude

import           Data.Aeson (FromJSON, ToJSON)
import           Test.Hspec (Spec, describe, it)
import           Test.Hspec.QuickCheck (prop)
import           Test.QuickCheck (Property)
import           Test.QuickCheck.Monadic (assert, monadicIO, run)

import           NodeIPC.Example (exampleWithFD, exampleWithProcess,
                                  getReadWriteHandles)
import           NodeIPC.Lib (MsgIn (..), MsgOut (..))
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

    describe "startNodeJsIPC" $ do
        describe "FD" $
            it "should return Started, Pong" $ monadicIO $ do
                (started, pong) <- run exampleWithFD
                assert $ started == Started
                assert $ pong    == Pong
        describe "Process" $
            it "should return Started, Pong" $ monadicIO $ do
                (started, pong) <- run exampleWithProcess
                assert $ started == Started
                assert $ pong    == Pong

-- | Test if given message can be send and recieved using 'sendMessage', 'readMessage'
testMessage :: (FromJSON msg, ToJSON msg, Eq msg) => msg -> Property
testMessage msg = monadicIO $ do
    (readHndl, writeHndl) <- run getReadWriteHandles
    run $ sendMessage writeHndl msg
    response <- run $ readMessage readHndl

    assert $ response == msg
