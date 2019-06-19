{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE RankNTypes          #-}

module Cardano.Shell.NodeIPC.SimplePortServer
  ( handleIPCProtocol
  , testStartNodeIPC
  , MsgIn(..)
  , MsgOut(..)
  ) where

import           Cardano.Prelude

import           Test.QuickCheck (Arbitrary (..), Gen, arbitraryASCIIChar,
                                  choose, elements, listOf1)
import           Data.Aeson (FromJSON (parseJSON), ToJSON (toEncoding),
                             defaultOptions, genericParseJSON,
                             genericToEncoding)
import           Data.Aeson.Types (Options, SumEncoding (ObjectWithSingleField),
                                   sumEncoding)
import Cardano.Shell.NodeIPC.Lib
import           Cardano.Shell.NodeIPC.Message (MessageException,
                                                ReadHandle (..),
                                                WriteHandle (..), readMessage,
                                                sendMessage)

opts :: Options
opts = defaultOptions { sumEncoding = ObjectWithSingleField }

-- | Message from the server being sent to the client.
data MsgIn
    = QueryPort
    -- ^ Ask which port to use
    | Ping
    -- ^ Ping
    | Shutdown
    -- ^ Shutdown message from the server
    | MessageInFailure MessageSendFailure
    deriving (Show, Eq, Generic)

instance Arbitrary MsgIn where
    arbitrary = elements [QueryPort, Ping]

-- | Message which is send out from Cardano-node
data MsgOut
    = Started
    -- ^ Notify Daedalus that the node has started
    | ReplyPort Word16
    -- ^ Reply of QueryPort
    | Pong
    -- ^ Reply of Ping
    | ShutdownInitiated
    -- ^ Reply of shutdown
    | MessageOutFailure MessageSendFailure
    deriving (Show, Eq, Generic)

instance Arbitrary MsgOut where
    arbitrary = do
        safeText   <- genSafeText
        randomPort <- choose (1000,10000)
        elements
            [ Started
            , ReplyPort randomPort
            , Pong
            , MessageOutFailure $ ParseError safeText
            ]
        where
          genSafeText :: Gen Text
          genSafeText = strConv Lenient <$> listOf1 arbitraryASCIIChar

instance ToJSON   MsgIn  where
    toEncoding = genericToEncoding opts

instance FromJSON MsgIn  where
    parseJSON = genericParseJSON opts

instance ToJSON   MsgOut where
    toEncoding = genericToEncoding opts

instance FromJSON MsgOut where
    parseJSON = genericParseJSON opts

-- | Function for handling the protocol
handleIPCProtocol :: forall m. (MonadIO m) => Port -> MsgIn -> m MsgOut
handleIPCProtocol (Port port) = \case
    QueryPort          -> pure (ReplyPort port)
    Ping               -> pure Pong
    -- Send message, flush buffer, shutdown. Since it's complicated to reason with another
    -- thread that shuts down the program after some time, we do it immediately.
    Shutdown           -> return ShutdownInitiated >> liftIO $ exitWith (ExitFailure 22)
    MessageInFailure f -> pure $ MessageOutFailure f

-- | Test 'startIPC'
testStartNodeIPC :: (ToJSON a, FromJSON b) => Port -> a -> IO (b, b)
testStartNodeIPC port msg = do
    (clientReadHandle, clientWriteHandle) <- getReadWriteHandles
    (serverReadHandle, serverWriteHandle) <- getReadWriteHandles

    -- Start the server
    (_, responses) <-
        startIPC
            SingleMessage
            serverReadHandle
            clientWriteHandle
            (handleIPCProtocol port)
        `concurrently`
        do
            -- Use these functions so you don't pass the wrong handle by mistake
            let readClientMessage :: FromJSON b => IO b
                readClientMessage = readMessage clientReadHandle

            let sendServer :: (ToJSON msg) => msg -> IO ()
                sendServer = sendMessage serverWriteHandle

            -- Communication starts here
            started     <- readClientMessage
            sendServer msg
            response    <- readClientMessage
            return (started, response)

    return responses
