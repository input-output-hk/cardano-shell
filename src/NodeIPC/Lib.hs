{-| Node IPC module. For details please read the spec:

<https://github.com/input-output-hk/cardano-shell/blob/develop/specs/CardanoShellSpec.pdf>
-}

{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}

module NodeIPC.Lib
    ( startNodeJsIPC
    , Port (..)
    -- * For testing
    , getIPCHandle
    , MsgIn(..)
    , MsgOut(..)
    , NodeIPCException(..)
    , MessageSendFailure(..)
    ) where

import           Cardano.Prelude hiding (catches)

import           Control.Exception.Safe (Handler (..), MonadCatch, catches,
                                         throwM)
import           Data.Aeson (FromJSON (parseJSON), ToJSON (toEncoding),
                             defaultOptions, genericParseJSON,
                             genericToEncoding)
import           Data.Aeson.Types (Options, SumEncoding (ObjectWithSingleField),
                                   sumEncoding)
import           GHC.IO.Handle.FD (fdToHandle)
import           System.Environment (lookupEnv)
import           System.IO (hClose, hFlush, hSetNewlineMode,
                            noNewlineTranslation)
import           System.IO.Error (IOError, isEOFError)
import           Test.QuickCheck

import           NodeIPC.Message (MessageException, ReadHandle (..),
                                  WriteHandle (..), readMessage, sendMessage)

import qualified Prelude as P (Show (..))

-- | Message expecting from Daedalus
data MsgIn
    = QueryPort
    -- ^ Ask which port to use
    | Ping
    -- ^ Ping
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
    | MessageOutFailure MessageSendFailure
    deriving (Show, Eq, Generic)

data MessageSendFailure
    = ParseError Text
    | GeneralFailure
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

opts :: Options
opts = defaultOptions { sumEncoding = ObjectWithSingleField }

instance ToJSON   MsgIn  where
    toEncoding = genericToEncoding opts

instance FromJSON MsgIn  where
    parseJSON = genericParseJSON opts

instance ToJSON   MsgOut where
    toEncoding = genericToEncoding opts

instance FromJSON MsgOut where
    parseJSON = genericParseJSON opts

instance FromJSON MessageSendFailure where
    parseJSON = genericParseJSON opts

instance ToJSON MessageSendFailure where
    toEncoding = genericToEncoding opts

-- | Port that is used to communicate between Cardano-node and Daedalus
-- (e.g 8090)
newtype Port = Port
    { getPort :: Word16
    } deriving Show

instance Arbitrary Port where
    arbitrary = Port <$> arbitrary

data NodeIPCException
    = NodeChannelNotFound
    -- ^ Node channel was not found
    | UnableToParseNodeChannel Text
    -- ^ Unable to parse given 'Text' as File descriptor
    | IPCException
    -- ^ Exception thrown when there's something wrong with IPC

instance Show NodeIPCException where
    show = \case
        NodeChannelNotFound          -> "Env variable NODE_CHANNEL_FD cannot be found"
        UnableToParseNodeChannel err -> "Unable to parse NODE_CHANNEL_FD: " <> show err
        IPCException                 -> "IOError has occured"

instance Exception NodeIPCException

-- | Acquire a Handle that can be used for IPC
getIPCHandle :: IO Handle
getIPCHandle = do
    mFdstring <- liftIO $ lookupEnv "NODE_CHANNEL_FD"
    case mFdstring of
        Nothing -> throwM NodeChannelNotFound
        Just fdstring -> case readEither fdstring of
            Left err -> throwM $ UnableToParseNodeChannel $ toS err
            Right fd -> liftIO $ fdToHandle fd

-- | Start NodeJS IPC with given 'ReadHandle', 'WriteHandle' and 'Port'
startNodeJsIPC :: (MonadIO m) => ReadHandle -> WriteHandle -> Port -> m ()
startNodeJsIPC readHandle writeHandle port =
    liftIO $ void $ ipcListener readHandle writeHandle port

-- | Start IPC listener with given Handles and Port
--
-- when the listener recieves 'Ping' it will return 'Pong'.
--
-- If it recieves 'QueryPort', then the listener
-- responds with 'ReplyPort' with 'Port',
ipcListener :: forall m . (MonadIO m, MonadCatch m) => ReadHandle -> WriteHandle -> Port -> m ()
ipcListener readHndl@(ReadHandle rHndl) writeHndl@(WriteHandle wHndl) (Port port) = do
    catches handleMsgIn [Handler handler, Handler handleMsgError]
  where
    handleMsgIn :: m ()
    handleMsgIn = do
        liftIO $ hSetNewlineMode rHndl noNewlineTranslation
        send Started
        msgIn <- readMessage readHndl
        case msgIn of
            QueryPort -> send (ReplyPort port) >> shutdown
            Ping      -> do
                send Pong
                shutdown
            MessageInFailure _ -> shutdown

    send :: MsgOut -> m ()
    send = sendMessage writeHndl

    -- Huge catch all, fix this:
    handler :: IOError -> m ()
    handler err = do
        liftIO $ do
            when (isEOFError err) $ logError "its an eof"
            hClose rHndl
            hClose wHndl
            hFlush stdout
        throwM IPCException

    handleMsgError :: MessageException -> m ()
    handleMsgError err = do
        liftIO $ logError "Unexpected message"
        send $ MessageOutFailure $ ParseError $ show err

    -- (TODO:) Exception handling on broken handles (e.g.handle is already closed etc.)
    -- Implement here
    shutdown :: m ()
    shutdown = return ()


--------------------------------------------------------------------------------
-- placeholder
--------------------------------------------------------------------------------

logError :: Text -> IO ()
logError _ = return ()
