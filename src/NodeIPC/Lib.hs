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

import           NodeIPC.Message (MessageException, ReadHandle(..), WriteHandle(..),
                                  readMessage, sendMessage)

import qualified Prelude as P (Show (..))

-- ^ Message expecting from Daedalus
data MsgIn
    = QueryPort
    -- ^ Ask which port to use
    | Ping
    -- ^ Ping
    deriving (Show, Eq, Generic)

-- ^ Message which is send out from Cardano-node
data MsgOut
    = Started
    -- ^ Notify Daedalus that the node has started
    | ReplyPort Word16
    -- ^ Reply of QueryPort
    | Pong
    -- ^ Reply of Ping
    | ParseError Text
    -- ^ Incoming message could not be parsed
    deriving (Show, Eq, Generic)

opts :: Options
opts = defaultOptions { sumEncoding = ObjectWithSingleField }

instance ToJSON   MsgIn  where toEncoding = genericToEncoding opts
instance FromJSON MsgIn  where parseJSON = genericParseJSON opts
instance ToJSON   MsgOut where toEncoding = genericToEncoding opts
instance FromJSON MsgOut where parseJSON = genericParseJSON opts

newtype Port = Port
    { getPort :: Word16
    }

data NodeIPCException
    = NodeChannelNotFound
    | UnableToParseNodeChannel Text
    | IPCException

instance Show NodeIPCException where
    show = \case
        NodeChannelNotFound          -> "Env variable NODE_CHANNEL_FD cannot be found"
        UnableToParseNodeChannel err -> "Unable to parse NODE_CHANNEL_FD: " <> show err
        IPCException                 -> "IOError has occured"

instance Exception NodeIPCException

-- | Acquire Handle for IPC communication
getIPCHandle :: IO Handle
getIPCHandle = do
    mFdstring <- liftIO $ lookupEnv "NODE_CHANNEL_FD"
    case mFdstring of
        Nothing -> throwM NodeChannelNotFound
        Just fdstring -> case readEither fdstring of
            Left err -> throwM $ UnableToParseNodeChannel $ toS err
            Right fd -> liftIO $ fdToHandle fd

-- | Start NodeJS IPC with given 'Handle' and 'Port'
startNodeJsIPC :: (MonadIO m) => ReadHandle -> WriteHandle -> Port -> m ()
startNodeJsIPC readHandle writeHandle port =
    liftIO $ void $ async $ ipcListener readHandle writeHandle port

-- | Start IPC listener with given Handle and Port
ipcListener :: forall m . (MonadIO m, MonadCatch m)
            => ReadHandle
            -- ^ Read handle
            -> WriteHandle
            -- ^ Write handle
            -> Port
            -- ^ Open port
            -> m ()
ipcListener readHndl@(ReadHandle rHndl) writeHndl (Port port) = do
    liftIO $ hSetNewlineMode rHndl noNewlineTranslation
    send Started
    handleMsgIn
  where
    handleMsgIn :: m ()
    handleMsgIn =
        catches
            (do
                msgIn <- readMessage readHndl
                liftIO $ putTextLn $ show msgIn
                case msgIn of
                    QueryPort -> send (ReplyPort port) >> shutdown
                    Ping      -> do
                        send Pong
                        shutdown
            )
        [Handler handler, Handler handleMsgError]

    send :: MsgOut -> m ()
    send = sendMessage writeHndl

    -- Huge catch all, fix this:
    handler :: IOError -> m ()
    handler err = do
        liftIO $ when (isEOFError err) $ logError "its an eof"
        liftIO $ hClose rHndl
        liftIO $ hFlush stdout
        throwM IPCException

    handleMsgError :: MessageException -> m ()
    handleMsgError err = do
        liftIO $ putTextLn "Unexpected message"
        send $ ParseError $ show err
        handleMsgIn

    shutdown :: m ()
    shutdown = return ()


--------------------------------------------------------------------------------
-- placeholder
--------------------------------------------------------------------------------

logError :: Text -> IO ()
logError = putTextLn <$> show
