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

import           Cardano.Prelude hiding (catches, handle)

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

import           NodeIPC.Message (MessageException, readMessage, sendMessage)

import qualified Prelude as P (Show (..))

-- Try to figure out something that uses MsgIn

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
        UnableToParseNodeChannel err -> "Unable to parse NODE_CHANNEL_FD: " <> toS err
        IPCException                 -> "IOError has occured"

instance Exception NodeIPCException

getIPCHandle :: IO Handle
getIPCHandle = do
    mFdstring <- liftIO $ lookupEnv "NODE_CHANNEL_FD"
    case mFdstring of
        Nothing -> throwM NodeChannelNotFound
        Just fdstring -> case readEither fdstring of
            Left err -> throwM $ UnableToParseNodeChannel $ toS err
            Right fd -> liftIO $ fdToHandle fd

-- Pass logging layer here
startNodeJsIPC :: (MonadIO m) => Port -> m ()
startNodeJsIPC port = do
    portHandle <- liftIO $ getIPCHandle
    liftIO $ void $ forkIO $ startIpcListener portHandle port

-- | Start IPC listener with given Handle and Port
startIpcListener :: forall m . (MonadIO m, MonadCatch m) => Handle -> Port -> m ()
startIpcListener portHandle (Port port) = do
    liftIO $ hSetNewlineMode portHandle noNewlineTranslation
    catches
       (forever $ do
           line <- liftIO $ readMessage portHandle
           handleMsgIn line
       )
       [Handler handler, Handler handleMsgError]
  where
     send :: MsgOut -> m ()
     send = sendMessage portHandle

     handleMsgIn :: MsgIn -> m ()
     handleMsgIn QueryPort = send $ ReplyPort port
     handleMsgIn Ping      = send Pong

     -- Huge catch all, fix this:
     handler :: IOError -> m ()
     handler err = do
       liftIO $ when (isEOFError err) $ logError "its an eof"
       liftIO $ hFlush stdout
       liftIO $ hClose portHandle
       liftIO $ throwM IPCException

     handleMsgError :: MessageException -> m ()
     handleMsgError err = send $ ParseError $ show err

--------------------------------------------------------------------------------
-- placeholder
--------------------------------------------------------------------------------

logError :: Text -> IO ()
logError = putTextLn
