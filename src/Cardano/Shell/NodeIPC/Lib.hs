{-| Node IPC module. For details please read the spec:

<https://github.com/input-output-hk/cardano-shell/blob/develop/specs/CardanoShellSpec.pdf>
-}

{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Cardano.Shell.NodeIPC.Lib
    ( startNodeJsIPC
    , startIPC
    , Port (..)
    -- * Testing
    , getIPCHandle
    , MsgIn(..)
    , MsgOut(..)
    , NodeIPCException(..)
    , MessageSendFailure(..)
    ) where

import           Cardano.Prelude hiding (catches, handle)

import           Control.Exception.Safe (Handler (..), MonadCatch, catches,
                                         throwM)
import           Data.Aeson (FromJSON (parseJSON), ToJSON (toEncoding),
                             defaultOptions, genericParseJSON,
                             genericToEncoding)
import           Data.Aeson.Types (Options, SumEncoding (ObjectWithSingleField),
                                   sumEncoding)
import           GHC.IO.Handle
import           GHC.IO.Handle.FD (fdToHandle)
import           System.Environment (lookupEnv)
import           System.IO (hClose, hFlush, hSetNewlineMode,
                            noNewlineTranslation)
import           System.IO.Error (IOError, isEOFError)
import           Test.QuickCheck

import           Cardano.Shell.NodeIPC.Message (MessageException,
                                                ReadHandle (..),
                                                WriteHandle (..), readMessage,
                                                sendMessage)

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

-- | Message that can be used to let the other know the that exception had occured
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
-- (e.g @8090@)
newtype Port = Port
    { getPort :: Word16
    } deriving Show

instance Arbitrary Port where
    arbitrary = Port <$> arbitrary

-- | Exception thrown from Node IPC protocol
data NodeIPCException
    = NodeChannelNotFound
    -- ^ Node channel was not found
    | UnableToParseNodeChannel Text
    -- ^ Unable to parse given 'Text' as File descriptor
    | IPCException
    -- ^ Exception thrown when there's something wrong with IPC
    | HandleClosed Handle
    -- ^ Given handle is closed therefore cannot be used
    | UnreadableHandle Handle
    -- ^ Given handle cannot be used to read
    | UnwritableHandle Handle
    -- ^ Given handle cannot be used to write

instance Show NodeIPCException where
    show = \case
        NodeChannelNotFound          -> "Env variable NODE_CHANNEL_FD cannot be found"
        UnableToParseNodeChannel err -> "Unable to parse NODE_CHANNEL_FD: " <> show err
        IPCException                 -> "IOError has occured"
        HandleClosed h               -> "Given handle is closed: " <> show h
        UnreadableHandle h           -> "Unable to read with given handle: " <> show h
        UnwritableHandle h           -> "Unable to write with given handle: " <> show h

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

-- | Start IPC with given 'ReadHandle', 'WriteHandle' and 'Port'
startIPC :: forall m. (MonadIO m) => ReadHandle -> WriteHandle -> Port -> m ()
startIPC readHandle writeHandle port = liftIO $ void $ ipcListener readHandle writeHandle port

-- | Start IPC with NodeJS
--
-- This only works if NodeJS spawns the Haskell executable as child process 
-- (See @server.js@ as an example)
startNodeJsIPC :: forall m. (MonadIO m) => Port -> m ()
startNodeJsIPC port = do
    handle <- liftIO $ getIPCHandle
    let readHandle = ReadHandle handle
    let writeHandle = WriteHandle handle
    liftIO $ void $ ipcListener readHandle writeHandle port

-- | Start IPC listener with given Handles and Port
--
-- When the listener recieves 'Ping' it will return 'Pong'.
--
-- If it recieves 'QueryPort', then the listener
-- responds with 'ReplyPort' with 'Port',
ipcListener :: forall m . (MonadIO m, MonadCatch m) => ReadHandle -> WriteHandle -> Port -> m ()
ipcListener readHandle@(ReadHandle rHndl) writeHandle@(WriteHandle wHndl) (Port port) = do
    checkHandles readHandle writeHandle
    catches handleMsgIn [Handler handler, Handler handleMsgError]
  where
    handleMsgIn :: m ()
    handleMsgIn = do
        liftIO $ hSetNewlineMode rHndl noNewlineTranslation
        send Started
        msgIn <- readMessage readHandle
        case msgIn of
            QueryPort -> send (ReplyPort port)
            Ping      -> send Pong
            -- TODO:Handle them nicely
            MessageInFailure _ -> return ()

    send :: MsgOut -> m ()
    send = sendMessage writeHandle

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

    -- | Check if given two handles are usable (i.e. Handle is open, can be used to read/write)
    checkHandles :: ReadHandle -> WriteHandle -> m ()
    checkHandles (ReadHandle rHandle) (WriteHandle wHandle) = liftIO $ do
        checkHandle rHandle hIsOpen (HandleClosed rHandle)
        checkHandle wHandle hIsOpen (HandleClosed wHandle)
        checkHandle rHandle hIsReadable (UnreadableHandle rHandle)
        checkHandle wHandle hIsWritable (UnwritableHandle wHandle)

    checkHandle :: Handle -> (Handle -> IO Bool) -> NodeIPCException -> IO ()
    checkHandle handle pre exception = do
        result <- pre handle
        when (not result) $ throwM exception

--------------------------------------------------------------------------------
-- placeholder
--------------------------------------------------------------------------------

logError :: Text -> IO ()
logError _ = return ()
