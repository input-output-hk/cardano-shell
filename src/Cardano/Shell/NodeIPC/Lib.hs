{-| Node IPC module. For details please read the spec:

<https://github.com/input-output-hk/cardano-shell/blob/develop/specs/CardanoShellSpec.pdf>
-}

{-# LANGUAGE DeriveGeneric          #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE ScopedTypeVariables    #-}

module Cardano.Shell.NodeIPC.Lib
    ( startNodeJsIPC
    , startIPC
    , Port (..)
    , ProtocolDuration (..)
    -- * Testing
    , getIPCHandle
    , MsgIn(..)
    , MsgOut(..)
    , NodeIPCException(..)
    , MessageSendFailure(..)
    -- * Predicates
    , isIPCException
    , isHandleClosed
    , isUnreadableHandle
    , isUnwritableHandle
    , isNodeChannelCannotBeFound
    ) where

import           Cardano.Prelude hiding (catches, finally, handle)

import           Control.Exception.Safe (Handler (..), MonadCatch, MonadMask,
                                         catches, finally, throwM)
import           Data.Aeson (FromJSON (parseJSON), ToJSON (toEncoding),
                             defaultOptions, genericParseJSON,
                             genericToEncoding)
import           Data.Aeson.Types (Options, SumEncoding (ObjectWithSingleField),
                                   sumEncoding)
import           GHC.IO.Handle (hIsOpen, hIsReadable, hIsWritable)
import           GHC.IO.Handle.FD (fdToHandle)
import           System.Environment (lookupEnv)
import           System.IO (hClose, hFlush, hSetNewlineMode,
                            noNewlineTranslation)
import           System.IO.Error (IOError, isEOFError)
import           Test.QuickCheck (Arbitrary (..), Gen, arbitraryASCIIChar,
                                  choose, elements, listOf1)

import           Cardano.Shell.NodeIPC.Message (MessageException,
                                                ReadHandle (..),
                                                WriteHandle (..), readMessage,
                                                sendMessage)

import qualified Prelude as P (Show (..))

-- | The way the IPC protocol works.
data ProtocolDuration
    = SingleMessage
    -- ^ Responds to a single message and exits
    | MultiMessage
    -- ^ Runs forever responding to messages
    deriving (Eq, Show)

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
    } deriving (Eq, Show, Generic)

instance FromJSON Port where
    parseJSON = genericParseJSON opts

instance ToJSON Port where
    toEncoding = genericToEncoding opts

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
startIPC :: forall m. (MonadIO m) => ProtocolDuration -> ReadHandle -> WriteHandle -> Port -> m ()
startIPC protocolDuration readHandle writeHandle port = liftIO $ void $ ipcListener protocolDuration readHandle writeHandle port

-- | Start IPC with NodeJS
--
-- This only works if NodeJS spawns the Haskell executable as child process
-- (See @server.js@ as an example)
startNodeJsIPC :: forall m. (MonadIO m) => ProtocolDuration -> Port -> m ()
startNodeJsIPC protocolDuration port = do
    handle          <- liftIO $ getIPCHandle
    let readHandle  = ReadHandle handle
    let writeHandle = WriteHandle handle
    liftIO $ void $ ipcListener protocolDuration readHandle writeHandle port

-- | Function for handling the protocol
handleIPCProtocol :: forall m. (MonadIO m) => Port -> MsgIn -> m MsgOut
handleIPCProtocol (Port port) = \case
    QueryPort          -> pure (ReplyPort port)
    Ping               -> pure Pong
    MessageInFailure f -> pure $ MessageOutFailure f

-- | Start IPC listener with given Handles and Port
--
-- When the listener recieves 'Ping' it will return 'Pong'.
--
-- If it recieves 'QueryPort', then the listener
-- responds with 'ReplyPort' with 'Port',
ipcListener
    :: forall m. (MonadIO m, MonadCatch m, MonadMask m)
    => ProtocolDuration
    -> ReadHandle
    -> WriteHandle
    -> Port
    -> m ()
ipcListener protocolDuration readHandle@(ReadHandle rHndl) writeHandle@(WriteHandle wHndl) port = do
    checkHandles readHandle writeHandle
    handleMsgIn `catches` [Handler handler, Handler handleMsgError] `finally` shutdown
  where
    handleMsgIn :: m ()
    handleMsgIn = do
        liftIO $ hSetNewlineMode rHndl noNewlineTranslation
        send Started -- Send the message first time the IPC is up!

        let frequencyFunction = case protocolDuration of
                                    SingleMessage -> void
                                    MultiMessage  -> forever

        -- Fetch message and respond to it
        frequencyFunction $ do
            msgIn               <- readMessage readHandle        -- Read message
            messageByteString   <- handleIPCProtocol port msgIn  -- Respond
            sendMessage writeHandle messageByteString            -- Write to client/server

    send :: MsgOut -> m ()
    send = sendMessage writeHandle

    handler :: IOError -> m ()
    handler err = do
        liftIO $ when (isEOFError err) $ logError "its an eof"
        throwM IPCException

    shutdown :: m ()
    shutdown = liftIO $ do
        hClose rHndl
        hClose wHndl
        hFlush stdout

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
-- Placeholder
--------------------------------------------------------------------------------

-- | Use this until we find suitable logging library
logError :: Text -> IO ()
logError _ = return ()

--------------------------------------------------------------------------------
-- Predicates
--------------------------------------------------------------------------------

-- | Checks if given 'NodeIPCException' is 'IPCException'
isIPCException :: NodeIPCException -> Bool
isIPCException IPCException = True
isIPCException _            = False

-- | Checks if given 'NodeIPCException' is 'HandleClosed'
isHandleClosed :: NodeIPCException -> Bool
isHandleClosed (HandleClosed _) = True
isHandleClosed _                = False

-- | Checks if given 'NodeIPCException' is 'UnreadableHandle'
isUnreadableHandle :: NodeIPCException -> Bool
isUnreadableHandle (UnreadableHandle _) = True
isUnreadableHandle _                    = False

-- | Checks if given 'NodeIPCException' is 'UnwritableHandle'
isUnwritableHandle :: NodeIPCException -> Bool
isUnwritableHandle (UnwritableHandle _) = True
isUnwritableHandle _                    = False

-- | Checks if given 'NodeIPCException' is 'NodeChannelNotFound'
isNodeChannelCannotBeFound :: NodeIPCException -> Bool
isNodeChannelCannotBeFound NodeChannelNotFound = True
isNodeChannelCannotBeFound _                   = False
