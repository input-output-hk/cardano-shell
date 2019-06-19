{-| Node IPC module. For details please read the spec:

<https://github.com/input-output-hk/cardano-shell/blob/develop/specs/CardanoShellSpec.pdf>
-}

{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Cardano.Shell.NodeIPC.Lib
    ( startNodeJsIPC
    , startIPC
    , Port (..)
    , ProtocolDuration (..)
    , clientIPCListener
    , ServerHandles (..)
    , ClientHandles (..)
    , closeFullDuplexAnonPipesHandles
    , createFullDuplexAnonPipesHandles
    , bracketFullDuplexAnonPipesHandles
    , serverReadWrite
    -- * Testing
    , getIPCHandle
    , getReadWriteHandles
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
import           GHC.IO.Handle (hIsOpen, hIsReadable, hIsWritable, hIsEOF)
import           GHC.IO.Handle.FD (fdToHandle)

import           System.Environment (lookupEnv)
import           System.Process (createPipe)

import           System.IO (BufferMode (..), hClose, hFlush, hSetBuffering,
                            hSetNewlineMode, noNewlineTranslation)
import           System.IO.Error (IOError, isEOFError)

import           Test.QuickCheck (Arbitrary (..), Gen, arbitraryASCIIChar,
                                  choose, elements, listOf1)

import           Cardano.Shell.NodeIPC.Message (MessageException,
                                                ReadHandle (..),
                                                WriteHandle (..), readMessage,
                                                sendMessage)

import qualified Prelude as P (Show (..))

-- | When using pipes, __the write doesn't block, but the read blocks__!
-- As a consequence, we eiter need to use IDs to keep track of the client/server pair,
-- or (read) block so we know which message pair arrived.
-- This might seems an overkill for this task, but it's actually required if we
-- want to reason about it and test it properly.
--
-- >>> (readEnd, writeEnd) <- createPipe
--
-- >>> replicateM 100 $ sendMessage (WriteHandle writeEnd) Cardano.Shell.NodeIPC.Ping
-- [(),(),(),(),(),(),(),(),(),(),(),(),(),(),(),(),(),(),(),(),(),(),(),(),(),(),(),(),(),(),(),(),(),(),(),(),(),(),(),(),(),(),(),(),(),(),(),(),(),(),(),(),(),(),(),(),(),(),(),(),(),(),(),(),(),(),(),(),(),(),(),(),(),(),(),(),(),(),(),(),(),(),(),(),(),(),(),(),(),(),(),(),(),(),(),(),(),(),(),()]
--
-- >>> mesg <- replicateM 100 ((readMessage (ReadHandle readEnd)) :: IO MsgIn)
--
-- >>> mesg <- (readMessage (ReadHandle readEnd)) :: IO MsgIn
--
--
-- Blocked!

-- | The way the IPC protocol works - it either responds to a single
-- __IPC__ message or it remains in a loop responding to multiple messages.
data ProtocolDuration
    = SingleMessage
    -- ^ Responds to a single message and exits
    | MultiMessage
    -- ^ Runs forever responding to messages
    deriving (Eq, Show)


-- We look at the messages from the perspective of the client.
--
-- @MsgIn@ ---> CLIENT --> @MsgOut@
--


-- | Message that can be used to let the other know the that exception had occured
data MessageSendFailure
    = ParseError Text
    | GeneralFailure
    deriving (Show, Eq, Generic)

opts :: Options
opts = defaultOptions { sumEncoding = ObjectWithSingleField }

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
    = NodeChannelNotFound Text
    -- ^ Node channel was not found
    | UnableToParseNodeChannel Text
    -- ^ Unable to parse given 'Text' as File descriptor
    | IPCException
    -- ^ Exception thrown when there's something wrong with IPC
    | HandleClosed Handle
    -- ^ Given handle is closed therefore cannot be used
    | HandleEOF Handle
    -- ^ Given handle End Of File
    | UnreadableHandle Handle
    -- ^ Given handle cannot be used to read
    | UnwritableHandle Handle
    -- ^ Given handle cannot be used to write

instance Show NodeIPCException where
    show = \case
        NodeChannelNotFound envName ->
            "Environment variable cannot be found: " <> strConv Lenient envName
        UnableToParseNodeChannel err ->
            "Unable to parse file descriptor: " <> strConv Lenient err
        IPCException ->
            "IOError has occured"
        HandleClosed h ->
            "Given handle is closed: " <> show h
        HandleEOF h ->
            "Given handle is at EOF: " <> show h
        UnreadableHandle h ->
            "Unable to read with given handle: " <> show h
        UnwritableHandle h ->
            "Unable to write with given handle: " <> show h

instance Exception NodeIPCException

-- | Acquire a Handle that can be used for IPC
getIPCHandle :: IO (Either NodeIPCException Handle)
getIPCHandle = do
    mFdstring <- liftIO $ lookupEnv "NODE_CHANNEL_FD"
    case mFdstring of
        Nothing -> pure $ Left $ NodeChannelNotFound "NODE_CHANNEL_FD"
        Just fdstring -> case readEither fdstring of
            Left err -> pure $ Left $ UnableToParseNodeChannel $ toS err
            Right fd -> liftIO $ Right <$> fdToHandle fd

-- | Start IPC with given 'ReadHandle', 'WriteHandle' and 'Port'
startIPC :: forall a b m. (FromJSON a, ToJSON b, MonadIO m, MonadMask m) => ProtocolDuration -> ReadHandle -> WriteHandle -> (a -> IO b) -> m (Either NodeIPCException (Async (), b -> IO ()))
startIPC protocolDuration readHandle writeHandle handler = ipcListener protocolDuration readHandle writeHandle handler

-- | Start IPC with NodeJS
--
-- This only works if NodeJS spawns the Haskell executable as child process
-- (See @server.js@ as an example)
startNodeJsIPC :: forall a b m. (FromJSON a, ToJSON b, MonadIO m, MonadMask m) => ProtocolDuration -> (a -> IO b) -> m (Either NodeIPCException (Async (), b -> IO ()))
startNodeJsIPC protocolDuration handler = do
    eHandle          <- liftIO $ getIPCHandle
    case eHandle of
      Left err -> pure $ Left $ err
      Right handle -> do
        let readHandle  = ReadHandle handle
        let writeHandle = WriteHandle handle

        ipcListener protocolDuration readHandle writeHandle handler

-- | Start IPC listener with given Handles and Port
--
-- When the listener recieves 'Ping' it will return 'Pong'.
--
-- If it recieves 'QueryPort', then the listener
-- responds with 'ReplyPort' with 'Port',
ipcListener
    :: forall a b m. (MonadIO m, MonadCatch m, MonadMask m, FromJSON a, ToJSON b)
    => ProtocolDuration
    -> ReadHandle
    -> WriteHandle
    -> (a -> IO b)
    -> m (Either NodeIPCException (Async (), b -> IO ()))
ipcListener protocolDuration readHandle@(ReadHandle rHndl) writeHandle@(WriteHandle wHndl) handler = do
    liftIO $ checkHandles readHandle writeHandle
    handleMsgIn `catches` [] `finally` shutdown
  where
    handleMsgIn :: m (Either NodeIPCException (Async (), b -> IO ()))
    handleMsgIn = do
        liftIO $ hSetNewlineMode rHndl noNewlineTranslation

        let frequencyFunction = case protocolDuration of
                                    SingleMessage -> void
                                    MultiMessage  -> forever

        -- Fetch message and respond to it
        async <- liftIO $ async $ frequencyFunction $ liftIO $ do
            msgIn               <- readMessage readHandle  -- Read message
            messageByteString   <- handler msgIn           -- Respond
            send messageByteString                         -- Write to client/server
        pure $ Right $ (async,send)

    -- TODO, put the messages into a queue, so if 2 threads try to write at a time, they dont get interleaved
    send :: b -> IO ()
    send = sendMessage writeHandle

    shutdown :: m ()
    shutdown = liftIO $ do
        hClose rHndl
        hClose wHndl
        hFlush stdout

    --handleMsgError :: MessageException -> m ()
    --handleMsgError err = do
    --    liftIO $ logError "Unexpected message"
    --    send $ MessageOutFailure $ ParseError $ show err


--errorHandler :: (MonadIO m, MonadCatch m) => IOError -> m (Either NodeIPCException a)
--errorHandler err = when (isEOFError err) $ pure $ Left IPCException


-- | Check if given two handles are usable (i.e. Handle is open, can be used to read/write)
checkHandles :: ReadHandle -> WriteHandle -> IO ()
checkHandles (ReadHandle rHandle) (WriteHandle wHandle) = do
    checkHandle rHandle hIsOpen (HandleClosed rHandle)
    checkHandle wHandle hIsOpen (HandleClosed wHandle)
    checkHandle rHandle hIsReadable (UnreadableHandle rHandle)
    checkHandle wHandle hIsWritable (UnwritableHandle wHandle)
  where
    -- | Utility function for checking a handle.
    checkHandle :: Handle -> (Handle -> IO Bool) -> NodeIPCException -> IO ()
    checkHandle handle pre exception = do
        result <- pre handle
        when (not result) $ throwM exception

-- | Client side IPC protocol.
clientIPCListener
    :: forall a b m. (MonadIO m, MonadMask m, FromJSON a, ToJSON b)
    => ProtocolDuration
    -> ClientHandles
    -> (a -> IO b)
    -- ^ This is really making things confusing. A Port is here,
    -- but it's determined on the client side, not before.
    -> m (Either NodeIPCException (Async (), b -> IO ()))
clientIPCListener duration clientHandles handler =
    ipcListener
        duration
        (getClientReadHandle clientHandles)
        (getClientWriteHandle clientHandles)
        handler

-- | The set of handles for the server, the halves of one pipe.
data ServerHandles = ServerHandles
    { getServerReadHandle  :: !ReadHandle
    , getServerWriteHandle :: !WriteHandle
    }

-- | The set of handles for the client, the halves of one pipe.
data ClientHandles = ClientHandles
    { getClientReadHandle  :: !ReadHandle
    , getClientWriteHandle :: !WriteHandle
    }

-- | This is a __blocking call__ that sends the message to the client
-- and returns it's response, __after the client response arrives__.
serverReadWrite :: (ToJSON a, FromJSON b) => ServerHandles -> a -> IO b
serverReadWrite serverHandles msgIn = do

    let readHandle      = getServerReadHandle serverHandles
    let writeHandle     = getServerWriteHandle serverHandles

    -- First check if the handles are valid!
    checkHandles readHandle writeHandle

    -- Then send message and __block__ read.
    sendMessage writeHandle msgIn

    -- Check if the handle is at End Of Line, we need to do this
    -- here since we @hIsEOF@ __blocks__ as well.
    whenM (hIsEOF . getReadHandle $ readHandle) $
        throwM . HandleEOF . getReadHandle $ readHandle

    -- Read message
    readMessage readHandle

-- | A bracket function that can be useful.
bracketFullDuplexAnonPipesHandles
    :: ((ServerHandles, ClientHandles) -> IO ())
    -> IO ()
bracketFullDuplexAnonPipesHandles computationToRun =
    bracket
        createFullDuplexAnonPipesHandles
        closeFullDuplexAnonPipesHandles
        computationToRun

-- | Close the pipe handles.
closeFullDuplexAnonPipesHandles :: (ServerHandles, ClientHandles) -> IO ()
closeFullDuplexAnonPipesHandles (serverHandles, clientHandles) = do
    -- close the server side
    hClose $ getReadHandle  (getServerReadHandle serverHandles)
    hClose $ getWriteHandle (getServerWriteHandle serverHandles)

    -- close the client side
    hClose $ getReadHandle  (getClientReadHandle clientHandles)
    hClose $ getWriteHandle (getClientWriteHandle clientHandles)

-- | Creation of a two-way communication between the server and the client.
-- Full-duplex (two-way) communication normally requires two anonymous pipes.
-- TODO(KS): Bracket this!
createFullDuplexAnonPipesHandles :: IO (ServerHandles, ClientHandles)
createFullDuplexAnonPipesHandles = do

    (clientReadHandle, clientWriteHandle) <- getReadWriteHandles
    (serverReadHandle, serverWriteHandle) <- getReadWriteHandles

    let serverHandles = ServerHandles clientReadHandle serverWriteHandle
    let clientHandles = ClientHandles serverReadHandle clientWriteHandle

    return (serverHandles, clientHandles)

-- | Create a pipe for interprocess communication and return a
-- ('ReadHandle', 'WriteHandle') Handle pair.
getReadWriteHandles :: IO (ReadHandle, WriteHandle)
getReadWriteHandles = do
    (readHndl, writeHndl) <- createPipe

    hSetBuffering readHndl LineBuffering
    hSetBuffering writeHndl LineBuffering

    let readHandle  = ReadHandle readHndl
    let writeHandle = WriteHandle writeHndl

    return (readHandle, writeHandle)

--------------------------------------------------------------------------------
-- Placeholder
--------------------------------------------------------------------------------

-- | Use this until we find suitable logging library
--logError :: Text -> IO ()
--logError _ = return ()

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
isNodeChannelCannotBeFound (NodeChannelNotFound _) = True
isNodeChannelCannotBeFound _                       = False
