{-| Node IPC module. For details please read the spec:

<https://github.com/input-output-hk/cardano-shell/blob/develop/specs/CardanoShellSpec.pdf>
-}

{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}

module Cardano.Shell.NodeIPC.Lib
    ( startNodeJsIPC
    , startIPC
    , Port (..)
    , ProtocolDuration (..)
    , handleIPCProtocol
    , clientIPCListener
    , testStartNodeIPC
    , ServerHandles (..)
    , ClientHandles (..)
    , closeFullDuplexAnonPipesHandles
    , createFullDuplexAnonPipesHandles
    , bracketFullDuplexAnonPipesHandles
    , serverReadWrite
    -- * Testing
    , getIPCHandle
    , getHandleFromEnv
    , MsgIn(..)
    , MsgOut(..)
    , NodeIPCError(..)
    , MessageSendFailure(..)
    -- * Predicates
    , isIPCError
    , isHandleClosed
    , isUnreadableHandle
    , isUnwritableHandle
    , isNodeChannelCannotBeFound
    ) where

import           Cardano.Prelude hiding (catches, finally, handle)

import           Control.Exception.Safe (Handler (..), catches, finally)
import           Data.Aeson (FromJSON (parseJSON), ToJSON (toEncoding),
                             defaultOptions, genericParseJSON,
                             genericToEncoding)
import           Data.Aeson.Types (Options, SumEncoding (ObjectWithSingleField),
                                   sumEncoding)
import           GHC.IO.Handle (hIsEOF, hIsOpen, hIsReadable, hIsWritable)
import           GHC.IO.Handle.FD (fdToHandle)

import           System.Environment (lookupEnv)
import           System.IO (BufferMode (..), hClose, hFlush, hSetBuffering,
                            hSetNewlineMode, noNewlineTranslation)
import           System.IO.Error (IOError, isEOFError)
import           System.Process (createPipe)
import           Test.QuickCheck (Arbitrary (..), Gen, arbitraryASCIIChar,
                                  choose, elements, listOf1, oneof)

import           Cardano.Shell.NodeIPC.Message (MessageException,
                                                ReadHandle (..),
                                                WriteHandle (..), readMessage,
                                                sendMessage)
import           Prelude (String)

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
    arbitrary = oneof
        [ return QueryPort
        , return Ping
        , MessageInFailure <$> arbitrary
        -- , return Shutdown
        ]

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

-- | Message that can be used to let the other know the that exception had occured
data MessageSendFailure
    = ParseError Text
    | GeneralFailure
    deriving (Show, Eq, Generic)

instance Arbitrary MessageSendFailure where
    arbitrary = oneof
        [ ParseError <$> genSafeText
        , return GeneralFailure
        ]

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
data NodeIPCError
    = NodeChannelNotFound Text
    -- ^ Node channel was not found
    | UnableToParseNodeChannel Text
    -- ^ Unable to parse given 'Text' as File descriptor
    | IPCError
    -- ^ Exception thrown when there's something wrong with IPC
    | HandleClosed Handle
    -- ^ Given handle is closed therefore cannot be used
    | HandleEOF Handle
    -- ^ Given handle End Of File
    | UnreadableHandle Handle
    -- ^ Given handle cannot be used to read
    | UnwritableHandle Handle
    -- ^ Given handle cannot be used to write
    | NoStdIn
    deriving (Eq)

instance Show NodeIPCError where
    show = \case
        NodeChannelNotFound envName ->
            "Environment variable cannot be found: " <> strConv Lenient envName
        UnableToParseNodeChannel err ->
            "Unable to parse file descriptor: " <> strConv Lenient err
        IPCError ->
            "IOError has occured"
        HandleClosed h ->
            "Given handle is closed: " <> show h
        HandleEOF h ->
            "Given handle is at EOF: " <> show h
        UnreadableHandle h ->
            "Unable to read with given handle: " <> show h
        UnwritableHandle h ->
            "Unable to write with given handle: " <> show h
        NoStdIn -> "createProcess returned Nothing when creating pipes for the subprocess"

-- | Acquire a Handle that can be used for IPC from Environment
getHandleFromEnv :: String -> IO (Either NodeIPCError Handle)
getHandleFromEnv envName = runExceptT $ do
    mFdstring <- liftIO $ lookupEnv envName
    case mFdstring of
        Nothing -> throwError $ NodeChannelNotFound $ toS envName
        Just fdstring ->
            case readEither fdstring of
                Left err -> throwError $ UnableToParseNodeChannel $ toS err
                Right fd -> liftIO (fdToHandle fd)

getIPCHandle :: IO (Either NodeIPCError Handle)
getIPCHandle = getHandleFromEnv "NODE_CHANNEL_FD"

-- | Start IPC with given 'ReadHandle', 'WriteHandle' and 'Port'
startIPC
    :: ProtocolDuration
    -> ReadHandle
    -> WriteHandle
    -> Port
    -> IO (Either NodeIPCError ())
startIPC protocolDuration readHandle writeHandle port =
    runExceptT $ ipcListener protocolDuration readHandle writeHandle port

-- | Start IPC with NodeJS
--
-- This only works if NodeJS spawns the Haskell executable as child process
-- (See @server.js@ as an example)
startNodeJsIPC
    :: ProtocolDuration
    -> Port
    -> IO (Either NodeIPCError ())
startNodeJsIPC protocolDuration port = do
    eHandle <- getIPCHandle
    runIPCListener eHandle
  where
    runIPCListener :: Either NodeIPCError Handle -> IO (Either NodeIPCError ())
    runIPCListener (Left nodeIPCError) = return . Left $ nodeIPCError
    runIPCListener (Right handle) = do
        let readHandle  = ReadHandle handle
        let writeHandle = WriteHandle handle
        liftIO $ runExceptT $ ipcListener protocolDuration readHandle writeHandle port

-- | Function for handling the protocol
handleIPCProtocol :: Port -> MsgIn -> IO MsgOut
handleIPCProtocol (Port port) = \case
    QueryPort          -> pure (ReplyPort port)
    Ping               -> pure Pong
    -- Send message, flush buffer, shutdown. Since it's complicated to reason with another
    -- thread that shuts down the program after some time, we do it immediately.
    Shutdown           -> return ShutdownInitiated >> exitWith (ExitFailure 22)
    MessageInFailure f -> pure $ MessageOutFailure f

-- | Start IPC listener with given Handles and Port
--
-- When the listener recieves 'Ping' it will return 'Pong'.
--
-- If it recieves 'QueryPort', then the listener
-- responds with 'ReplyPort' with 'Port',
ipcListener
    :: ProtocolDuration
    -> ReadHandle
    -> WriteHandle
    -> Port
    -> ExceptT NodeIPCError IO ()
ipcListener protocolDuration readHandle@(ReadHandle rHndl) writeHandle@(WriteHandle wHndl) port = do
    checkHandles readHandle writeHandle
    handleMsgIn `catches` [Handler handler, Handler handleMsgError]
    `finally`
    shutdown
  where
    handleMsgIn :: ExceptT NodeIPCError IO ()
    handleMsgIn = do
        liftIO $ hSetNewlineMode rHndl noNewlineTranslation
        send Started -- Send the message first time the IPC is up!

        let frequencyFunction = case protocolDuration of
                                    SingleMessage -> void
                                    MultiMessage  -> forever

        -- Fetch message and respond to it
        liftIO $ frequencyFunction $ do
            msgIn               <- readMessage readHandle        -- Read message
            messageByteString   <- handleIPCProtocol port msgIn  -- Respond
            sendMessage writeHandle messageByteString            -- Write to client/server

    send :: MsgOut -> ExceptT NodeIPCError IO ()
    send = sendMessage writeHandle

    shutdown :: ExceptT NodeIPCError IO ()
    shutdown = do
        liftIO $ do
            hClose rHndl
            hClose wHndl
            hFlush stdout
        throwError IPCError

    handleMsgError :: MessageException -> ExceptT NodeIPCError IO ()
    handleMsgError err = do
        liftIO $ logError "Unexpected message"
        send $ MessageOutFailure $ ParseError $ show err

    handler :: IOError -> ExceptT NodeIPCError IO ()
    handler err =
        when (isEOFError err) $ shutdown


-- | Check if given two handles are usable (i.e. Handle is open, can be used to read/write)
checkHandles :: ReadHandle -> WriteHandle -> ExceptT NodeIPCError IO ()
checkHandles (ReadHandle rHandle) (WriteHandle wHandle) = do
    checkHandle rHandle hIsOpen (HandleClosed rHandle)
    checkHandle wHandle hIsOpen (HandleClosed wHandle)
    checkHandle rHandle hIsReadable (UnreadableHandle rHandle)
    checkHandle wHandle hIsWritable (UnwritableHandle wHandle)
  where
    -- | Utility function for checking a handle.
    checkHandle :: Handle -> (Handle -> IO Bool) -> NodeIPCError -> ExceptT NodeIPCError IO ()
    checkHandle handle pre exception = do
        result <- liftIO $ pre handle
        when (not result) $ throwError exception

-- | Client side IPC protocol.
clientIPCListener
    :: ProtocolDuration
    -> ClientHandles
    -> Port
    -- ^ This is really making things confusing. A Port is here,
    -- but it's determined on the client side, not before.
    -> IO (Either NodeIPCError ())
clientIPCListener duration clientHandles port =
    runExceptT $ ipcListener
        duration
        (getClientReadHandle clientHandles)
        (getClientWriteHandle clientHandles)
        port

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
serverReadWrite :: ServerHandles -> MsgIn -> IO (Either NodeIPCError MsgOut)
serverReadWrite serverHandles msgIn = runExceptT $ do

    let readHandle      = getServerReadHandle serverHandles
    let writeHandle     = getServerWriteHandle serverHandles

    -- First check if the handles are valid!
    checkHandles readHandle writeHandle

    -- Then send message and __block__ read.
    sendMessage writeHandle msgIn

    -- Check if the handle is at End Of Line, we need to do this
    -- here since we @hIsEOF@ __blocks__ as well.
    whenM (liftIO . hIsEOF . getReadHandle $ readHandle) $
        throwError . HandleEOF . getReadHandle $ readHandle

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


-- | Test 'startIPC'
testStartNodeIPC :: (ToJSON msg) => Port -> msg -> IO (MsgOut, MsgOut)
testStartNodeIPC port msg = do
    (clientReadHandle, clientWriteHandle) <- getReadWriteHandles
    (serverReadHandle, serverWriteHandle) <- getReadWriteHandles

    -- Start the server
    (_, responses) <-
        startIPC
            SingleMessage
            serverReadHandle
            clientWriteHandle
            port
        `concurrently`
        do
            -- Use these functions so you don't pass the wrong handle by mistake
            let readClientMessage :: IO MsgOut
                readClientMessage = readMessage clientReadHandle

            let sendServer :: (ToJSON msg) => msg -> IO ()
                sendServer = sendMessage serverWriteHandle

            -- Communication starts here
            started     <- readClientMessage
            sendServer msg
            response    <- readClientMessage
            return (started, response)

    return responses

--------------------------------------------------------------------------------
-- Placeholder
--------------------------------------------------------------------------------

-- | Use this until we find suitable logging library
logError :: Text -> IO ()
logError _ = return ()

--------------------------------------------------------------------------------
-- Predicates
--------------------------------------------------------------------------------

-- | Checks if given 'NodeIPCError' is 'IPCError'
isIPCError :: NodeIPCError -> Bool
isIPCError IPCError = True
isIPCError _        = False

-- | Checks if given 'NodeIPCError' is 'HandleClosed'
isHandleClosed :: NodeIPCError -> Bool
isHandleClosed (HandleClosed _) = True
isHandleClosed _                = False

-- | Checks if given 'NodeIPCError' is 'UnreadableHandle'
isUnreadableHandle :: NodeIPCError -> Bool
isUnreadableHandle (UnreadableHandle _) = True
isUnreadableHandle _                    = False

-- | Checks if given 'NodeIPCError' is 'UnwritableHandle'
isUnwritableHandle :: NodeIPCError -> Bool
isUnwritableHandle (UnwritableHandle _) = True
isUnwritableHandle _                    = False

-- | Checks if given 'NodeIPCError' is 'NodeChannelNotFound'
isNodeChannelCannotBeFound :: NodeIPCError -> Bool
isNodeChannelCannotBeFound (NodeChannelNotFound _) = True
isNodeChannelCannotBeFound _                       = False
