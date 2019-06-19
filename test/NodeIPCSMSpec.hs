{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving  #-}

-- Yes, yes, this is an exception.
{-# OPTIONS_GHC -fno-warn-orphans #-}

module NodeIPCSMSpec
    ( nodeIPCSMSpec
    , prop_nodeIPC
    ) where

import           Cardano.Prelude

import           Data.TreeDiff (ToExpr (..))

import           Test.Hspec (Spec, describe, it)

import           Test.QuickCheck (Gen, Property, arbitrary, generate, oneof,
                                  (===))
import           Test.QuickCheck.Monadic (PropertyM, assert, monadicIO, run)

import           Test.StateMachine
import           Test.StateMachine.Types
import qualified Test.StateMachine.Types.Rank2 as Rank2

import           Cardano.Shell.NodeIPC (MessageSendFailure (..), MsgIn (..),
                                        MsgOut (..), NodeIPCException (..),
                                        Port (..), ProtocolDuration (..),
                                        ServerHandles (..), clientIPCListener,
                                        closeFullDuplexAnonPipesHandles,
                                        handleIPCProtocol,
                                        createFullDuplexAnonPipesHandles,
                                        readMessage, serverReadWrite)

-------------------------------------------------------------------------------
-- Tests
-------------------------------------------------------------------------------

nodeIPCSMSpec :: Spec
nodeIPCSMSpec = do
    describe "Node IPC state machine" $ do
        it "should return the correct response" $ do
            prop_nodeIPC

prop_nodeIPC :: Property
prop_nodeIPC =

    forAllCommands smUnused (Just 200) $ \cmds -> monadicIO $ do
        withServerHandles $ \serverHandles -> do

            let nodeSM                      = nodeIPCSM serverHandles

            -- Run the actual commands
            (hist, _model, res)             <- runCommands nodeSM cmds

            -- Pretty the commands
            prettyCommands nodeSM hist $ checkCommandNames cmds (res === Ok)

-- | Weird, but ok.
smUnused :: StateMachine Model Action IO Response
smUnused = nodeIPCSM $ panic "used env during command generation"

-- | All the setup for the tests/model is here.
withServerHandles :: (ServerHandles -> PropertyM IO ()) -> PropertyM IO ()
withServerHandles runServer = do

    -- Create the arbitrary port where the IPC server is running on
    port                            <- run $ generate arbitrary

    -- Create the handles for a full duplex communcation (we can use two sockets as well)
    (serverHandles, clientHandles) <- liftIO createFullDuplexAnonPipesHandles

    -- Create the IPC server, it's using async, but it can be a separate process.
    clientIPCAsync                  <-
        liftIO $ async $ clientIPCListener MultiMessage clientHandles (handleIPCProtocol $ Port port)

    -- Communication starts here
    started <- run $ readMessage (getServerReadHandle serverHandles)

    -- The first message must be @Started@.
    assert $ started == Started

    -- Run the server side checks
    runServer serverHandles

    -- Close async
    run $ cancel clientIPCAsync

    -- Close handles
    run $ closeFullDuplexAnonPipesHandles (serverHandles, clientHandles)

-------------------------------------------------------------------------------
-- Language
-------------------------------------------------------------------------------

-- | The list of commands/actions the model can take.
data Action (r :: Type -> Type)
    = PingCmd
    | QueryPortCmd
    | ShutdownCmd
    deriving (Show, Generic1, Rank2.Foldable, Rank2.Traversable, Rank2.Functor, CommandNames)

-- | The types of responses of the model.
data Response (r :: Type -> Type)
    = StartedResponse
    | PongResponse
    | ReplyPortResponse Word16
    | ShutdownInitiatedResponse
    deriving (Show, Generic1, Rank2.Foldable, Rank2.Traversable, Rank2.Functor)

-- | The types of error that can occur in the model.
data Error
    = UnexpectedError
    | ExitCodeError ExitCode
    | IPCExceptionError NodeIPCException
    deriving (Show)

instance Exception Error

-- TODO(KS): ISO? Not really painful at this point, so KISS.

-- | Abstract to concrete.
actionToConcrete :: Action r -> MsgIn
actionToConcrete PingCmd      = Ping
actionToConcrete QueryPortCmd = QueryPort
actionToConcrete ShutdownCmd  = Shutdown

-- | Abstract to concrete.
responseToConcreate :: Response r -> MsgOut
responseToConcreate StartedResponse           = Started
responseToConcreate PongResponse              = Pong
responseToConcreate (ReplyPortResponse port)  = ReplyPort port
responseToConcreate ShutdownInitiatedResponse = ShutdownInitiated

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

deriving instance ToExpr (Model Concrete)

deriving instance ToExpr MsgIn
deriving instance ToExpr MessageSendFailure
deriving instance ToExpr MsgOut
deriving instance ToExpr InputOutputMessages

-------------------------------------------------------------------------------
-- The model we keep track of
-------------------------------------------------------------------------------

-- | Yes, this costs more but for a simple test it's acceptable.
-- The readability / performance tradeoff is good here.
data InputOutputMessages = InputOutputMessages
   { inputMessages  :: [MsgIn]
   , outputMessages :: [MsgOut]
   } deriving (Eq, Show, Generic)

-- | The model contains the messages that were communicated in the protocol.
data Model (r :: Type -> Type)
    = RunningModel !InputOutputMessages
    | ShutdownInit
    deriving (Eq, Show, Generic)

-- | Initially, we don't have any messages in the protocol.
initialModel :: Model r
initialModel = RunningModel $ InputOutputMessages
    { inputMessages     = []
    , outputMessages    = []
    }

-------------------------------------------------------------------------------
-- State machine
-------------------------------------------------------------------------------

nodeIPCSM :: ServerHandles -> StateMachine Model Action IO Response
nodeIPCSM serverHandles = StateMachine
    { initModel     = initialModel
    , transition    = mTransitions
    , precondition  = mPreconditions
    , postcondition = mPostconditions
    , generator     = mGenerator
    , invariant     = Nothing
    , shrinker      = mShrinker
    , semantics     = mSemantics
    , mock          = mMock
    , distribution  = Nothing
    }
  where
    -- | Let's handle just Ping/Pong for now.
    mTransitions :: Model r -> Action r -> Response r -> Model r
    mTransitions (RunningModel model) action response   = RunningModel $ model
        { inputMessages     = actionToConcrete action       : inputMessages model
        , outputMessages    = responseToConcreate response  : outputMessages model
        }
    mTransitions _ ShutdownCmd _                        = ShutdownInit
    mTransitions ShutdownInit _ _                       = ShutdownInit

    -- | Preconditions for this model.
    mPreconditions :: Model Symbolic -> Action Symbolic -> Logic
    mPreconditions (RunningModel model) _   =
        length (inputMessages model) - length (outputMessages model) .== 0
    mPreconditions ShutdownInit         _   = Bot

    -- | Post conditions for the system.
    mPostconditions :: Model Concrete -> Action Concrete -> Response Concrete -> Logic
    mPostconditions _   PingCmd         PongResponse                = Top -- valid
    mPostconditions _   PingCmd         _                           = Bot -- invalid
    mPostconditions _   QueryPortCmd    (ReplyPortResponse _)       = Top -- valid
    mPostconditions _   QueryPortCmd    _                           = Bot -- invalid
    mPostconditions _   ShutdownCmd     (ShutdownInitiatedResponse) = Top
    mPostconditions _   ShutdownCmd     _                           = Bot

    -- | Generator for symbolic actions.
    mGenerator :: Model Symbolic -> Maybe (Gen (Action Symbolic))
    mGenerator ShutdownInit = Nothing
    mGenerator _            = Just $ oneof
        [ return PingCmd
        , return QueryPortCmd
        --, return ShutdownCmd
        ]

    -- | Trivial shrinker. __No shrinker__.
    mShrinker :: Model Symbolic -> Action Symbolic -> [Action Symbolic]
    mShrinker _ _ = []

    -- | Here we'd do the dispatch to the actual SUT.
    mSemantics :: Action Concrete -> IO (Response Concrete)
    mSemantics PingCmd      = handleIPCProtocolTest Ping
    mSemantics QueryPortCmd = handleIPCProtocolTest QueryPort
    mSemantics ShutdownCmd  = handleIPCProtocolTest Shutdown

    handleIPCProtocolTest :: MsgIn -> IO (Response Concrete)
    handleIPCProtocolTest actionIn = do
        -- The first message is @Started@

        -- _ <- traceIO ("**************************" :: Text) ("START - " :: Text)
        -- _ <- traceIO (show actionIn :: Text) ("IN - " :: Text)

        -- Fetch message and respond to it, this is __blocking__.
        msgIn :: Either NodeIPCException MsgOut <- try $ serverReadWrite serverHandles actionIn

        -- _ <- traceIO (show msgIn :: Text) ("OUT - " :: Text)

        case msgIn of
            Right Started               -> return StartedResponse
            Right Pong                  -> return PongResponse
            Right (ReplyPort p)         -> return (ReplyPortResponse p)
            Right (MessageOutFailure _) -> return StartedResponse
            -- ^ This is no-op, ignored. Yes, yes, should be in the model.

            Left (HandleEOF _)          -> return ShutdownInitiatedResponse

            Left _unexpectedException   -> throwIO UnexpectedError
            Right ShutdownInitiated     -> throwIO UnexpectedError


    -- | What is the mock for?
    mMock :: Model Symbolic -> Action Symbolic -> GenSym (Response Symbolic)
    mMock _ PingCmd      = return PongResponse
    mMock _ QueryPortCmd = return $ ReplyPortResponse 12345 -- Random number
    mMock _ ShutdownCmd  = return ShutdownInitiatedResponse


