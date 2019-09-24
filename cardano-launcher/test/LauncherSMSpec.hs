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

module LauncherSMSpec
    ( launcherSMSpec
    , prop_launcher
    ) where

import           Cardano.Prelude

import           Data.TreeDiff (ToExpr (..))

import           Test.Hspec (Spec, describe, it)

import           Test.QuickCheck (Gen, Property, oneof, (===))
import           Test.QuickCheck.Monadic (monadicIO)

import           Test.StateMachine
import           Test.StateMachine.Types
import qualified Test.StateMachine.Types.Rank2 as Rank2

import           Cardano.Shell.Launcher (DaedalusExitCode (..),
                                         Isomorphism (..), RestartRunner (..),
                                         UpdateRunner (..),
                                         handleDaedalusExitCode)

-------------------------------------------------------------------------------
-- Tests
-------------------------------------------------------------------------------

launcherSMSpec :: Spec
launcherSMSpec = do
    describe "Launcher state machine" $ do
        it "should return the correct response" $ do
            prop_launcher

prop_launcher :: Property
prop_launcher =

    forAllCommands smUnused (Just 1000) $ \cmds -> monadicIO $ do

        -- Run the actual commands
        (hist, _model, res) <- runCommands launcherSM cmds

        -- Pretty the commands
        prettyCommands launcherSM hist $ checkCommandNames cmds (res === Ok)

-- | Weird, but ok.
smUnused :: StateMachine Model Action IO Response
smUnused = launcherSM

-------------------------------------------------------------------------------
-- Language
-------------------------------------------------------------------------------

-- Probably need to wrap in a newtype.
type UpdateExitCode = DaedalusExitCode
type WalletExitCode = DaedalusExitCode

-- | The list of commands/actions the model can take.
-- The __r__ type here is the polymorphic type param for symbolic and concrete @Action@.
data Action (r :: Type -> Type)
    = RunUpdateAction !UpdateExitCode !WalletExitCode
    -- ^ The update functions with @UpdateRunner@ and @RestartRunner@.
    | WalletSafeModeAction !WalletExitCode
    | WalletNormalModeAction !WalletExitCode
    deriving (Show, Generic1, Rank2.Foldable, Rank2.Traversable, Rank2.Functor, CommandNames)

-- | The types of responses of the model.
-- The __r__ type here is the polymorphic type param for symbolic and concrete @Response@.
data Response (r :: Type -> Type)
    = UpdateRunResponse
    | WalletSafeModeResponse
    | WalletNormalModeResponse
    | ExitCodeFailureResponse Int
    | ExitCodeSuccessResponse
    -- ^ The wallet completed the execution.
    deriving (Show, Generic1, Rank2.Foldable, Rank2.Traversable, Rank2.Functor)

-- | The types of error that can occur in the model.
data Error
    = ExitCodeError ExitCode
    | UnexpectedError
    deriving (Show)

-- | Do we need this instance?
instance Exception Error

-- TODO(KS): ISO? Not really painful at this point, so KISS.

-- | Abstract to concrete.
actionToConcrete :: Action r -> DaedalusExitCode
actionToConcrete (RunUpdateAction _ _)          = RunUpdate
actionToConcrete (WalletSafeModeAction _)       = RestartInGPUSafeMode
actionToConcrete (WalletNormalModeAction _)     = RestartInGPUNormalMode

-- | Abstract to concrete.
responseToConcrete :: Response r -> DaedalusExitCode
responseToConcrete UpdateRunResponse             = RunUpdate
responseToConcrete WalletSafeModeResponse        = RestartInGPUSafeMode
responseToConcrete WalletNormalModeResponse      = RestartInGPUNormalMode
responseToConcrete (ExitCodeFailureResponse ecf) = ExitCodeFailure ecf
responseToConcrete ExitCodeSuccessResponse       = ExitCodeSuccess

-- | Abstract to concrete.
concreteToResponse :: DaedalusExitCode -> Response r
concreteToResponse RunUpdate              = UpdateRunResponse
concreteToResponse RestartInGPUSafeMode   = WalletSafeModeResponse
concreteToResponse RestartInGPUNormalMode = WalletNormalModeResponse
concreteToResponse (ExitCodeFailure ecf)  = ExitCodeFailureResponse ecf
concreteToResponse ExitCodeSuccess        = ExitCodeSuccessResponse

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

deriving instance ToExpr (Model Concrete)

deriving instance ToExpr DaedalusExitCode
deriving instance ToExpr InputOutputMessages

-------------------------------------------------------------------------------
-- The model we keep track of
-------------------------------------------------------------------------------

-- | List of exit codes.
data InputOutputMessages = InputOutputMessages
   { returnedWalletExitCodes  :: ![DaedalusExitCode]
   , executionWalletExitCodes :: ![DaedalusExitCode]
   } deriving (Eq, Show, Generic)

-- | The model contains the messages that were communicated in the protocol.
data Model (r :: Type -> Type) = RunningModel !InputOutputMessages
    deriving (Eq, Show, Generic)

-- | Initially, we don't have any exit codes in the protocol.
initialModel :: Model r
initialModel = RunningModel $ InputOutputMessages
    { returnedWalletExitCodes   = []
    , executionWalletExitCodes  = []
    }

-------------------------------------------------------------------------------
-- State machine
-------------------------------------------------------------------------------

launcherSM :: StateMachine Model Action IO Response
launcherSM = StateMachine
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
        { returnedWalletExitCodes   = actionToConcrete action       : returnedWalletExitCodes model
        , executionWalletExitCodes  = responseToConcrete response   : executionWalletExitCodes model
        }

    -- | Preconditions for this model.
    mPreconditions :: Model Symbolic -> Action Symbolic -> Logic
    mPreconditions (RunningModel model) _   =
        length (returnedWalletExitCodes model) - length (executionWalletExitCodes model) .== 0

    -- | Post conditions for the system.
    -- This formatting is horrible, but it's kind of hard to make this any better.
    mPostconditions :: Model Concrete -> Action Concrete -> Response Concrete -> Logic

    mPostconditions _   (RunUpdateAction _ _)                               UpdateRunResponse           = Top
    mPostconditions _   (RunUpdateAction _               ExitCodeSuccess)   ExitCodeSuccessResponse     = Top
    -- If it's any other ExitCode but success, that is wrong.
    mPostconditions _   (RunUpdateAction ExitCodeSuccess ExitCodeSuccess)   _                           = Bot
    mPostconditions _   (RunUpdateAction _updaterFun     walletFunction )   exitCodeResponse            =
        walletFunction .== (responseToConcrete exitCodeResponse)

    -- The launcher exit code is what the wallet returns.
    mPostconditions _   (WalletSafeModeAction walletFunction)               exitCodeResponse            =
        walletFunction .== (responseToConcrete exitCodeResponse)

    -- The launcher exit code is what the wallet returns.
    mPostconditions _   (WalletNormalModeAction walletFunction)             exitCodeResponse            =
        walletFunction .== (responseToConcrete exitCodeResponse)

    -- | Generator for symbolic actions.
    mGenerator :: Model Symbolic -> Maybe (Gen (Action Symbolic))
    mGenerator _            = Just $ oneof
        [ RunUpdateAction <$> arbitraryDaedalusExitCode <*> arbitraryDaedalusExitCode
        , WalletSafeModeAction <$> arbitraryDaedalusExitCode
        , WalletNormalModeAction <$> arbitraryDaedalusExitCode
        ]

    -- | Trivial shrinker. __No shrinker__.
    mShrinker :: Model Symbolic -> Action Symbolic -> [Action Symbolic]
    mShrinker _ _ = []

    -- | Here we'd do the dispatch to the actual SUT.
    mSemantics :: Action Concrete -> IO (Response Concrete)
    mSemantics (RunUpdateAction updateFunctionDEC launcherFunctionDEC)  =
        let
            updateRunner :: UpdateRunner
            updateRunner = UpdateRunner . return $ isoFrom updateFunctionDEC

            restartRunner :: RestartRunner
            restartRunner = RestartRunner $ \_wm -> return $ isoFrom launcherFunctionDEC
        in
            concreteToResponse <$>
                handleDaedalusExitCode updateRunner restartRunner RunUpdate

    mSemantics (WalletSafeModeAction launcherFunctionDEC)               =
        let
            restartRunner :: RestartRunner
            restartRunner = RestartRunner $ \_wm -> return $ isoFrom launcherFunctionDEC
         in
            concreteToResponse <$>
                handleDaedalusExitCode doNotUse restartRunner RestartInGPUSafeMode

    mSemantics (WalletNormalModeAction launcherFunctionDEC)             =
        let
            restartRunner :: RestartRunner
            restartRunner = RestartRunner $ \_wm -> return $ isoFrom launcherFunctionDEC
        in
            concreteToResponse <$>
                handleDaedalusExitCode doNotUse restartRunner RestartInGPUNormalMode

    -- | Compare sybolic and SUT.
    mMock :: Model Symbolic -> Action Symbolic -> GenSym (Response Symbolic)
    mMock _ (RunUpdateAction _ _)       = return UpdateRunResponse
    mMock _ (WalletSafeModeAction _)    = return WalletSafeModeResponse
    mMock _ (WalletNormalModeAction _)  = return WalletNormalModeResponse

-- | A simple utility function so we don't have to pass panic around.
doNotUse :: a
doNotUse = panic "Should not be used!"

-- | Correct generation of @DaedalusExitCode@.
arbitraryDaedalusExitCode :: Gen DaedalusExitCode
arbitraryDaedalusExitCode = oneof
    [ return RunUpdate
    , return RestartInGPUSafeMode
    , return RestartInGPUNormalMode
    , ExitCodeFailure <$> (oneof $ map return $ [1..19] <> [23..256])
    , return ExitCodeSuccess
    ]

