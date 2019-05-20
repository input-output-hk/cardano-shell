{-| Node IPC module. For details please read the spec:

<https://github.com/input-output-hk/cardano-shell/blob/develop/specs/CardanoShellSpec.pdf>
-}

module Cardano.Shell.NodeIPC
    (-- * Data types
      Port(..)
    , MsgIn(..)
    , MsgOut(..)
    , ReadHandle(..)
    , WriteHandle(..)
     -- * IPC protocol
    , ProtocolDuration (..)
    , startNodeJsIPC
    , startIPC
    , handleIPCProtocol
    , clientIPCListener
    , testStartNodeIPC
    , ServerHandles (..)
    , ClientHandles (..)
    , closeFullDuplexAnonPipesHandles
    , createFullDuplexAnonPipesHandles
    , bracketFullDuplexAnonPipesHandles
    , serverReadWrite
     -- ** Exceptions
    , NodeIPCException(..)
    , MessageSendFailure(..)
    , MessageException(..)
     -- * Used for testing
    , sendMessage
    , readMessage
    , exampleWithFD
    , exampleWithProcess
    , getReadWriteHandles
    , getHandleFromEnv
    -- * Predicates
    , isIPCException
    , isHandleClosed
    , isUnreadableHandle
    , isUnwritableHandle
    , isNodeChannelCannotBeFound
    ) where

import           Cardano.Shell.NodeIPC.Example (exampleWithFD,
                                                exampleWithProcess,
                                                getHandleFromEnv,
                                                getReadWriteHandles)
#endif
import           Cardano.Shell.NodeIPC.Lib (ClientHandles (..),
                                            MessageSendFailure (..), MsgIn (..),
                                            MsgOut (..), NodeIPCException (..),
                                            Port (..), ProtocolDuration (..),
                                            ServerHandles (..),
                                            bracketFullDuplexAnonPipesHandles,
                                            clientIPCListener,
                                            closeFullDuplexAnonPipesHandles,
                                            createFullDuplexAnonPipesHandles,
                                            handleIPCProtocol, isHandleClosed,
                                            isIPCException,
                                            isNodeChannelCannotBeFound,
                                            isUnreadableHandle,
                                            isUnwritableHandle, serverReadWrite,
                                            startIPC, startNodeJsIPC,
                                            testStartNodeIPC)
import           Cardano.Shell.NodeIPC.Message (MessageException (..),
                                                ReadHandle (..),
                                                WriteHandle (..), readMessage,
                                                sendMessage)
