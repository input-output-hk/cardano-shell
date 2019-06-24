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
    , ServerHandles (..)
    , ClientHandles (..)
    , closeFullDuplexAnonPipesHandles
    , createFullDuplexAnonPipesHandles
    , bracketFullDuplexAnonPipesHandles
    , serverReadWrite
     -- ** Exceptions
    , NodeIPCError(..)
    , MessageSendFailure(..)
    , MessageException(..)
     -- * Used for testing
    , sendMessage
    , readMessage
    , exampleWithFD
    , exampleServerWithProcess
    , getReadWriteHandles
    , getHandleFromEnv
    -- * Predicates
    , isIPCError
    , isHandleClosed
    , isUnreadableHandle
    , isUnwritableHandle
    , isNodeChannelCannotBeFound
    ) where

import           Cardano.Shell.NodeIPC.Lib (ClientHandles (..),
                                            MessageSendFailure (..), MsgIn (..),
                                            MsgOut (..), NodeIPCError (..),
                                            Port (..), ProtocolDuration (..),
                                            ServerHandles (..),
                                            bracketFullDuplexAnonPipesHandles,
                                            clientIPCListener,
                                            closeFullDuplexAnonPipesHandles,
                                            createFullDuplexAnonPipesHandles,
                                            getHandleFromEnv, handleIPCProtocol,
                                            isHandleClosed, isIPCError,
                                            isNodeChannelCannotBeFound,
                                            isUnreadableHandle,
                                            isUnwritableHandle, serverReadWrite,
                                            startIPC, startNodeJsIPC)
import           Cardano.Shell.NodeIPC.Message (MessageException (..),
                                                ReadHandle (..),
                                                WriteHandle (..), readMessage,
                                                sendMessage)
import           Cardano.Shell.NodeIPC.ServerExample (exampleServerWithProcess,
                                                      exampleWithFD,
                                                      getReadWriteHandles)
