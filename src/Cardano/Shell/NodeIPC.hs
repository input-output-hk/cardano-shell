{-| Node IPC module. For details please read the spec:

<https://github.com/input-output-hk/cardano-shell/blob/develop/specs/CardanoShellSpec.pdf>
-}

{-# LANGUAGE CPP #-}

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
     -- ** Exceptions
    , NodeIPCException(..)
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
    , isIPCException
    , isHandleClosed
    , isUnreadableHandle
    , isUnwritableHandle
    , isNodeChannelCannotBeFound
    ) where

import           Cardano.Shell.NodeIPC.ServerExample (exampleWithFD,
                                                exampleServerWithProcess,
                                                getHandleFromEnv,
                                                getReadWriteHandles)
import           Cardano.Shell.NodeIPC.Lib (MessageSendFailure (..), MsgIn (..),
                                            MsgOut (..), NodeIPCException (..),
                                            Port (..), ProtocolDuration (..),
                                            isHandleClosed, isIPCException,
                                            isNodeChannelCannotBeFound,
                                            isUnreadableHandle,
                                            isUnwritableHandle, startIPC,
                                            startNodeJsIPC)
import           Cardano.Shell.NodeIPC.Message (MessageException (..),
                                                ReadHandle (..),
                                                WriteHandle (..), readMessage,
                                                sendMessage)
