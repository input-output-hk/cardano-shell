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
    , exampleWithProcess
    , getReadWriteHandles
    -- * Predicates
    , isIPCException
    , isHandleClosed
    , isUnreadableHandle
    , isUnwritableHandle
    , isNodeChannelCannotBeFound
    ) where

import           Cardano.Shell.NodeIPC.Example (exampleWithFD,
                                                exampleWithProcess,
                                                getReadWriteHandles)
import           Cardano.Shell.NodeIPC.Lib (MessageSendFailure (..), MsgIn (..),
                                            MsgOut (..), NodeIPCException (..),
                                            Port (..), isHandleClosed,
                                            isIPCException,
                                            isNodeChannelCannotBeFound,
                                            isUnreadableHandle,
                                            isUnwritableHandle, startIPC,
                                            startNodeJsIPC)
import           Cardano.Shell.NodeIPC.Message (MessageException (..),
                                                ReadHandle (..),
                                                WriteHandle (..), readMessage,
                                                sendMessage)
