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
    , getIPCHandle
    , startNodeJsIPC
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
    ) where

import           Cardano.Shell.NodeIPC.Example (exampleWithFD,
                                                exampleWithProcess,
                                                getReadWriteHandles)
import           Cardano.Shell.NodeIPC.Lib (MessageSendFailure (..), MsgIn (..),
                                            MsgOut (..), NodeIPCException (..),
                                            Port (..), getIPCHandle,
                                            startNodeJsIPC)
import           Cardano.Shell.NodeIPC.Message (MessageException(..),
                                                ReadHandle (..),
                                                WriteHandle (..), readMessage,
                                                sendMessage)
