{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Copyright: © 2018-2019 IOHK
--
-- Daedalus <-> Wallet child process port discovery protocol.
-- Provides a mechanism for Daedalus to discover what port the cardano-wallet
-- server is listening on.
--
-- See <https://nodejs.org/api/child_process.html#child_process_child_process_spawn_command_args_options>
-- for more information about the message protocol.

module Cardano.Shell.DaedalusIPC
    ( daedalusIPC
    ) where

import           Cardano.Prelude

import           Cardano.BM.Trace (Trace, logError, logInfo, logNotice)
import           Cardano.Shell.NodeIPC.General (NodeChannelError (..),
                                                NodeChannelFinished (..),
                                                runNodeChannel,
                                                setupNodeChannel)
import           Control.Concurrent (threadDelay)
import           Control.Monad (forever)
import           Data.Aeson (FromJSON (..), ToJSON (..), Value (..), object,
                             withObject, (.:), (.=))
import           Data.Text (Text)

-- | Messages sent from Daedalus -> cardano-wallet
data MsgIn = QueryPort
    deriving (Show, Eq)

-- | Messages sent from cardano-wallet -> Daedalus
data MsgOut = Started | ReplyPort Int | ParseError Text
    deriving (Show, Eq)

instance FromJSON MsgIn where
    parseJSON = withObject "MsgIn" $ \v -> do
        (_ :: [()]) <- v .: "QueryPort"
        pure QueryPort

instance ToJSON MsgOut where
    toJSON Started        = object [ "Started" .= Array mempty ]
    toJSON (ReplyPort p)  = object [ "ReplyPort" .= p ]
    toJSON (ParseError e) = object [ "ParseError" .= e ]

-- | Start up the Daedalus IPC process. It's called 'daedalusIPC', but this
-- could be any nodejs program that needs to start cardano-wallet. All it does
-- is reply with a port number when asked, using a very nodejs-specific IPC
-- method.
--
-- If the IPC channel was successfully set up, this function won't return until
-- the parent process exits. Otherwise, it will return immediately. Before
-- returning, it will log an message about why it has exited.
daedalusIPC
    :: Trace IO Text
    -- ^ Logging object
    -> Int
    -- ^ Port number to send to Daedalus
    -> IO ()
daedalusIPC tr port = setupNodeChannel >>= \case
    Right chan -> do
        logInfo tr "Daedalus IPC server starting"
        runNodeChannel (pure . msg) action chan >>= \case
            Left (NodeChannelFinished err) ->
                logNotice tr $ "Daedalus IPC finished for this reason: " <> show err
            Right () -> logError tr "Unreachable code"
    Left NodeChannelDisabled -> do
        logInfo tr "Daedalus IPC is not enabled."
        sleep
    Left (NodeChannelBadFD err) ->
        logError tr $ "Problem starting Daedalus IPC: " <> show err
  where
    -- How to respond to an incoming message, or when there is an incoming
    -- message that couldn't be parsed.
    msg (Right QueryPort) = Just (ReplyPort port)
    msg (Left e)          = Just (ParseError e)

    -- What to do in context of runNodeChannel
    action :: (MsgOut -> IO ()) -> IO ()
    action send = send Started >> sleep

    sleep = forever $ threadDelay maxBound
