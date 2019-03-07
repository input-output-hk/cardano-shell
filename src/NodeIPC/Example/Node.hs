#!/usr/bin/env stack
{- stack --resolver lts-12.10 script
    --package=cardano-prelude
    --package=cardano-shell
-}

module Node where

import           Cardano.Prelude
import           NodeIPC.Lib (Port (..), getIPCHandle, startNodeJsIPC)
import           NodeIPC.Message (ReadHandle (..), WriteHandle (..))

main :: IO ()
main = do
    hndl <- getIPCHandle
    let readHndl = ReadHandle hndl
    let writeHndl = WriteHandle hndl
    let port = Port 8090
    startNodeJsIPC readHndl writeHndl port
    