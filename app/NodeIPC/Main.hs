module Main
    ( main
    ) where

import           Cardano.Prelude
import           Cardano.Shell.NodeIPC (Port (..), ProtocolDuration (..),
                                        startNodeJsIPC)

main :: IO ()
main = do
    let port = Port 8090
    startNodeJsIPC SingleMessage port
