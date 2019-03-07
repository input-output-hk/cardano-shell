module Main
    ( main 
    ) where

import           Cardano.Prelude hiding (handle)
import           Cardano.Shell.NodeIPC (Port (..), ReadHandle (..),
                                        WriteHandle (..), getIPCHandle,
                                        startNodeJsIPC)

main :: IO ()
main = do
    handle <- getIPCHandle
    let readHandle  = ReadHandle handle
    let writeHandle = WriteHandle handle
    let port        = Port 8090
    startNodeJsIPC readHandle writeHandle port
