{-# LANGUAGE LambdaCase #-}

module Main where

import           Cardano.Prelude

import           Cardano.BM.Configuration.Static (defaultConfigStdout)
import           Cardano.BM.Setup (setupTrace_)
import           Cardano.Shell.DaedalusIPC

main :: IO ()
main = fmap readEither <$> getArgs >>= \case
  [Right port] -> do
    c <- defaultConfigStdout
    (tr, _sb) <- setupTrace_ c "daedalus-ipc"
    daedalusIPC tr port
  _ -> do
    putStrLn ("Usage: daedalus-ipc PORT" :: Text)
    exitFailure
