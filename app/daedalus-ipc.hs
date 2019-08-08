{-# LANGUAGE LambdaCase #-}

module Main where

import           Cardano.Prelude

import           Cardano.Shell.DaedalusIPC

-- TODO(KS): If you want to provide the trace functions you need to pass them.
main :: IO ()
main = fmap readEither <$> getArgs >>= \case
  [Right port] -> do
    daedalusIPC port
  _ -> do
    putStrLn ("Usage: daedalus-ipc PORT" :: Text)
    exitFailure
