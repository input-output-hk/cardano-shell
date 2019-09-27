{-# LANGUAGE OverloadedStrings #-}

module Main where

import Cardano.Prelude

seconds :: Int
seconds = 1000000

main :: IO ExitCode
main = do
    putTextLn $ "Starting Daedalus"
    threadDelay $ 5 * seconds
    putText $ "Exiting for update"
    return $ ExitFailure 20