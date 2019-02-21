module Cardano.Shell.Update.Types where

import Cardano.Prelude

-- Types we need to check the behaviour.
data Epoch = Epoch Int
    deriving (Eq, Show)

data Blockchain = Blockchain (Map Epoch [Slot])
    deriving (Eq, Show)

data Slot = Slot Epoch (Maybe Block)
    deriving (Eq, Show)

data Block = Block BlockHash (Maybe InstallerVersion)
    deriving (Eq, Show)

data BlockHash = BlockHash !Text
    deriving (Eq, Show)

data InstallerVersion = InstallerVersion InstallerHash
    deriving (Eq, Show)

data InstallerHash = InstallerHash !Text
    deriving (Eq, Show)


