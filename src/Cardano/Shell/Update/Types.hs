module Cardano.Shell.Update.Types where

import           Cardano.Prelude

import qualified Data.Map as M
import           Test.QuickCheck (Gen, choose, frequency, listOf1)


-- Types we need to check the behaviour.
data Blockchain = Blockchain { getBlockchainContents :: !(Map Epoch [Slot]) }
    deriving (Eq, Show)

data Epoch = Epoch Int
    deriving (Eq, Ord, Show)

data Slot = Slot (Maybe Block)
    deriving (Eq, Show)

data Block = Block BlockHash (Maybe InstallerVersion)
    deriving (Eq, Show)

data BlockHash = BlockHash !Text
    deriving (Eq, Show)

data InstallerVersion = InstallerVersion InstallerHash
    deriving (Eq, Ord, Show)

data InstallerHash = InstallerHash !Text
    deriving (Eq, Ord, Show)

-- | The wrapper is used since this is an important distinction.
newtype LatestInstallerVersion = LatestInstallerVersion
    { getInstallerVersion :: InstallerVersion
    } deriving (Eq, Show)

-- | Function for fetching @InstallerVersion@ from a @Block@ from a @Slot@.
slotContainsInstaller :: Slot -> Maybe InstallerVersion
slotContainsInstaller (Slot Nothing)    = Nothing
slotContainsInstaller (Slot block)      = blockContainsInstaller =<< block
  where
    blockContainsInstaller :: Block -> Maybe InstallerVersion
    blockContainsInstaller (Block _ Nothing)          = Nothing
    blockContainsInstaller (Block _ installerVersion) = installerVersion


--------------------------------------------------------------------------------
-- Generation functions
--------------------------------------------------------------------------------

genInstallerVersion :: Gen InstallerVersion
genInstallerVersion = InstallerVersion <$> genInstallerHash

genInstallerHash :: Gen InstallerHash
genInstallerHash = InstallerHash <$> genSafeText

-- | Generate random ascii string, it's very simplifed.
genSafeText :: Gen Text
genSafeText = strConv Lenient <$> (listOf1 $ choose ('a', 'z'))

genBlock :: Gen Block
genBlock = Block <$> genBlockHash <*> genMaybeInstallerVersion

genSlot :: Gen Slot
genSlot = Slot <$> frequency
    [ (10, Just <$> genBlock)
    , (1 , pure Nothing)
    ]

genSlots :: Gen [Slot]
genSlots = replicateM 10 genSlot

genBlockHash :: Gen BlockHash
genBlockHash = BlockHash <$> genSafeText

genMaybeInstallerVersion :: Gen (Maybe InstallerVersion)
genMaybeInstallerVersion = frequency
    [ (1 , Just <$> genInstallerVersion)
    , (10, pure Nothing)
    ]

-- | Here we generate the blockchain that contains the installer
genBlockchainWithInstaller :: Gen Blockchain
genBlockchainWithInstaller = do
    numOfEpochs <- choose (1, 100)

    let availableEpochs = map Epoch [1..numOfEpochs]
    slots <- replicateM numOfEpochs genSlots

    let epochSlots = zip availableEpochs slots
    let blockchain = Blockchain $ M.fromList epochSlots

    pure blockchain


--------------------------------------------------------------------------------
-- Functions we can use to check the correct behaviour
--------------------------------------------------------------------------------

-- blockchain <- generate genBlockchainWithInstaller
-- latestUpdateFromBlockchain blockchain

-- | Here we fetch all the updates from the blockchain.
-- Simply iterate the blockchain and if there exists an @InstallerVersion@
-- append it to the existing list.
fetchUpdatesFromBlockchain :: Blockchain -> [InstallerVersion]
fetchUpdatesFromBlockchain (Blockchain blockchain) =
    let foldrInstallerVersions installerVersions (_epoch, slots) = installerVersions <> filter isJust (map slotContainsInstaller slots)
    in  catMaybes (foldl foldrInstallerVersions mempty (M.toList blockchain))

-- | Fetch latest installer version, or latest update from the blockchain.
latestUpdateFromBlockchain :: Blockchain -> Maybe LatestInstallerVersion
latestUpdateFromBlockchain = fmap LatestInstallerVersion . head . reverse . fetchUpdatesFromBlockchain

