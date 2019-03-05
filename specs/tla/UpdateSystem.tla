---------------------------- MODULE UpdateSystem ----------------------------
EXTENDS Integers,TLC 

VARIABLES node_state 
        , blockchain_state
        , syncedBlocksTick
        , installerVersionBlock
        , latestInstallerVersion    

--------------------------------------------------------

(* 

This algorithm CAN deadlock, since we don't update the blockchain when running it.
Why do we use values that are so small? To avoid combinatorial explosion of the state space. 

*)

(* We start with the fresh node, no block synced *)
Init == /\ node_state               = 0
        /\ blockchain_state         \in (1..216)  
        \* The number of updates on the blockchain
        \* /\ numOfUpdates             \in (0..blockchain_state)
        /\ installerVersionBlock    \in (1..216)
        /\ syncedBlocksTick         \in (1..20)
        /\ latestInstallerVersion   = 0

(* The formulas that need to be true for all states *)
Invariants ==   /\ node_state <= blockchain_state
                /\  \/ latestInstallerVersion = 0 \* We can make this a bit more precise 
                    \/ latestInstallerVersion = installerVersionBlock 

(* We sync 1-50 blocks in one tick *)
SyncBlocks ==   node_state' = IF (node_state + syncedBlocksTick) > blockchain_state
                        THEN blockchain_state
                        ELSE node_state + syncedBlocksTick    
        
(* The situation when we change the installer version *)
CheckUpdates == IF (node_state < installerVersionBlock /\ node_state' > installerVersionBlock)
                THEN latestInstallerVersion' = installerVersionBlock
                ELSE UNCHANGED latestInstallerVersion
        
(* Ideally, the blockchain would advance one block per tick, but the state explosion is VERY large. *)
RunNode ==  /\ SyncBlocks
            /\ CheckUpdates
            /\ UNCHANGED blockchain_state
            /\ UNCHANGED installerVersionBlock
            \* We want to change this every tick, since it's not a constant
            /\ syncedBlocksTick' = RandomElement(1..20)
                 
            
(* We stop if the blockchain is synced up *)            
Next == RunNode
        
=============================================================================
\* Modification History
\* Last modified Tue Mar 05 09:11:23 CET 2019 by ksaric
\* Created Tue Feb 26 15:16:50 CET 2019 by ksaric
