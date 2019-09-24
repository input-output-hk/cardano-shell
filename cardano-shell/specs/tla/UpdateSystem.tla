---------------------------- MODULE UpdateSystem ----------------------------
EXTENDS Integers,TLC 

VARIABLES node_state 
        , blockchain_state
        , synced_blocks_tick
        , installer_version_block
        , latest_installer_version    

--------------------------------------------------------

(* 

This algorithm CAN deadlock, since we don't update the blockchain when running it.
Why do we use values that are so small? To avoid combinatorial explosion of the state space. 

*)

(* We start with the fresh node, no block synced *)
Init == /\ node_state                   = 0
        /\ blockchain_state             \in (1..216)  
        \* The number of updates on the blockchain
        \* /\ numOfUpdates             \in (0..blockchain_state)
        /\ installer_version_block      \in (1..216)
        /\ synced_blocks_tick           \in (1..20)
        /\ latest_installer_version     = 0

(* The formulas that need to be true for all states *)
Invariants ==   /\ node_state <= blockchain_state
                /\  \/ latest_installer_version = 0 \* We can make this a bit more precise 
                    \/ latest_installer_version = latest_installer_version 

(* We sync 1-50 blocks in one tick *)
SyncBlocks ==   node_state' = IF (node_state + synced_blocks_tick) > blockchain_state
                        THEN blockchain_state
                        ELSE node_state + synced_blocks_tick    
        
(* The situation when we change the installer version *)
CheckUpdates == IF (node_state < installer_version_block /\ node_state' > installer_version_block)
                THEN latest_installer_version' = installer_version_block
                ELSE UNCHANGED latest_installer_version
        
(* Ideally, the blockchain would advance one block per tick, but the state explosion is VERY large. *)
RunNode ==  /\ SyncBlocks
            /\ CheckUpdates
            /\ UNCHANGED blockchain_state
            /\ UNCHANGED installer_version_block
            \* We want to change this every tick, since it's not a constant
            /\ synced_blocks_tick' = RandomElement(1..20)
                 
            
(* We stop if the blockchain is synced up *)            
Next == RunNode
        
=============================================================================
\* Modification History
\* Last modified Tue Mar 05 13:04:46 CET 2019 by ksaric
\* Created Tue Feb 26 15:16:50 CET 2019 by ksaric
