------------------------------ MODULE Launcher -------------------------

EXTENDS Naturals, Sequences

VARIABLES current_state

---------------------------------------------------------------------------

(* 
The type correctness for the state machine.
*)
TypeOK   == current_state \in {"update_mode", "wallet_normal_mode", "wallet_safe_mode", "success", "failure"}

(* 
The initial state.
*)
Init     == current_state = "update_mode"    

(*
The list of transitions that are moving from one state to the next.
*)
Next     == \/  /\  current_state   = "update_mode"
                /\  current_state'  = "wallet_normal_mode"
                
            \/  /\  current_state   = "wallet_normal_mode"
                /\  current_state'  \in {"update_mode", "wallet_normal_mode", "wallet_safe_mode", "success", "failure"}
                
            \/  /\  current_state   = "wallet_safe_mode"
                /\  current_state'  \in {"wallet_normal_mode", "success", "failure"}
                
            \/  /\  current_state   = "success"
                /\  current_state'  = "success"
            
            \/  /\  current_state   = "failure"
                /\  current_state'  = "failure"

(* 
If the current state is the wallet normal mode, we will eventually end up in one of these states - "success", "failure", "update_mode", "wallet_safe_mode".
And the current state will, AT SOME POINT, go through the wallet normal mode.
*)
Properties ==   /\  current_state = "wallet_normal_mode" ~> current_state \in {"success", "failure", "update_mode", "wallet_safe_mode"}
                /\  <>(current_state = "wallet_normal_mode")
                
(* 
There is an interesting function here. The WF_ is here to designate that this is a fair process. 
Since we don't want to have stuttering in this model, we are using this command for (Weak Fair) process.
More about stuttering here - https://lamport.azurewebsites.net/tla/stuttering.html?back-link=advanced.html
*)
Spec     == Init /\ [][Next]_<<current_state>> /\ WF_<<current_state>>(Next)

THEOREM Spec => []TypeOK

===========================================================================
