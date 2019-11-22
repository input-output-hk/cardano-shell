---------------------- MODULE UpdateSystemWallet ------------------------

EXTENDS TLC, Integers, Sequences

CONSTANTS launcher_state_depth  \* How many state depth we want to check?

(*--algorithm launcher
    variables
        current_launcher_state_depth = launcher_state_depth,
        current_wallet_exit_code = 0,
        update_exists \in {TRUE, FALSE},
                
        next_state = "update_mode",
        
        wallet_exit_codes = <<>>,
        updater_exit_codes = <<>>,
        
        \* Tracking global state changes
        update_running = FALSE,
        wallet_running = FALSE
     
define 
    IsElementInSeq(el,seq)==\E i \in DOMAIN seq:seq[i]=el
end define;


\* Simply defining the update to be non-deterministic.
macro update_arrived() begin

    either
        update_exists := TRUE;
    or
        update_exists := FALSE;
    end either;

end macro;
     
macro check_end_state(wallet_exit_codes) begin

    (* We always must pass through at least two labels before we end the proceess. *)
    assert Len(wallet_exit_codes) >= 2;
    
    (* We must pass through the "wallet_normal_mode" when running the spec. *)
    assert IsElementInSeq("update_mode", wallet_exit_codes);
    assert IsElementInSeq("wallet_normal_mode", wallet_exit_codes);

    goto Done;

end macro;
     
(* The Wallet process *)     
fair process Wallet = "Wallet"
begin
    WalletRun:
        await wallet_running /\ next_state \in {"normal_mode", "safe_mode"};
        
        current_launcher_state_depth := current_launcher_state_depth - 1;

        \* This is before the actual "wallet run", so we can see with which "mode"
        \* was run with.
        if next_state = "normal_mode" then 
            wallet_exit_codes := Append(wallet_exit_codes, "wallet_normal_mode");
        elsif next_state = "safe_mode" then
            wallet_exit_codes := Append(wallet_exit_codes, "wallet_safe_mode");
        end if;
        
        
        if current_launcher_state_depth <= 0 then
            goto Done;
        else
            either
                current_wallet_exit_code := 0;  \* Success
                next_state := "success";
                
                \* Check the end state
                check_end_state(wallet_exit_codes);
                
            or
                current_wallet_exit_code := 1;  \* Failure
                next_state := "failure";
                
                \* Check the end state
                check_end_state(wallet_exit_codes);
                
            or
                current_wallet_exit_code := 20; \* Update
                next_state := "update_mode";
                
                goto WalletRun;
            or
                current_wallet_exit_code := 21; \* Safe mode
                next_state := "safe_mode";
                \* Each time we go into safe mode, we can simulate an update.
                update_arrived();
                
                goto WalletRun;
            or
                current_wallet_exit_code := 22; \* Normal mode
                next_state := "normal_mode";
                
                \* Each time we go into safe mode, we can simulate an update.
                update_arrived();
                
                goto WalletRun;
            end either;
        end if; 

end process;


(* The Launcher process *)        
fair process Launcher = "Launcher"
       
begin
    Update:
        await next_state = "update_mode";
        
        update_running := TRUE;
        wallet_running := FALSE;
    
        wallet_exit_codes := Append(wallet_exit_codes, "update_mode");

        if update_exists then
            updater_exit_codes := Append(updater_exit_codes, "updater_success");
            update_exists := FALSE;
        else
            updater_exit_codes := Append(updater_exit_codes, "updater_failure");
        end if;
        
        next_state := "normal_mode";
        \* We have to run the wallet after the update
            
        
        
    Launching:
    
        update_running := FALSE;
        wallet_running := TRUE;
    
        \* The wallet is dictating the states the launcher has to handle.
        if next_state = "success" \/ next_state = "failure" \/ current_launcher_state_depth <= 0 then
            goto Done;
        elsif next_state = "update_mode" then
            goto Update;
        else
            goto Launching; 
        end if; 

end process;

       
end algorithm;*)
\* BEGIN TRANSLATION
VARIABLES current_launcher_state_depth, current_wallet_exit_code, 
          update_exists, next_state, wallet_exit_codes, updater_exit_codes, 
          update_running, wallet_running, pc

(* define statement *)
IsElementInSeq(el,seq)==\E i \in DOMAIN seq:seq[i]=el


vars == << current_launcher_state_depth, current_wallet_exit_code, 
           update_exists, next_state, wallet_exit_codes, updater_exit_codes, 
           update_running, wallet_running, pc >>

ProcSet == {"Wallet"} \cup {"Launcher"}

Init == (* Global variables *)
        /\ current_launcher_state_depth = launcher_state_depth
        /\ current_wallet_exit_code = 0
        /\ update_exists \in {TRUE, FALSE}
        /\ next_state = "update_mode"
        /\ wallet_exit_codes = <<>>
        /\ updater_exit_codes = <<>>
        /\ update_running = FALSE
        /\ wallet_running = FALSE
        /\ pc = [self \in ProcSet |-> CASE self = "Wallet" -> "WalletRun"
                                        [] self = "Launcher" -> "Update"]

WalletRun == /\ pc["Wallet"] = "WalletRun"
             /\ wallet_running /\ next_state \in {"normal_mode", "safe_mode"}
             /\ current_launcher_state_depth' = current_launcher_state_depth - 1
             /\ IF next_state = "normal_mode"
                   THEN /\ wallet_exit_codes' = Append(wallet_exit_codes, "wallet_normal_mode")
                   ELSE /\ IF next_state = "safe_mode"
                              THEN /\ wallet_exit_codes' = Append(wallet_exit_codes, "wallet_safe_mode")
                              ELSE /\ TRUE
                                   /\ UNCHANGED wallet_exit_codes
             /\ IF current_launcher_state_depth' <= 0
                   THEN /\ pc' = [pc EXCEPT !["Wallet"] = "Done"]
                        /\ UNCHANGED << current_wallet_exit_code, 
                                        update_exists, next_state >>
                   ELSE /\ \/ /\ current_wallet_exit_code' = 0
                              /\ next_state' = "success"
                              /\ Assert(Len(wallet_exit_codes') >= 2, 
                                        "Failure of assertion at line 41, column 5 of macro called at line 76, column 17.")
                              /\ Assert(IsElementInSeq("update_mode", wallet_exit_codes'), 
                                        "Failure of assertion at line 44, column 5 of macro called at line 76, column 17.")
                              /\ Assert(IsElementInSeq("wallet_normal_mode", wallet_exit_codes'), 
                                        "Failure of assertion at line 45, column 5 of macro called at line 76, column 17.")
                              /\ pc' = [pc EXCEPT !["Wallet"] = "Done"]
                              /\ UNCHANGED update_exists
                           \/ /\ current_wallet_exit_code' = 1
                              /\ next_state' = "failure"
                              /\ Assert(Len(wallet_exit_codes') >= 2, 
                                        "Failure of assertion at line 41, column 5 of macro called at line 83, column 17.")
                              /\ Assert(IsElementInSeq("update_mode", wallet_exit_codes'), 
                                        "Failure of assertion at line 44, column 5 of macro called at line 83, column 17.")
                              /\ Assert(IsElementInSeq("wallet_normal_mode", wallet_exit_codes'), 
                                        "Failure of assertion at line 45, column 5 of macro called at line 83, column 17.")
                              /\ pc' = [pc EXCEPT !["Wallet"] = "Done"]
                              /\ UNCHANGED update_exists
                           \/ /\ current_wallet_exit_code' = 20
                              /\ next_state' = "update_mode"
                              /\ pc' = [pc EXCEPT !["Wallet"] = "WalletRun"]
                              /\ UNCHANGED update_exists
                           \/ /\ current_wallet_exit_code' = 21
                              /\ next_state' = "safe_mode"
                              /\ \/ /\ update_exists' = TRUE
                                 \/ /\ update_exists' = FALSE
                              /\ pc' = [pc EXCEPT !["Wallet"] = "WalletRun"]
                           \/ /\ current_wallet_exit_code' = 22
                              /\ next_state' = "normal_mode"
                              /\ \/ /\ update_exists' = TRUE
                                 \/ /\ update_exists' = FALSE
                              /\ pc' = [pc EXCEPT !["Wallet"] = "WalletRun"]
             /\ UNCHANGED << updater_exit_codes, update_running, 
                             wallet_running >>

Wallet == WalletRun

Update == /\ pc["Launcher"] = "Update"
          /\ next_state = "update_mode"
          /\ update_running' = TRUE
          /\ wallet_running' = FALSE
          /\ wallet_exit_codes' = Append(wallet_exit_codes, "update_mode")
          /\ IF update_exists
                THEN /\ updater_exit_codes' = Append(updater_exit_codes, "updater_success")
                     /\ update_exists' = FALSE
                ELSE /\ updater_exit_codes' = Append(updater_exit_codes, "updater_failure")
                     /\ UNCHANGED update_exists
          /\ next_state' = "normal_mode"
          /\ pc' = [pc EXCEPT !["Launcher"] = "Launching"]
          /\ UNCHANGED << current_launcher_state_depth, 
                          current_wallet_exit_code >>

Launching == /\ pc["Launcher"] = "Launching"
             /\ update_running' = FALSE
             /\ wallet_running' = TRUE
             /\ IF next_state = "success" \/ next_state = "failure" \/ current_launcher_state_depth <= 0
                   THEN /\ pc' = [pc EXCEPT !["Launcher"] = "Done"]
                   ELSE /\ IF next_state = "update_mode"
                              THEN /\ pc' = [pc EXCEPT !["Launcher"] = "Update"]
                              ELSE /\ pc' = [pc EXCEPT !["Launcher"] = "Launching"]
             /\ UNCHANGED << current_launcher_state_depth, 
                             current_wallet_exit_code, update_exists, 
                             next_state, wallet_exit_codes, updater_exit_codes >>

Launcher == Update \/ Launching

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == Wallet \/ Launcher
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Wallet)
        /\ WF_vars(Launcher)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

===========================================================================
