---------------------- MODULE LauncherUpdateSystem ------------------------

EXTENDS TLC, Integers, Sequences

CONSTANTS launcher_state_depth  \* How many state depth we want to check?

(*--algorithm launcher
    variables
        current_launcher_state_depth = launcher_state_depth,
        current_wallet_exit_code = 0,
        update_exists \in {TRUE, FALSE}
     
define 
    IsElementInSeq(el,seq)==\E i \in DOMAIN seq:seq[i]=el
end define;
     
fair process Launcher = "Launcher"
    variables
        wallet_exit_codes = <<>>,
        updater_exit_codes = <<>>
        
begin
    Update:
        current_launcher_state_depth := current_launcher_state_depth - 1;
        
        if current_launcher_state_depth <= 0 then
            goto Done;
        else
            wallet_exit_codes := Append(wallet_exit_codes, "update_mode");
    
            if update_exists then
                updater_exit_codes := Append(updater_exit_codes, "updater_success");
                update_exists := FALSE;
            else
                updater_exit_codes := Append(updater_exit_codes, "updater_failure");
            end if;
            
            goto NormalMode;
        end if;
        

        
    NormalMode:
        current_launcher_state_depth := current_launcher_state_depth - 1;
        
        if current_launcher_state_depth <= 0 then
            goto Done;
        else
            wallet_exit_codes := Append(wallet_exit_codes, "wallet_normal_mode");
    
            either
                current_wallet_exit_code := 0;  \* Success
                goto Success;
            or
                current_wallet_exit_code := 20; \* Update
                goto Update;
            or
                current_wallet_exit_code := 21; \* Safe mode
                goto SafeMode;
            or
                current_wallet_exit_code := 22; \* Normal mode
                goto NormalMode;
            or
                current_wallet_exit_code := 1;  \* Failure
                goto Failure;
            end either;
        end if;
    

        
    SafeMode:
        current_launcher_state_depth := current_launcher_state_depth - 1;
        
        if current_launcher_state_depth <= 0 then
            goto Done;
        else
            wallet_exit_codes := Append(wallet_exit_codes, "wallet_safe_mode");
    
            either
                current_wallet_exit_code := 0;  \* Success
                goto Success;
            or
                current_wallet_exit_code := 20; \* Update
                goto Update;
            or
                current_wallet_exit_code := 21; \* Safe mode
                goto SafeMode;
            or
                current_wallet_exit_code := 22; \* Normal mode
                goto NormalMode;
            or
                current_wallet_exit_code := 1;  \* Failure
                goto Failure;
            end either;   
        end if;
        
       
    Success:
        (* We always must pass through at least two labels before we end the proceess. *)
        assert Len(wallet_exit_codes) >= 2;
        
        (* We must pass through the "wallet_normal_mode" when running the spec. *)
        assert IsElementInSeq("update_mode", wallet_exit_codes);
        assert IsElementInSeq("wallet_normal_mode", wallet_exit_codes);
        
        wallet_exit_codes := Append(wallet_exit_codes, "success");
        goto Done;
        
    Failure:
        (* We always must pass through at least two labels before we end the proceess. *)
        assert Len(wallet_exit_codes) >= 2;
        
        (* We must pass through the "wallet_normal_mode" when running the spec. *)
        assert IsElementInSeq("update_mode", wallet_exit_codes);
        assert IsElementInSeq("wallet_normal_mode", wallet_exit_codes);
        
        wallet_exit_codes := Append(wallet_exit_codes, "failure");
        goto Done;

end process;

       
end algorithm;*)
\* BEGIN TRANSLATION
VARIABLES current_launcher_state_depth, current_wallet_exit_code, 
          update_exists, pc

(* define statement *)
IsElementInSeq(el,seq)==\E i \in DOMAIN seq:seq[i]=el

VARIABLES wallet_exit_codes, updater_exit_codes

vars == << current_launcher_state_depth, current_wallet_exit_code, 
           update_exists, pc, wallet_exit_codes, updater_exit_codes >>

ProcSet == {"Launcher"}

Init == (* Global variables *)
        /\ current_launcher_state_depth = launcher_state_depth
        /\ current_wallet_exit_code = 0
        /\ update_exists \in {TRUE, FALSE}
        (* Process Launcher *)
        /\ wallet_exit_codes = <<>>
        /\ updater_exit_codes = <<>>
        /\ pc = [self \in ProcSet |-> "Update"]

Update == /\ pc["Launcher"] = "Update"
          /\ current_launcher_state_depth' = current_launcher_state_depth - 1
          /\ IF current_launcher_state_depth' <= 0
                THEN /\ pc' = [pc EXCEPT !["Launcher"] = "Done"]
                     /\ UNCHANGED << update_exists, wallet_exit_codes, 
                                     updater_exit_codes >>
                ELSE /\ wallet_exit_codes' = Append(wallet_exit_codes, "update_mode")
                     /\ IF update_exists
                           THEN /\ updater_exit_codes' = Append(updater_exit_codes, "updater_success")
                                /\ update_exists' = FALSE
                           ELSE /\ updater_exit_codes' = Append(updater_exit_codes, "updater_failure")
                                /\ UNCHANGED update_exists
                     /\ pc' = [pc EXCEPT !["Launcher"] = "NormalMode"]
          /\ UNCHANGED current_wallet_exit_code

NormalMode == /\ pc["Launcher"] = "NormalMode"
              /\ current_launcher_state_depth' = current_launcher_state_depth - 1
              /\ IF current_launcher_state_depth' <= 0
                    THEN /\ pc' = [pc EXCEPT !["Launcher"] = "Done"]
                         /\ UNCHANGED << current_wallet_exit_code, 
                                         wallet_exit_codes >>
                    ELSE /\ wallet_exit_codes' = Append(wallet_exit_codes, "wallet_normal_mode")
                         /\ \/ /\ current_wallet_exit_code' = 0
                               /\ pc' = [pc EXCEPT !["Launcher"] = "Success"]
                            \/ /\ current_wallet_exit_code' = 20
                               /\ pc' = [pc EXCEPT !["Launcher"] = "Update"]
                            \/ /\ current_wallet_exit_code' = 21
                               /\ pc' = [pc EXCEPT !["Launcher"] = "SafeMode"]
                            \/ /\ current_wallet_exit_code' = 22
                               /\ pc' = [pc EXCEPT !["Launcher"] = "NormalMode"]
                            \/ /\ current_wallet_exit_code' = 1
                               /\ pc' = [pc EXCEPT !["Launcher"] = "Failure"]
              /\ UNCHANGED << update_exists, updater_exit_codes >>

SafeMode == /\ pc["Launcher"] = "SafeMode"
            /\ current_launcher_state_depth' = current_launcher_state_depth - 1
            /\ IF current_launcher_state_depth' <= 0
                  THEN /\ pc' = [pc EXCEPT !["Launcher"] = "Done"]
                       /\ UNCHANGED << current_wallet_exit_code, 
                                       wallet_exit_codes >>
                  ELSE /\ wallet_exit_codes' = Append(wallet_exit_codes, "wallet_safe_mode")
                       /\ \/ /\ current_wallet_exit_code' = 0
                             /\ pc' = [pc EXCEPT !["Launcher"] = "Success"]
                          \/ /\ current_wallet_exit_code' = 20
                             /\ pc' = [pc EXCEPT !["Launcher"] = "Update"]
                          \/ /\ current_wallet_exit_code' = 21
                             /\ pc' = [pc EXCEPT !["Launcher"] = "SafeMode"]
                          \/ /\ current_wallet_exit_code' = 22
                             /\ pc' = [pc EXCEPT !["Launcher"] = "NormalMode"]
                          \/ /\ current_wallet_exit_code' = 1
                             /\ pc' = [pc EXCEPT !["Launcher"] = "Failure"]
            /\ UNCHANGED << update_exists, updater_exit_codes >>

Success == /\ pc["Launcher"] = "Success"
           /\ Assert(Len(wallet_exit_codes) >= 2, 
                     "Failure of assertion at line 100, column 9.")
           /\ Assert(IsElementInSeq("update_mode", wallet_exit_codes), 
                     "Failure of assertion at line 103, column 9.")
           /\ Assert(IsElementInSeq("wallet_normal_mode", wallet_exit_codes), 
                     "Failure of assertion at line 104, column 9.")
           /\ wallet_exit_codes' = Append(wallet_exit_codes, "success")
           /\ pc' = [pc EXCEPT !["Launcher"] = "Done"]
           /\ UNCHANGED << current_launcher_state_depth, 
                           current_wallet_exit_code, update_exists, 
                           updater_exit_codes >>

Failure == /\ pc["Launcher"] = "Failure"
           /\ Assert(Len(wallet_exit_codes) >= 2, 
                     "Failure of assertion at line 111, column 9.")
           /\ Assert(IsElementInSeq("update_mode", wallet_exit_codes), 
                     "Failure of assertion at line 114, column 9.")
           /\ Assert(IsElementInSeq("wallet_normal_mode", wallet_exit_codes), 
                     "Failure of assertion at line 115, column 9.")
           /\ wallet_exit_codes' = Append(wallet_exit_codes, "failure")
           /\ pc' = [pc EXCEPT !["Launcher"] = "Done"]
           /\ UNCHANGED << current_launcher_state_depth, 
                           current_wallet_exit_code, update_exists, 
                           updater_exit_codes >>

Launcher == Update \/ NormalMode \/ SafeMode \/ Success \/ Failure

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == Launcher
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Launcher)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

===========================================================================
