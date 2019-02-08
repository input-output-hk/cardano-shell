---- MODULE IPCProtocol ----

VARIABLES pc   

\* All the states that exist. 
\* Don't forget to uncheck "Deadlock" since this is a long-running program!
TypeOK      ==     pc \in {"Started", "Ping", "Pong", "QueryPort", "ReplyPort"}

\* Initial state.
Init        ==     pc = "Started"

\* These definitions are about the simple ping-pong protocol.
InitToPing  ==  /\ pc  = "Started"
                /\ pc' = "Ping"
                
PingPong    ==  /\ pc  = "Ping"
                /\ pc' = "Pong"
                
PongInit    ==  /\ pc  = "Pong"
                /\ pc' = "Started"

\* These definitions are about the port communication.
InitToQuery ==  /\ pc  = "Started"
                /\ pc' = "QueryPort"
            
QueryPort   ==  /\ pc  = "QueryPort"
                /\ pc' = "ReplyPort"
                
ReplyInit   ==  /\ pc  = "ReplyPort"
                /\ pc' = "Started"
            
\* Transitions.
Next        ==  TypeOK /\
                \/ InitToPing 
                \/ InitToQuery 
                \/ PingPong 
                \/ QueryPort
                \/ ReplyInit

==============================
