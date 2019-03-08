------------------------------ MODULE Channel ------------------------------

\* Taken from "Specifying systems"

EXTENDS Naturals

CONSTANT Data

VARIABLE chan

TypeInvariant == chan \in [val: Data, ready: {0, 1}, ack: {0,1}]

----------------------------------------------------------------------------

\* In the begining, the ack and ready flags are the same.
Init == /\ TypeInvariant
        /\ chan.ack = chan.ready

\* When the flags are the same, you can send the message.
Send(d) ==  /\ chan.ready   = chan.ack
            /\ chan'        = [chan EXCEPT !.val = d, !.ready = 1 - chan.ready]
            
\* When the flags are not the same, you can confirm the message.
Receive ==  /\ chan.ready   /= chan.ack
            /\ chan'        = [chan EXCEPT !.ready = 1 - chan.ready]
            
Next    == (\E d \in Data: Send(d)) /\ Receive

Spec    == Init /\ [][Next]_chan  

----------------------------------------------------------------------------

THEOREM Spec => []TypeInvariant

============================================================================