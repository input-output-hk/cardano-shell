------------------------------ MODULE InnerFIFO-----------------------------

\* Taken from "Specifying systems"

EXTENDS Naturals, Sequences

CONSTANT Message

VARIABLE in, out, q

InChan  == INSTANCE Channel WITH Data <- Message, chan <- in
OutChan == INSTANCE Channel WITH Data <- Message, chan <- out

TypeInvariant ==    /\ InChan!TypeInvariant
                    /\ OutChan!TypeInvariant
                    /\ q \in Seq(Message)

----------------------------------------------------------------------------

\* Init both channels and make sure the message queue is empty.
Init        ==  /\ InChan!Init
                /\ OutChan!Init
                /\ q = <<>>

\* Send msg to the in channel.        
InSend(msg) ==  /\ InChan!Send(msg)
                /\ UNCHANGED <<out, q>>
            
\* Append the received message to the queue.
BufReceive ==   /\ InChan!Receive
                /\ q' = Append(q, in.val)
                /\ UNCHANGED out
                
\* Send the message to out channel and remove from queue.
BufSend    ==   /\ q /= <<>>
                /\ OutChan!Send(Head(q)) \* Send the first element out to the out channel.
                /\ q' = Tail(q) \* The queue after the send doesn't have that element.
                /\ UNCHANGED in
                
\* Receive message from the out channel.
OutReceive ==   /\ OutChan!Receive
                /\ UNCHANGED <<in, q>>
                
Next       ==   \/ \E msg \in Message: InSend(msg)
                \/ BufReceive
                \/ BufSend
                \/ OutReceive 
                
\* We don't automatically add the message...
PassNext   ==   \/ BufReceive
                \/ BufSend
                \/ OutReceive 
             
              
Spec    == Init /\ [][Next]_<<in, out, q>>

----------------------------------------------------------------------------

THEOREM Spec => []TypeInvariant

============================================================================