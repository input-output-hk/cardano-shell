------------------------------ MODULE IPCProtocol -------------------------

(* 

In Linux versions before 2.6.11, the capacity of a pipe was the same as 
the system page size (e.g., 4096 bytes on i386). Since Linux 2.6.11, 
the pipe capacity is 16 pages (i.e., 65,536 bytes in a system with a 
page size of 4096 bytes).

N               = 20
Messsage        = {"ping","pong","queryPort","replyPort"}
MessagePairs    = {[msgIn |-> "ping", msgOut |-> "pong"],[msgIn |-> "queryPort", msgOut |-> "replyPort"]}

*)

EXTENDS Naturals, Sequences

VARIABLES inQueue, outQueue
            
CONSTANT Message, MessagePairs, N
ASSUME (N \in Nat) /\ (N > 0) \* Both queues have the same number of messages
ASSUME (\A msgPair \in MessagePairs:    /\ msgPair.msgIn \in Message 
                                        /\ msgPair.msgOut \in Message 
                                        /\ msgPair.msgIn /= msgPair.msgOut) 

\* A simple type invariant
TypeOK   == /\ \A msgPair \in MessagePairs: msgPair.msgIn /= msgPair.msgOut

\* Util function
Last(s)  == s[Len(s)]

---------------------------------------------------------------------------

(* 
\* We would usually use the existing structures, but the problem with these is that
\* they have a step that chooses a random message when we advance their state using next.
InQueue  == INSTANCE BoundedFIFO WITH in <- inQueueIn, out <- inQueueOut, q <- inQueue
OutQueue == INSTANCE BoundedFIFO WITH in <- outQueueIn, out <- outQueueOut, q <- outQueue
*)
  
\* Make sure that once the message goes in, eventually it must go out as it's pair response
MsgIncl  ==
  \A msgPair \in MessagePairs :
    (Len(inQueue) > 0) => Last(inQueue) = msgPair.msgIn ~> Head(outQueue) = msgPair.msgOut
    
---------------------------------------------------------------------------

\* When theys start they are empty
Init     == /\ inQueue  = <<>>
            /\ outQueue = <<>>

                \* If the input queue is empty, we presume that the sender awaits for the response.
BNext    == /\  IF Len(inQueue) = 0
                \* Append a new message to the in queue
                THEN \E msgPair \in MessagePairs:   /\ inQueue' = Append(inQueue, msgPair.msgIn) 
                                                    /\ UNCHANGED(outQueue)
                \* Advances a step, removes a message from in queue and appends it's pair to out queue                                                    
                ELSE \E msgPair \in MessagePairs:   /\ inQueue' = Tail(inQueue) 
                                                    /\ outQueue' = Append(outQueue, msgPair.msgOut)
            /\ Len(inQueue)  < N \* Bounded inQueue, this gets discharged, but let's keep our invariants
            /\ Len(outQueue) < N \* Bounded outQueue 
           
Spec     == /\ MsgIncl 
            /\ Init 
            /\ [][BNext]_<<inQueue,outQueue>>

----------------------------------------------------------------------------

THEOREM Spec => []TypeOK

============================================================================