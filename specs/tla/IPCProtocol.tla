------------------------------ MODULE IPCProtocol -------------------------

(* 

In Linux versions before 2.6.11, the capacity of a pipe was the same as 
the system page size (e.g., 4096 bytes on i386). Since Linux 2.6.11, 
the pipe capacity is 16 pages (i.e., 65,536 bytes in a system with a 
page size of 4096 bytes).

*)

EXTENDS Naturals, Sequences

VARIABLES   inQueueIn, inQueueOut, inQueue, 
            outQueueIn, outQueueOut, outQueue
            
CONSTANT Message, MessagePairs, N
ASSUME (N \in Nat) /\ (N > 0) \* Both queues have the same number of messages
ASSUME (MessagePairs \in [msgIn: Message, msgOut: Message]) 

\* A simple type invariant
TypeOK   == /\ MessagePairs \in [msgIn: Message, msgOut: Message]
            /\ \A msgPair   \in MessagePairs: msgPair.msgIn /= msgPair.msgOut
            /\ inQueue      \in Seq(Message)
            /\ outQueue     \in Seq(Message)

\* Util function
Last(s)  == s[Len(s)]

---------------------------------------------------------------------------

InQueue  == INSTANCE BoundedFIFO WITH in <- inQueueIn, out <- inQueueOut, q <- inQueue
OutQueue == INSTANCE BoundedFIFO WITH in <- outQueueIn, out <- outQueueOut, q <- outQueue

\* Make sure that if the in queue is non-empty, given some length in queue of x, 
\* out queue will eventually reach a point where it will be at least that size, if not greater
MsgTrans ==
  \A x \in Nat :
    (Len(inQueue) > 0) => Len(inQueue) = x ~> Len(outQueue) >= x
    
    
\* Make sure that once the message goes in, it must go out as it's pair
MsgIncl  ==
  \A msgPair \in MessagePairs :
    (Len(inQueue) > 0) => Last(inQueue) = msgPair.msgIn ~> Head(outQueue) = msgPair.msgOut
    
---------------------------------------------------------------------------

Init     == /\ InQueue!Init
            /\ OutQueue!Init

BNext    == /\ InQueue!BNext
            /\ OutQueue!BNext
           
Spec     == /\ MsgTrans 
            /\ MsgIncl 
            /\ Init 
            /\ [][BNext]_<<inQueueIn,inQueueOut,inQueue,outQueueIn,outQueueOut,outQueue>>

----------------------------------------------------------------------------

THEOREM Spec => []TypeOK

============================================================================