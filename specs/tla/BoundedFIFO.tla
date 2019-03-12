------------------------------ MODULE BoundedFIFO -------------------------

\* Taken from "Specifying systems"

(* 

In Linux versions before 2.6.11, the capacity of a pipe was the same as 
the system page size (e.g., 4096 bytes on i386). Since Linux 2.6.11, 
the pipe capacity is 16 pages (i.e., 65,536 bytes in a system with a 
page size of 4096 bytes).

*)

EXTENDS Naturals, Sequences

VARIABLES in, out, q
CONSTANT Message, N
ASSUME (N \in Nat) /\ (N > 0)

---------------------------------------------------------------------------

Inner    == INSTANCE InnerFIFO WITH in <- in, out <- out, q <- q

Init     == Inner!Init

InSend(msg) == Inner!InSend(msg)

BNext    == /\ Inner!Next 
            /\ Inner!BufReceive => (Len(q) < N)
            
BPassNext == Inner!PassNext
            
Spec     == Init /\ [][BNext]_<<in,out,q>>

===========================================================================
