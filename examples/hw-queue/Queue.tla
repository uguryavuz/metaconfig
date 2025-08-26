------------------------------- MODULE Queue --------------------------------
(***************************************************************************)
(* This module defines the queue type, in a way that is compatible with    *)
(* meta-configuration tracking.                                            *)
(***************************************************************************)
(* Author: Ugur Y. Yavuz (Boston University)                               *)
(* Last updated: 2025-07-24                                                *)
(***************************************************************************)

EXTENDS Sequences

CONSTANTS 
  ProcSet,  (* Symbolic set of processes *)
  EltDomain (* Domain of queue element values *)

(***************************************************************************)
(* Operations and arguments                                                *)
(***************************************************************************)
OpNames == {"Enq", "Deq"}
                
ArgsOf(op) ==
  CASE op = "Enq" -> [val: EltDomain]
    [] op = "Deq" -> {"BOT"}
    
RetsOf(op) ==
  CASE op = "Enq" -> {"ACK"}
    [] op = "Deq" -> EltDomain

(***************************************************************************)
(* State domain and initial state                                          *)
(***************************************************************************)
StateDomain == Seq(EltDomain)
\* InitState == <<>> (* Empty queue *)
InitState == CHOOSE q \in StateDomain : TRUE  (* Arbitrary initial queue *)

(***************************************************************************)
(* Transition relation                                                     *)
(***************************************************************************)
(* Delta(c, p, d) is true if process p's operation changes configuration c *)
(* to configuration d.                                                     *)
(***************************************************************************)
Delta(c, p, d) == 
  CASE (c.op[p] = "Enq")
    -> /\ c.arg[p] \in ArgsOf("Enq")
       /\ c.res[p] = "BOT"
       /\ d.state  = c.state \o <<c.arg[p].val>>
       /\ d.op     = c.op
       /\ d.arg    = c.arg
       /\ d.res    = [c.res EXCEPT ![p] = "ACK"]
    [] (c.op[p] = "Deq")
    -> /\ c.arg[p] \in ArgsOf("Deq")
       /\ c.res[p] = "BOT"
       /\ c.state  # <<>>
       /\ d.state  = Tail(c.state)
       /\ d.op     = c.op
       /\ d.arg    = c.arg
       /\ d.res    = [c.res EXCEPT ![p] = Head(c.state)]
    [] OTHER 
    -> FALSE

=============================================================================