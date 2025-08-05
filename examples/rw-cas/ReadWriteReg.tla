---------------------------- MODULE ReadWriteReg ----------------------------
(***************************************************************************)
(* This module defines the read-write register type, in a way that is      *)
(* compatible with meta-configuration tracking.                            *)
(***************************************************************************)
(* Author: Ugur Y. Yavuz (Boston University)                               *)
(* Last updated: 2025-07-24                                                *)
(***************************************************************************)

CONSTANTS 
  ACK,      (* Default return value for returns with no def. value *)
  BOT,      (* Symbolic bottom value *)
  ProcSet,  (* Symbolic set of processes *)
  RegDomain (* Domain of register values *)

(***************************************************************************)
(* Operations and arguments                                                *)
(***************************************************************************)
OpNames == {"Read", "Write"}
                
ArgsOf(op) ==
  CASE op = "Read"  -> {BOT}
    [] op = "Write" -> [newval: RegDomain]
    
RetsOf(op) ==
  CASE op = "Read"  -> RegDomain
    [] op = "Write" -> {ACK}

(***************************************************************************)
(* State domain and initial state                                          *)
(***************************************************************************)
StateDomain == RegDomain
InitState == CHOOSE val \in StateDomain : TRUE  (* Arbitr. RegDomain val *)

(***************************************************************************)
(* Transition relation                                                     *)
(***************************************************************************)
(* Delta(c, p, d) is true if process p's operation changes configuration c *)
(* to configuration d.                                                     *)
(***************************************************************************)
Delta(c, p, d) == 
  CASE (c.op[p] = "Read")
    -> /\ c.arg[p] \in ArgsOf("Read")
       /\ c.res[p] = BOT
       /\ d.state  = c.state
       /\ d.op     = c.op
       /\ d.arg    = c.arg
       /\ d.res    = [c.res EXCEPT ![p] = c.state]
    [] (c.op[p] = "Write")
    -> /\ c.arg[p] \in ArgsOf("Write")
       /\ c.res[p] = BOT
       /\ d.state  = c.arg[p].newval
       /\ d.op     = c.op
       /\ d.arg    = c.arg
       /\ d.res    = [c.res EXCEPT ![p] = ACK]
    [] OTHER 
    -> FALSE

(***************************************************************************)
(* Instantiate the meta-configuration tracking module                      *)
(***************************************************************************)
INSTANCE MCTracking

=============================================================================