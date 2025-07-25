---------------------------- MODULE ReadWriteReg ----------------------------
(***************************************************************************)
(* This module defines the read-write register type, in a way that is      *)
(* compatible with meta-configuration tracking.                            *)
(***************************************************************************)
(* Author: Ugur Y. Yavuz (Boston University)                               *)
(* Last updated: 2025-07-24                                                *)
(***************************************************************************)

CONSTANTS ACK,      (* Default return value for returns with no def. value *)
          BOT,      (* Symbolic bottom value *)
          ProcSet,  (* Symbolic set of processes *)
          RegDomain (* Domain of register values *)

(***************************************************************************)
(* Operations and arguments                                                *)
(***************************************************************************)
OpNames == {"Read", "Write"}
ArgsOf(op) == CASE op = "Read"  -> {BOT}
                [] op = "Write" -> [newval: RegDomain]
                
(***************************************************************************)
(* Domain of configurations                                                *)
(***************************************************************************)
StateDomain == RegDomain
OpDomain    == OpNames \union {BOT}
ArgDomain   == [newval: RegDomain] \union {BOT}
RetDomain   == RegDomain \union {ACK}
ResDomain   == RetDomain \union {BOT}

ConfigDomain == [state: StateDomain, 
                 op: [ProcSet -> OpDomain], 
                 arg: [ProcSet -> ArgDomain], 
                 res: [ProcSet -> ResDomain]]

(***************************************************************************)
(* Transition relation                                                     *)
(***************************************************************************)
(* Delta(c, p, d) is true if process p's operation changes configuration c *)
(* to configuration d.                                                     *)
(***************************************************************************)
Delta(c, p, d) == 
    CASE (c.op[p] = "Read" /\ c.arg[p] = BOT /\ c.res[p] = BOT)
      -> /\ d.state = c.state
         /\ d.op    = c.op
         /\ d.arg   = c.arg
         /\ d.res   = [c.res EXCEPT ![p] = c.state]
      [] (c.op[p] = "Write" /\ c.arg[p].newval \in RegDomain /\ c.res[p] = BOT)
      -> /\ d.state = c.arg[p].newval
         /\ d.op    = c.op
         /\ d.arg   = c.arg
         /\ d.res   = [c.res EXCEPT ![p] = ACK]
      [] OTHER -> FALSE

=============================================================================