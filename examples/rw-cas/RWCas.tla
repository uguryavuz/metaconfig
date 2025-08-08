------------------------------- MODULE RWCas --------------------------------
(***************************************************************************)
(* This module defines the RWCas implementation of the read-write          *)
(* register type.                                                          *)
(***************************************************************************)
(* Author: Ugur Y. Yavuz (Boston University)                               *)
(* Last updated: 2025-07-24                                                *)
(***************************************************************************)

EXTENDS ReadWriteReg

(***************************************************************************)
(* RWCas implementation                                                    *)
(***************************************************************************)
VARIABLES X, x, arg, ret, pc
implvars == <<X, x>>

(* R1: x <- X *)
R1(p) == 
  /\ pc[p] = "R1"
  /\ x' = [x EXCEPT ![p] = X]
  /\ pc' = [pc EXCEPT ![p] = "R2"]
  /\ UNCHANGED <<X, arg, ret>>

(* R2: return x *)
R2(p) == 
  /\ pc[p] = "R2"
  /\ pc' = [pc EXCEPT ![p] = "RM"]
  /\ ret' = [ret EXCEPT ![p] = x[p]]
  /\ UNCHANGED <<X, x, arg>>

(* W1: x <- X *)
W1(p) == 
  /\ pc[p] = "W1"
  /\ x' = [x EXCEPT ![p] = X]
  /\ pc' = [pc EXCEPT ![p] = "W2"]
  /\ UNCHANGED <<X, arg, ret>>

(* W2: X.CAS(x, arg.newval) *)
W2(p) == 
  /\ pc[p] = "W2"
  /\ IF X = x[p] 
        THEN X' = arg[p].newval
        ELSE X' = X
  /\ pc' = [pc EXCEPT ![p] = "W3"]
  /\ UNCHANGED <<x, arg, ret>>

(* W3: return ack *)
W3(p) == 
  /\ pc[p] = "W3"
  /\ pc' = [pc EXCEPT ![p] = "RM"]
  /\ ret' = [ret EXCEPT ![p] = ACK]
  /\ UNCHANGED <<X, x, arg>>

ImplInit == 
  /\ X = InitState
  /\ x \in [ProcSet -> RegDomain]

(************************************************************************)
(* Correspondence between operations and line identifiers               *)
(************************************************************************)

(* First line of each operation *)
OpToFirstLine(op) == 
  CASE op = "Read"  -> "R1"
    [] op = "Write" -> "W1"

(* Program counter to operation mapping *)
PCtoOp(pcp) == 
  CASE pcp \in {"R1", "R2"} -> "Read"
    [] pcp \in {"W1", "W2", "W3"} -> "Write"
    [] pcp = "RM" -> BOT

(* Line identifiers *)
LineIDs == {"R1", "R2", "W1", "W2", "W3", "RM"}

(* Intermediate line actions for given process *)
InterLines(p) == {R1(p), W1(p), W2(p)}

(* Return line actions for given process *)
ReturnLines(p) == {R2(p), W3(p)}

==========================================================================
