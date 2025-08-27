------------------------------ MODULE HWQueue -------------------------------
(***************************************************************************)
(* This module defines the Herlihy-Wing queue implementation.              *)
(***************************************************************************)
(* Author: Ugur Y. Yavuz (Boston University)                               *)
(* Last updated: 2025-07-24                                                *)
(***************************************************************************)

EXTENDS Integers, Queue

(***************************************************************************)
(* RWCas implementation                                                    *)
(***************************************************************************)
VARIABLES A, L, l, j, v, arg, ret, pc
implvars == <<A, L, l, j, v>>

(* E1: l <- L.F&I(1) *)
E1(p) == 
  /\ pc[p] = "E1"
  /\ l' = [l EXCEPT ![p] = L]
  /\ L' = L + 1
  /\ pc' = [pc EXCEPT ![p] = "E2"]
  /\ UNCHANGED <<A, j, v, arg, ret>>

(* E2: A[l] <- arg.val *)
E2(p) ==
  /\ pc[p] = "E2"
  /\ A' = [A EXCEPT ![l[p]] = arg[p].val]
  /\ pc' = [pc EXCEPT ![p] = "E3"]
  /\ UNCHANGED <<L, l, j, v, arg, ret>>

(* E3: return ack *)
E3(p) == 
  /\ pc[p] = "E3"
  /\ pc' = [pc EXCEPT ![p] = "RM"]
  /\ ret' = [ret EXCEPT ![p] = "ACK"]
  /\ UNCHANGED <<A, L, l, j, v, arg>>

(* D1: l <- L && j <- 1 *)
D1(p) == 
  /\ pc[p] = "D1"
  /\ l' = [l EXCEPT ![p] = L]
  /\ j' = [j EXCEPT ![p] = 1]
  /\ pc' = [pc EXCEPT ![p] = "D2"]
  /\ UNCHANGED <<A, L, v, arg, ret>>

(* D2: if (j = L) then goto D1 else   *)
(*       v <- A[j].swap("BOT");       *)
(*       if (v != "BOT") then goto D3 *)
(*       else j <- j + 1; goto D2     *)
D2(p) == 
  /\ pc[p] = "D2"
  /\ IF (j[p] = l[p]) THEN  (* CASE (j[p] = l[p]) *)
        /\ pc' = [pc EXCEPT ![p] = "D1"]
        /\ UNCHANGED <<A, L, l, j, v, arg, ret>>
        ELSE IF (A[j[p]] # "BOT") THEN (* CASE (j[p] # l[p] /\ A[j[p]] # "BOT") *)
        /\ A' = [A EXCEPT ![j[p]] = "BOT"]
        /\ v' = [v EXCEPT ![p] = A[j[p]]]
        /\ pc' = [pc EXCEPT ![p] = "D3"]
        /\ UNCHANGED <<L, l, j, arg, ret>>
        ELSE (* CASE (j[p] # l[p] /\ A[j[p]] = "BOT") *)
        /\ UNCHANGED A (* swap leaves A unchanged if A[j] = "BOT" *)
        /\ v' = [v EXCEPT ![p] = "BOT"] (* swap returns "BOT" *)
        /\ j' = [j EXCEPT ![p] = j[p] + 1]
        /\ UNCHANGED pc (* p remains at D2 *)
        /\ UNCHANGED <<L, l, arg, ret>> 

\*   /\ pc[p] = "D2"
\*   /\ CASE (j[p] = l[p]) 
\*         -> /\ pc' = [pc EXCEPT ![p] = "D1"]
\*            /\ UNCHANGED <<A, L, l, j, v, arg, ret>>
\*        [] (j[p] # l[p] /\ A[j[p]] # "BOT") 
\*         -> /\ A' = [A EXCEPT ![j[p]] = "BOT"]
\*            /\ v' = [v EXCEPT ![p] = A[j[p]]]
\*            /\ pc' = [pc EXCEPT ![p] = "D3"]
\*            /\ UNCHANGED <<L, l, j, arg, ret>>
\*        [] (j[p] # l[p] /\ A[j[p]] = "BOT") 
\*         -> /\ UNCHANGED A (* swap leaves A unchanged if A[j] = "BOT" *)
\*            /\ v' = [v EXCEPT ![p] = "BOT"] (* swap returns "BOT" *)
\*            /\ j' = [j EXCEPT ![p] = j[p] + 1]
\*            /\ UNCHANGED pc (* p remains at D2 *)
\*            /\ UNCHANGED <<L, l, arg, ret>>

(* D3: return v *)
D3(p) == 
  /\ pc[p] = "D3"
  /\ pc' = [pc EXCEPT ![p] = "RM"]
  /\ ret' = [ret EXCEPT ![p] = v[p]]
  /\ UNCHANGED <<A, L, l, j, v, arg>>

ImplInit == 
  /\ A = [i \in Nat \ {0} |-> IF i \in 1..Len(InitState) THEN InitState[i] ELSE "BOT"]
  /\ L = Len(InitState) + 1
  /\ l \in [ProcSet -> Nat \ {0}]
  /\ j \in [ProcSet -> Nat \ {0}]
  /\ v \in [ProcSet -> EltDomain \cup {"BOT"}]

-----------------------------------------------------------------------------
(***************************************************************************)
(* Correspondence between operations and line identifiers                  *)
(***************************************************************************)

(* First line of each operation *)
OpToFirstLine(op) == 
  CASE op = "Enq" -> "E1"
    [] op = "Deq" -> "D1"

(* Program counter to operation mapping *)
PCtoOp(pcp) == 
  CASE pcp \in {"E1", "E2", "E3"} -> "Enq"
    [] pcp \in {"D1", "D2", "D3"} -> "Deq"
    [] pcp = "RM" -> "BOT"

(* Line identifiers *)
LineIDs == {"E1", "E2", "E3", "D1", "D2", "D3", "RM"}

(* Intermediate line actions for given process *)
InterLines(p) == {E1(p), E2(p), D1(p), D2(p)}

(* Return line actions for given process *)
ReturnLines(p) == {E3(p), D3(p)}

=============================================================================
