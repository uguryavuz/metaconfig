------------------------- MODULE RWCASAugmentation --------------------------
(***************************************************************************)
(* This module defines the augmentation of RWCAS with the meta-config      *)
(* tracking variable and the theorem that P != {} is an invariant of the   *)
(* augmented algorithm. This proves the linearizability of RWCAS.          *)
(***************************************************************************)
(* Author: Ugur Y. Yavuz (Boston University)                               *)
(* Last updated: 2025-07-25                                                *)
(***************************************************************************)

EXTENDS RWCAS
INSTANCE MCTracking

VARIABLE P
avars == <<vars, P>>

(***************************************************************************)
(* The initial state of the augmented algorithm.                           *)
(***************************************************************************)
AInit == /\ Init
         /\ P = {[state |-> InitState,
                  op    |-> [p \in ProcSet |-> BOT],
                  arg   |-> [p \in ProcSet |-> BOT],
                  res   |-> [p \in ProcSet |-> BOT]]}

(***************************************************************************)
(* The next action of the augmented algorithm.                             *)
(***************************************************************************)
(* The next action of the augmented algorithm is defined as follows:       *)
(* 1. If a process p invokes an operation, then the meta-configuration     *)
(*    tracking variable P is updated to include the invocation,            *)
(*    and allows subsequent evolving.                                      *)
(* 2. If a process p executes an intermediate line, then the meta-         *)
(*    configuration tracking variable P is updated via evolving.           *)
(*    (i.e. the linearization of all possible sequences of processes)      *)
(* 3. If a process p returns a value, then the meta-configuration tracking *)
(*    variable P, post-evolving, is filtered to include only those configs *)
(*    that have p returning the value to-be-returned (which is the         *)
(*    value in the ret register in the next state).                        *)
(***************************************************************************)
ANext == \E p \in ProcSet : \/ /\ InvokeAct(p)
                               /\ P' = Evolve(Invoke(P, p, PCtoOp(pc'[p]), arg'[p]))
                            \/ /\ IntermAct(p)
                               /\ P' = Evolve(P)
                            \/ /\ ReturnAct(p)
                               /\ P' = Filter(Evolve(P), p, ret'[p])
    
(***************************************************************************)
(* The spec of the augmented algorithm.                                    *)
(***************************************************************************)
ASpec == AInit /\ [][ANext]_avars

(***************************************************************************)
(* THEOREM                                                                 *)
(***************************************************************************)
THEOREM RWCASisLinearizable == ASpec => [](P # {})

=============================================================================