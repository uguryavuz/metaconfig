------------------------ MODULE RWCASLinearizability ------------------------
EXTENDS RWCAS
INSTANCE MCTracking

\* CONSTANTS 
\*   ImplInit, (* RWCAS *)
\*   InitState, (* RWCAS <- ReadWriteReg *)
\*   IntLines(_), (* RWCAS *)
\*   LineIDs, (* RWCAS *)
\*   OpToInvocLine(_), (* RWCAS *)
\*   PCtoOp(_), (* RWCAS *)
\*   RetLines(_) (* RWCAS *)

\* VARIABLES implvars, arg, ret, pc, P
\* vars == <<implvars, arg, ret, pc>>
\* varsP == <<vars, P>>

VARIABLE P
vars == <<implvars, arg, ret, pc>>
varsP == <<vars, P>>

(* Invocation action for process p *)
InvokeAct(p) == 
  /\ pc[p] = "RM"
  /\ \E op \in OpNames :
      /\ pc' = [pc EXCEPT ![p] = OpToInvocLine(op)]
      /\ \E newarg \in ArgsOf(op) : arg' = [arg EXCEPT ![p] = newarg]
  /\ UNCHANGED <<implvars, ret>>

(* Intermediate-line action for process p *)
IntermAct(p) == \E LineAct \in IntLines(p) : LineAct

(* Return action for process p *)
ReturnAct(p) == \E LineAct \in RetLines(p) : LineAct

(* Initial state *)
Init == 
  /\ ImplInit
  /\ pc = [p \in ProcSet |-> "RM"]
  /\ arg \in [ProcSet -> ArgDomain]
  /\ ret \in [ProcSet -> RetDomain]

(* Next-state relation *)
Next == \E p \in ProcSet : 
  \/ InvokeAct(p)
  \/ IntermAct(p)
  \/ ReturnAct(p)

(* Full specification *)
Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* The initial state of the augmented algorithm.                           *)
(***************************************************************************)
AInit == 
  /\ Init
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
ANext == \E p \in ProcSet : 
  \/ /\ InvokeAct(p)
     /\ P' = Evolve(Invoke(P, p, PCtoOp(pc'[p]), arg'[p]))
  \/ /\ IntermAct(p)
     /\ P' = Evolve(P)
  \/ /\ ReturnAct(p)
     /\ P' = Filter(Evolve(P), p, ret'[p])

(***************************************************************************)
(* The spec of the augmented algorithm.                                    *)
(***************************************************************************)
ASpec == AInit /\ [][ANext]_varsP

(***************************************************************************)
(* Theorem: ASpec implies Spec.                                            *)
(***************************************************************************)
THEOREM ASpecImpliesSpec == ASpec => Spec

=============================================================================