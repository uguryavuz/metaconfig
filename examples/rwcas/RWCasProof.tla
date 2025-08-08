----------------------------- MODULE RWCasProof -----------------------------
(***************************************************************************)
EXTENDS RWCas, TLAPS
INSTANCE MCTracking

\* CONSTANTS 
\*   ImplInit, (* RWCAS *)
\*   InitState, (* RWCAS <- ReadWriteReg *)
\*   InterLines(_), (* RWCAS *)
\*   LineIDs, (* RWCAS *)
\*   OpToFirstLine(_), (* RWCAS *)
\*   PCtoOp(_), (* RWCAS *)
\*   ReturnLines(_) (* RWCAS *)

\* VARIABLES implvars, arg, ret, pc, P
\* vars == <<implvars, arg, ret, pc>>
\* varsP == <<vars, P>>

VARIABLE P
vars == <<implvars, arg, ret, pc>>
varsP == <<vars, P>>

(* Invocation action for process p *)
InvocAct(p) == 
  /\ pc[p] = "RM"
  /\ \E op \in OpNames :
      /\ pc' = [pc EXCEPT ![p] = OpToFirstLine(op)]
      /\ \E newarg \in ArgsOf(op) : arg' = [arg EXCEPT ![p] = newarg]
  /\ UNCHANGED <<implvars, ret>>

(* Intermediate-line action for process p *)
InterAct(p) == \E LineAct \in InterLines(p) : LineAct

(* Return action for process p *)
ReturnAct(p) == \E LineAct \in ReturnLines(p) : LineAct

(* Initial state *)
Init == 
  /\ ImplInit
  /\ pc = [p \in ProcSet |-> "RM"]
  /\ arg \in [ProcSet -> ArgDomain]
  /\ ret \in [ProcSet -> RetDomain]

(* Next-state relation *)
Next == \E p \in ProcSet : 
  \/ InvocAct(p)
  \/ InterAct(p)
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
  \/ /\ InvocAct(p)
     /\ P' = Evolve(Invoke(P, p, PCtoOp(pc'[p]), arg'[p]))
  \/ /\ InterAct(p)
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
  <1>1. AInit => Init
    BY DEF AInit
  <1>2. [ANext]_varsP => [Next]_vars
    BY DEF ANext, Next, varsP
  <1> QED 
    BY <1>1, <1>2, PTL DEF ASpec, Spec

-----------------------------------------------------------------------------
(***************************************************************************)
(* ASSUMPTIONS                                                             *)
(***************************************************************************)



-----------------------------------------------------------------------------
(***************************************************************************)
(* INVARIANTS                                                              *)
(***************************************************************************)



-----------------------------------------------------------------------------
(***************************************************************************)
(* PLAUSIBILITY SET DEFINITION AND INVARIANTS                              *)
(***************************************************************************)

(***************************************************************************)
(* Plausibility set definition                                             *)
(***************************************************************************)
Q == {c \in ConfigDomain : FALSE}

(***************************************************************************)
(* Plausibility set theorem 1: Q is non-empty is an invariant of Spec.     *)
(***************************************************************************)

THEOREM PlausSetThm1 == 
    Spec => [](Q # {})

LEMMA PlausSetInitLemma == 
    AInit => Q = P

InvocProperty == 
  \A p \in ProcSet : InvocAct(p) => (Q' \in SUBSET Evolve(Invoke(Q, p, PCtoOp(pc'[p]), arg'[p])))

LEMMA InvocLemma == 
    ASpec => [][InvocProperty]_varsP

InterProperty == 
  \A p \in ProcSet : InterAct(p) => (Q' \in SUBSET Evolve(Q))

LEMMA InterLemma == 
    ASpec => [][InterProperty]_varsP

ReturnProperty ==
  \A p \in ProcSet : ReturnAct(p) => (Q' \in SUBSET Filter(Evolve(Q), p, ret'[p]))

LEMMA ReturnLemma == 
    ASpec => [][ReturnProperty]_varsP

LEMMA UnchangedLemma == UNCHANGED varsP => Q' = Q

THEOREM PlausSetThm2 == ASpec => [](Q \in SUBSET P)
  <1> SUFFICES ASSUME [][InvocProperty]_varsP,
                      [][InterProperty]_varsP,
                      [][ReturnProperty]_varsP
               PROVE  ASpec => [](Q \in SUBSET P)
    BY ASpecImpliesSpec, InvocLemma, InterLemma, ReturnLemma
  <1>1. AInit => Q \in SUBSET P 
    BY PlausSetInitLemma
  <1>2. (Q \in SUBSET P) /\ [ANext]_varsP => (Q \in SUBSET P)'
    <2>1. ASSUME Q \in SUBSET P,
                 NEW p \in ProcSet, 
                 InvocAct(p),
                 ~(UNCHANGED varsP),
                 P' = Evolve(Invoke(P, p, PCtoOp(pc'[p]), arg'[p]))
          PROVE  (Q \in SUBSET P)'
      <3>1. [InvocProperty]_varsP 
        BY PTL
      <3>2. Invoke(Q, p, PCtoOp(pc'[p]), arg'[p]) \in SUBSET Invoke(P, p, PCtoOp(pc'[p]), arg'[p]) 
        BY <2>1, InvokeForSubset
      <3> SUFFICES Q' \in SUBSET Evolve(Invoke(P, p, PCtoOp(pc'[p]), arg'[p])) 
        BY <2>1
      <3> SUFFICES Q' \in SUBSET Evolve(Invoke(Q, p, PCtoOp(pc'[p]), arg'[p])) 
        BY <3>2, EvolveForSubset
      <3> QED 
        BY <2>1, <3>1 DEF InvocProperty
    <2>2. ASSUME Q \in SUBSET P,
                 NEW p \in ProcSet, 
                 InterAct(p),
                 ~(UNCHANGED varsP),
                 P' = Evolve(P)
          PROVE  (Q \in SUBSET P)'
      <3>1. [InterProperty]_varsP 
        BY PTL
      <3> SUFFICES Q' \in SUBSET Evolve(P) 
        BY <2>2
      <3> SUFFICES Q' \in SUBSET Evolve(Q) 
        BY <2>2, EvolveForSubset
      <3> QED 
        BY <2>2, <3>1 DEF InterProperty
    <2>3. ASSUME Q \in SUBSET P,
                 NEW p \in ProcSet, 
                 ReturnAct(p),
                 ~(UNCHANGED varsP),
                 P' = Filter(Evolve(P), p, ret'[p])
          PROVE  (Q \in SUBSET P)'
      <3>1. [ReturnProperty]_varsP
        BY PTL
      <3>2. Evolve(Q) \in SUBSET Evolve(P)
        BY <2>3, EvolveForSubset
      <3> SUFFICES Q' \in SUBSET Filter(Evolve(P), p, ret'[p])
        BY <2>3
      <3> SUFFICES Q' \in SUBSET Filter(Evolve(Q), p, ret'[p])
        BY <3>2, FilterForSubset
      <3> QED
        BY <2>3, <3>1 DEF ReturnProperty
    <2>4. ASSUME Q \in SUBSET P,
                 UNCHANGED varsP
          PROVE  (Q \in SUBSET P)'
      BY UnchangedLemma, <2>4 DEF varsP
    <2> QED
      BY <2>1, <2>2, <2>3, <2>4 DEF ANext
  <1> QED
    BY <1>1, <1>2, PTL DEF ASpec

-----------------------------------------------------------------------------
(***************************************************************************)
(* META-CONFIGURATION TRACKING LINEARIZABILITY INVARIANT                   *)
(***************************************************************************)

THEOREM Linearizability == ASpec => [](P # {})
  <1> SUFFICES ASSUME [](Q # {}), [](Q \in SUBSET P)
               PROVE  ASpec => [](P # {})
    BY ASpecImpliesSpec, PlausSetThm1, PlausSetThm2
  <1>1. AInit => P # {}
    <2>1. Q # {} /\ Q \in SUBSET P BY PTL
    <2> QED BY <2>1
  <1>2. [ANext]_varsP => (P # {})'
    <2>1. (Q # {})' /\ (Q \in SUBSET P)' BY PTL
    <2> QED BY <2>1
  <1> QED
    BY <1>1, <1>2, PTL DEF ASpec

=============================================================================
