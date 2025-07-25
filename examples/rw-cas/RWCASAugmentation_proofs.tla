---------------------- MODULE RWCASAugmentation_proofs ----------------------
(***************************************************************************)
(* This module defines the augmentation of RWCAS with the meta-config      *)
(* tracking variable and the theorem that P != {} is an invariant of the   *)
(* augmented algorithm. This proves the linearizability of RWCAS.          *)
(***************************************************************************)
(* Author: Ugur Y. Yavuz (Boston University)                               *)
(* Last updated: 2025-07-25                                                *)
(***************************************************************************)

EXTENDS RWCAS, Assumptions, FiniteSetTheorems, TLAPS
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
(* THEOREMS                                                                *)
(***************************************************************************)

THEOREM ASpecImpliesSpec == ASpec => Spec
  <1>1. AInit => Init
    BY DEF AInit
  <1>2. [ANext]_avars => [Next]_vars
    BY DEF ANext, Next, avars
  <1> QED
    BY <1>1, <1>2, PTL DEF ASpec, Spec

TypeOK == /\ X \in RegDomain
          /\ x \in [ProcSet -> RegDomain]
          /\ arg \in [ProcSet -> ArgDomain]
          /\ ret \in [ProcSet -> RetDomain]
          /\ pc \in [ProcSet -> LineIDs]
          /\ \A p \in ProcSet : pc[p] # "RM" => arg[p] \in ArgsOf(PCtoOp(pc[p])) 

THEOREM SpecTypeOK == Spec => []TypeOK
  <1>1. Init => TypeOK
    BY RegDomainNE DEF Init, InitState, TypeOK, LineIDs
  <1>2. TypeOK /\ [Next]_vars => TypeOK'
    <2> SUFFICES ASSUME TypeOK,
                        [Next]_vars
                 PROVE  TypeOK'
      OBVIOUS
    <2>1. ASSUME NEW p \in ProcSet,
                 InvokeAct(p)
          PROVE  TypeOK'
      BY <2>1 DEF TypeOK, InvokeAct, LineIDs, ArgsOf, ArgDomain, PCtoOp, OpToInvocLine, OpNames
    <2>2. ASSUME NEW p \in ProcSet,
                 NEW LineAct \in IntLines(p),
                 LineAct
          PROVE  TypeOK'
      <3>1. CASE R1(p)
        BY <3>1 DEF TypeOK, R1, LineIDs, ArgsOf, PCtoOp
      <3>2. CASE W1(p)
        BY <3>2 DEF TypeOK, W1, LineIDs, ArgsOf, PCtoOp
      <3>3. CASE W2(p)
        BY <3>3 DEF TypeOK, W2, LineIDs, ArgsOf, PCtoOp
      <3> QED
        BY <2>2, <3>1, <3>2, <3>3 DEF IntLines
    <2>3. ASSUME NEW p \in ProcSet,
                 NEW LineAct \in RetLines(p),
                 LineAct
          PROVE  TypeOK'
      <3>1. CASE R2(p)
        BY <3>1 DEF TypeOK, R2, LineIDs, ArgsOf, PCtoOp, RetDomain
      <3>2. CASE W3(p)
        BY <3>2 DEF TypeOK, W3, LineIDs, ArgsOf, PCtoOp, RetDomain
      <3> QED
        BY <2>3, <3>1, <3>2 DEF RetLines
    <2>4. CASE UNCHANGED vars
      BY <2>4 DEF vars, TypeOK
    <2>5. QED
      BY <2>1, <2>2, <2>3, <2>4 DEF IntermAct, Next, ReturnAct
  <1> QED
    BY <1>1, <1>2, PTL DEF Spec

FinActiveInv == IsFiniteSet({q \in ProcSet : pc[q] # "RM"})

THEOREM SpecFinActiveInv == Spec => []FinActiveInv
  <1> SUFFICES ASSUME []TypeOK
               PROVE  Spec => []FinActiveInv
    BY SpecTypeOK
  <1>1. Init => FinActiveInv
    BY FS_EmptySet DEF Init, FinActiveInv
  <1>2. FinActiveInv /\ [Next]_vars => FinActiveInv'
    <2> SUFFICES ASSUME FinActiveInv,
                        TypeOK,
                        [Next]_vars
                 PROVE  FinActiveInv'
      BY PTL
    <2>1. ASSUME NEW p \in ProcSet,
                 InvokeAct(p)
          PROVE  FinActiveInv'
      <3> USE <2>1 DEF InvokeAct
      <3>1. {q \in ProcSet : pc'[q] # "RM"} \in SUBSET {q \in ProcSet : pc[q] # "RM" \/ q = p}
        BY DEF TypeOK
      <3>2. IsFiniteSet({q \in ProcSet : pc[q] # "RM"} \union {p})
        BY FS_Union, FS_Singleton DEF FinActiveInv
      <3>3. IsFiniteSet({q \in ProcSet : pc'[q] # "RM"})
        BY FS_Subset, <3>1, <3>2
      <3> QED
        BY <3>3 DEF FinActiveInv
    <2>2. ASSUME NEW p \in ProcSet,
                 NEW LineAct \in IntLines(p),
                 LineAct
          PROVE  FinActiveInv'
      <3>1. CASE R1(p)
        BY <3>1, FS_Subset DEF FinActiveInv, TypeOK, R1
      <3>2. CASE W1(p)
        BY <3>2, FS_Subset DEF FinActiveInv, TypeOK, W1
      <3>3. CASE W2(p)
        BY <3>3, FS_Subset DEF FinActiveInv, TypeOK, W2
      <3> QED
        BY <2>2, <3>1, <3>2, <3>3 DEF IntLines
    <2>3. ASSUME NEW p \in ProcSet,
                 NEW LineAct \in RetLines(p),
                 LineAct
          PROVE  FinActiveInv'
      <3>1. CASE R2(p)
        BY <3>1, FS_Subset DEF FinActiveInv, TypeOK, R2
      <3>2. CASE W3(p)
        BY <3>2, FS_Subset DEF FinActiveInv, TypeOK, W3
      <3> QED
        BY <2>3, <3>1, <3>2 DEF RetLines
    <2>4. CASE UNCHANGED vars
      BY <2>4, Zenon DEF vars, FinActiveInv
    <2>5. QED
      BY <2>1, <2>2, <2>3, <2>4 DEF IntermAct, Next, ReturnAct
  <1> QED
    BY <1>1, <1>2, PTL DEF Spec

(* TODO! - Rewrite this so that c.op and c.arg are more condensely specified via PCtoOp *)
Q == {c \in ConfigDomain : 
        /\ c.state = X
        /\ \A q \in ProcSet : 
           /\ pc[q] = "RM" => (c.op[q] = BOT     /\ c.arg[q] = BOT    /\ c.res[q] = BOT)
           /\ pc[q] = "R1" => (c.op[q] = "Read"  /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
           /\ pc[q] = "R2" => (c.op[q] = "Read"  /\ c.arg[q] = arg[q] /\ c.res[q] = x[q])
           /\ pc[q] = "W1" => (c.op[q] = "Write" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
           /\ pc[q] = "W2" => \/ (c.op[q] = "Write" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                              \/ /\ X # x[q]
                                 /\ (c.op[q] = "Write" /\ c.arg[q] = arg[q] /\ c.res[q] = ACK)
           /\ pc[q] = "W3" => (c.op[q] = "Write" /\ c.arg[q] = arg[q] /\ c.res[q] = ACK)}

QInv1 == Q # {}

THEOREM SpecQInv1 == Spec => []QInv1
  <1> SUFFICES ASSUME TypeOK
               PROVE  Q # {}
    BY SpecTypeOK, PTL DEF QInv1
  <1>1. PICK val \in StateDomain : val = X
    BY DEF TypeOK, StateDomain
  <1> DEFINE cop == [p \in ProcSet |-> PCtoOp(pc[p])]
  <1>2. cop \in [ProcSet -> OpDomain]
    BY DEF OpDomain, OpNames, PCtoOp, TypeOK, LineIDs
  <1> DEFINE carg == [p \in ProcSet |-> IF pc[p] = "RM" THEN BOT ELSE arg[p]]
  <1>3. carg \in [ProcSet -> ArgDomain]
    BY DEF ArgDomain, TypeOK, ArgsOf, PCtoOp
  <1> DEFINE cres == [p \in ProcSet |-> CASE pc[p] = "R2" -> x[p]
                                          [] pc[p] = "W3" -> ACK
                                          [] OTHER -> BOT]
  <1>4. cres \in [ProcSet -> ResDomain]
    BY DEF ResDomain, RetDomain, TypeOK
  <1> DEFINE c == [state |-> val, op |-> cop, arg |-> carg, res |-> cres]
  <1>5. c \in ConfigDomain
    BY <1>1, <1>2, <1>3, <1>4 DEF ConfigDomain
  <1> SUFFICES c \in Q
    OBVIOUS
  <1> QED
    BY <1>1, <1>5, Zenon DEF Q, PCtoOp, TypeOK

QInv2 == Q \in SUBSET P

THEOREM ASpecQInv2 == ASpec => []QInv2

THEOREM RWCASisLinearizable == ASpec => [](P # {})
  <1>1. (Q # {} /\ Q \in SUBSET P) => P # {} 
    OBVIOUS
  <1> SUFFICES ASpec => [](Q # {} /\ Q \in SUBSET P)
    BY <1>1, PTL
  <1> QED
    BY SpecQInv1, ASpecQInv2, ASpecImpliesSpec, PTL DEF QInv1, QInv2

-----------------------------------------------------------------------------
\* WIP

THEOREM SpecQInv2 == ASpec => []QInv2
\*   <1> SUFFICES ASSUME []TypeOK, []FinActiveInv, []QInv1
\*                PROVE  Spec => []QInv2
\*     BY SpecTypeOK, SpecFinActiveInv, SpecQInv1, PTL
\*   <1>1. Init => QInv2
\*   <1>2. QInv2 /\ [Next]_vars => QInv2'
\*   <1> QED 
\*     BY <1>1, <1>2, PTL DEF Spec

InvProp == Spec => [][\A p \in ProcSet : InvokeAct(p) => Q' \in SUBSET Evolve(Invoke(Q, p, PCtoOp(pc'[p]), arg'[p]))]_vars
IntProp == Spec => [][\A p \in ProcSet : IntermAct(p) => Q' \in SUBSET Evolve(Q)]_vars
RetProp == Spec => [][\A p \in ProcSet : ReturnAct(p) => Q' \in SUBSET Filter(Evolve(Q), p, ret'[p])]_vars

=============================================================================