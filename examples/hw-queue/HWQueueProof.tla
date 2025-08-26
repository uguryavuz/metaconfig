---------------------------- MODULE HWQueueProof ----------------------------
EXTENDS HWQueue, TLAPS, FiniteSetTheorems, FinitePermutations
INSTANCE MCTracking

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
           op    |-> [p \in ProcSet |-> "BOT"],
           arg   |-> [p \in ProcSet |-> "BOT"],
           res   |-> [p \in ProcSet |-> "BOT"]]}

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
ASSUME BotNotElt == "BOT" \notin EltDomain

-----------------------------------------------------------------------------
(***************************************************************************)
(* INVARIANTS                                                              *)
(***************************************************************************)

TypeOK == /\ A \in [Nat \ {0} -> EltDomain \cup {"BOT"}]
          /\ L \in Nat \ {0}
          /\ l \in [ProcSet -> Nat \ {0}]
          /\ j \in [ProcSet -> Nat \ {0}]
          /\ v \in [ProcSet -> EltDomain \cup {"BOT"}]
          /\ \A p \in ProcSet : pc[p] = "D3" => v[p] # "BOT"
          /\ arg \in [ProcSet -> ArgDomain]
          /\ \A p \in ProcSet : pc[p] # "RM" => arg[p] \in ArgsOf(PCtoOp(pc[p]))
          /\ ret \in [ProcSet -> RetDomain]
          /\ pc \in [ProcSet -> LineIDs]

LEMMA SpecTypeOK == Spec => []TypeOK
  <1>1. Init => TypeOK 
    <2> SUFFICES ASSUME Init
                 PROVE  TypeOK
      OBVIOUS
    <2>1. <<>> \in Seq(EltDomain)
      OBVIOUS
    <2> QED
      BY <2>1 DEF Init, ImplInit, InitState, TypeOK, LineIDs, StateDomain, ArgDomain
  <1>2. TypeOK /\ [Next]_vars => TypeOK' 
    <2> SUFFICES ASSUME TypeOK,
                        [Next]_vars
                 PROVE  TypeOK'
      OBVIOUS
    <2>1. ASSUME NEW p \in ProcSet,
                 InvocAct(p)
          PROVE  TypeOK'
      BY <2>1 DEF implvars, TypeOK, InvocAct, LineIDs, ArgsOf, ArgDomain, PCtoOp, OpToFirstLine, OpNames
    <2>2. ASSUME NEW p \in ProcSet,
                 NEW LineAct \in InterLines(p),
                 LineAct
          PROVE  TypeOK'
      <3>1. CASE E1(p)
        BY <3>1 DEF TypeOK, E1, LineIDs, ArgsOf, PCtoOp
      <3>2. CASE E2(p)
        BY <3>2 DEF TypeOK, E2, LineIDs, ArgsOf, PCtoOp
      <3>3. CASE D1(p)
        BY <3>3 DEF TypeOK, D1, LineIDs, ArgsOf, PCtoOp
      <3>4. CASE D2(p)
        <4>1. (A \in [Nat \ {0} -> EltDomain \cup {"BOT"}])'
          BY <3>4 DEF TypeOK, D2, LineIDs, ArgsOf, PCtoOp
        <4>2. (L \in Nat \ {0})'
          BY <3>4 DEF TypeOK, D2, LineIDs, ArgsOf, PCtoOp
        <4>3. (l \in [ProcSet -> Nat \ {0}])'
          BY <3>4 DEF TypeOK, D2, LineIDs, ArgsOf, PCtoOp
        <4>4. (j \in [ProcSet -> Nat \ {0}])'
          BY <3>4 DEF TypeOK, D2, LineIDs, ArgsOf, PCtoOp
        <4>5. (v \in [ProcSet -> EltDomain \cup {"BOT"}])'
          BY <3>4 DEF TypeOK, D2, LineIDs, ArgsOf, PCtoOp
        <4>6. (\A p_1 \in ProcSet : pc[p_1] = "D3" => v[p_1] # "BOT")'
          BY <3>4 DEF TypeOK, D2, LineIDs, ArgsOf, PCtoOp
        <4>7. (arg \in [ProcSet -> ArgDomain])'
          BY <3>4 DEF TypeOK, D2, LineIDs, ArgsOf, PCtoOp
        <4>8. (\A p_1 \in ProcSet : pc[p_1] # "RM" => arg[p_1] \in ArgsOf(PCtoOp(pc[p_1])))'
          BY <3>4 DEF TypeOK, D2, LineIDs, ArgsOf, PCtoOp
        <4>9. (ret \in [ProcSet -> RetDomain])'
          BY <3>4 DEF TypeOK, D2, LineIDs, ArgsOf, PCtoOp
        <4>10. (pc \in [ProcSet -> LineIDs])'
          BY <3>4 DEF TypeOK, D2, LineIDs, ArgsOf, PCtoOp
        <4>11. QED
          BY <4>1, <4>10, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9 DEF TypeOK       
      <3> QED 
        BY <2>2, <3>1, <3>2, <3>3, <3>4 DEF InterLines
    <2>3. ASSUME NEW p \in ProcSet,
                 NEW LineAct \in ReturnLines(p),
                 LineAct
          PROVE  TypeOK'
      <3>1. CASE E3(p)
        BY <3>1 DEF TypeOK, E3, LineIDs, ArgsOf, PCtoOp, OpNames, RetDomain, RetsOf
      <3>2. CASE D3(p)
        BY <3>2 DEF TypeOK, D3, LineIDs, ArgsOf, PCtoOp, OpNames, RetDomain, RetsOf
      <3> QED 
        BY <2>3, <3>1, <3>2 DEF ReturnLines
    <2>4. CASE UNCHANGED vars
      BY <2>4 DEF vars, implvars, TypeOK
    <2> QED
      BY <2>1, <2>2, <2>3, <2>4 DEF InterAct, Next, ReturnAct
  <1> QED
    BY <1>1, <1>2, PTL DEF Spec

(* Finite active processes invariant *)
FinActive == IsFiniteSet({q \in ProcSet : pc[q] # "RM"})

LEMMA SpecFinActive == Spec => []FinActive
  <1> SUFFICES ASSUME []TypeOK
               PROVE  Spec => []FinActive
    BY SpecTypeOK
  <1>1. Init => FinActive
    BY FS_EmptySet DEF Init, FinActive
  <1>2. FinActive /\ [Next]_vars => FinActive'
    <2> SUFFICES ASSUME FinActive,
                        [Next]_vars
                 PROVE  FinActive'
      OBVIOUS
    <2>1. ASSUME NEW p \in ProcSet,
                 InvocAct(p)
          PROVE  FinActive'
      <3> USE <2>1 DEF InvocAct
      <3>1. TypeOK
        BY PTL
      <3>2. {q \in ProcSet : pc'[q] # "RM"} \in SUBSET {q \in ProcSet : pc[q] # "RM" \/ q = p}
        BY <3>1 DEF TypeOK
      <3>3. IsFiniteSet({q \in ProcSet : pc[q] # "RM"} \union {p})
        BY FS_Union, FS_Singleton DEF FinActive
      <3>4. IsFiniteSet({q \in ProcSet : pc'[q] # "RM"})
        BY FS_Subset, <3>2, <3>3
      <3> QED
        BY <3>4 DEF FinActive
    <2>2. ASSUME NEW p \in ProcSet,
                 NEW LineAct \in InterLines(p),
                 LineAct
          PROVE  FinActive'
      <3>1. TypeOK
        BY PTL
      <3> USE <3>1
      <3>2. CASE E1(p)
        BY <3>2, FS_Subset DEF FinActive, TypeOK, E1
      <3>3. CASE E2(p)
        BY <3>3, FS_Subset DEF FinActive, TypeOK, E2
      <3>4. CASE D1(p)
        BY <3>4, FS_Subset DEF FinActive, TypeOK, D1
      <3>5. CASE D2(p)
        BY <3>5, FS_Subset DEF FinActive, TypeOK, D2
      <3> QED
        BY <2>2, <3>2, <3>3, <3>4, <3>5 DEF InterLines
    <2>3. ASSUME NEW p \in ProcSet,
                 NEW LineAct \in ReturnLines(p),
                 LineAct
          PROVE  FinActive'
      <3>1. TypeOK
        BY PTL
      <3> USE <3>1
      <3>2. CASE E3(p)
        BY <3>2, FS_Subset DEF FinActive, TypeOK, E3
      <3>3. CASE D3(p)
        BY <3>3, FS_Subset DEF FinActive, TypeOK, D3
      <3> QED
        BY <2>3, <3>2, <3>3 DEF ReturnLines
    <2>4. CASE UNCHANGED vars
      BY <2>4 DEF vars, FinActive
    <2>5. QED
      BY <2>1, <2>2, <2>3, <2>4 DEF InterAct, Next, ReturnAct
  <1> QED
    BY <1>1, <1>2, PTL DEF Spec

EnqIdxInv == \A p \in ProcSet : pc[p] \in {"E2", "E3"} 
                => /\ l[p] \in 1..(L-1)
                   /\ pc[p] = "E2" => A[l[p]] = "BOT"
                   /\ \A q \in ProcSet : (q # p /\ pc[q] \in {"E2", "E3"}) 
                         => l[q] # l[p]

BotPastL == \A i \in Nat \ {0} : i >= L => A[i] = "BOT"

LEMMA SpecEIIBPL == Spec => [](EnqIdxInv /\ BotPastL)
  <1> SUFFICES ASSUME []TypeOK
               PROVE  Spec => [](EnqIdxInv /\ BotPastL)
    BY SpecTypeOK
  <1>1. Init => (EnqIdxInv /\ BotPastL)
    <2>1. <<>> \in Seq(EltDomain)
      OBVIOUS
    <2> QED
      BY <2>1 DEF Init, EnqIdxInv, ImplInit, StateDomain, InitState, BotPastL
  <1>2. (EnqIdxInv /\ BotPastL) /\ [Next]_vars => (EnqIdxInv /\ BotPastL)'
    <2> SUFFICES ASSUME EnqIdxInv,
                        BotPastL,
                        [Next]_vars
                 PROVE  EnqIdxInv' /\ BotPastL'
      OBVIOUS
    <2>1. ASSUME NEW p \in ProcSet,
                 InvocAct(p)
          PROVE  EnqIdxInv' /\ BotPastL'
      <3>1. TypeOK
        BY PTL
      <3> QED
        BY <2>1, <3>1 DEF InvocAct, TypeOK, EnqIdxInv, BotPastL, implvars, OpToFirstLine, OpNames
    <2>2. ASSUME NEW p \in ProcSet,
                 NEW LineAct \in InterLines(p),
                 LineAct
          PROVE  EnqIdxInv' /\ BotPastL'
      <3>1. TypeOK
        BY PTL
      <3>2. CASE E1(p)
        BY <3>1, <3>2 DEF TypeOK, EnqIdxInv, BotPastL, E1
      <3>3. CASE E2(p)
        BY <3>1, <3>3 DEF TypeOK, EnqIdxInv, BotPastL, E2
      <3>4. CASE D1(p)
        BY <3>1, <3>4 DEF TypeOK, EnqIdxInv, BotPastL, D1
      <3>5. CASE D2(p)
        BY <3>1, <3>5 DEF TypeOK, EnqIdxInv, BotPastL, D2
      <3> QED
        BY <2>2, <3>2, <3>3, <3>4, <3>5 DEF InterLines
    <2>3. ASSUME NEW p \in ProcSet,
                 NEW LineAct \in ReturnLines(p),
                 LineAct
          PROVE  EnqIdxInv' /\ BotPastL'
      <3>1. TypeOK
        BY PTL
      <3>2. CASE E3(p)
        BY <3>1, <3>2 DEF TypeOK, EnqIdxInv, BotPastL, E3
      <3>3. CASE D3(p)
        BY <3>1, <3>3 DEF TypeOK, EnqIdxInv, BotPastL, D3
      <3> QED
        BY <2>3, <3>2, <3>3 DEF ReturnLines
    <2>4. CASE UNCHANGED vars
      BY <2>4 DEF vars, implvars, EnqIdxInv, BotPastL
    <2>5. QED
      BY  <2>1, <2>2, <2>3, <2>4 DEF InterAct, Next, ReturnAct
  <1> QED
    BY <1>1, <1>2, PTL DEF Spec
    
LEMMA SpecEnqIdxInv == Spec => []EnqIdxInv
  BY SpecEIIBPL
    
LEMMA SpecBotPastL == Spec => []BotPastL
  BY SpecEIIBPL
  
DeqIdxInv == \A p \in ProcSet : pc[p] = "D2" => (j[p] \in 1..l[p] /\ l[p] \in j[p]..L)

LEMMA SpecDeqIdxInv == Spec => []DeqIdxInv
  <1> SUFFICES ASSUME []TypeOK
               PROVE  Spec => []DeqIdxInv
    BY SpecTypeOK
  <1>1. Init => DeqIdxInv
    BY DEF Init, DeqIdxInv, ImplInit
  <1>2. DeqIdxInv /\ [Next]_vars => DeqIdxInv'
    <2> SUFFICES ASSUME DeqIdxInv,
                        [Next]_vars
                 PROVE  DeqIdxInv'
      OBVIOUS
    <2>1. ASSUME NEW p \in ProcSet,
                 InvocAct(p)
          PROVE  DeqIdxInv'
      <3>1. TypeOK
        BY PTL
      <3> QED
        BY <2>1, <3>1 DEF implvars, DeqIdxInv, InvocAct, LineIDs, OpToFirstLine, OpNames, TypeOK
    <2>2. ASSUME NEW p \in ProcSet,
                 NEW LineAct \in InterLines(p),
                 LineAct
          PROVE  DeqIdxInv'
      <3>1. TypeOK
        BY PTL
      <3>2. CASE E1(p)
        BY <3>1, <3>2 DEF TypeOK, DeqIdxInv, E1
      <3>3. CASE E2(p)
        BY <3>1, <3>3 DEF TypeOK, DeqIdxInv, E2
      <3>4. CASE D1(p)
        BY <3>1, <3>4 DEF TypeOK, DeqIdxInv, D1
      <3>5. CASE D2(p)
        BY <3>1, <3>5 DEF TypeOK, DeqIdxInv, D2
      <3> QED
        BY <2>2, <3>2, <3>3, <3>4, <3>5 DEF InterLines
    <2>3. ASSUME NEW p \in ProcSet,
                 NEW LineAct \in ReturnLines(p),
                 LineAct
          PROVE  DeqIdxInv'
      <3>1. TypeOK
        BY PTL
      <3>2. CASE E3(p)
        BY <3>1, <3>2 DEF TypeOK, DeqIdxInv, E3
      <3>3. CASE D3(p)
        BY <3>1, <3>3 DEF TypeOK, DeqIdxInv, D3
      <3> QED
        BY <2>3, <3>2, <3>3 DEF ReturnLines
    <2>4. CASE UNCHANGED vars
      BY <2>4 DEF vars, DeqIdxInv, implvars
    <2>5. QED
      BY <2>1, <2>2, <2>3, <2>4 DEF InterAct, Next, ReturnAct
  <1> QED
    BY <1>1, <1>2, PTL DEF Spec

-----------------------------------------------------------------------------
(***************************************************************************)
(* Plausibility set definition                                             *)
(***************************************************************************)
\* Q == {c \in ConfigDomain : FALSE}

Val(idx) == 
  IF 
    A[idx] # "BOT" 
  THEN 
    A[idx] 
  ELSE 
    IF 
      (\E q \in ProcSet : pc[q] = "E2" /\ l[q] = idx) 
    THEN 
      LET p == CHOOSE q \in ProcSet : pc[q] = "E2" /\ l[q] = idx IN arg[p]
    ELSE 
      "BOT"

Justified(idxseq) == 
  \A m, n \in 1..Len(idxseq) : m < n => 
    (idxseq[m] < idxseq[n] \/ (A[idxseq[m]] # "BOT" => 
      (\E p \in ProcSet : pc[p] = "D2" /\ idxseq[n] < j[p] /\ idxseq[m] < l[p])))

Q == {c \in ConfigDomain : 
        /\ c.op = [q \in ProcSet |-> PCtoOp(pc[q])]
        /\ c.arg = [q \in ProcSet |-> IF pc[q] = "RM" THEN "BOT" ELSE arg[q]]
        /\ \E idxset \in SUBSET 1..(L-1) :
           /\ \A m \in idxset : Val(m) # "BOT"
           /\ \A m \in 1..(L-1) : A[m] # "BOT" => m \in idxset
           /\ \E idxseq \in Perm(idxset) :
              /\ Justified(idxseq)
              /\ c.state = [i \in 1..Len(idxseq) |-> Val(idxseq[i])]
              /\ \A q \in ProcSet : 
                 /\ pc[q] = "RM" => c.res[q] = "BOT"
                 /\ pc[q] = "E1" => c.res[q] = "BOT"
                 /\ (pc[q] = "E2" /\ l[q] \notin idxset) => c.res[q] = "BOT"
                 /\ (pc[q] = "E2" /\ l[q] \in idxset) => c.res[q] = "ACK"
                 /\ pc[q] = "E3" => c.res[q] = "ACK"
                 /\ pc[q] = "D1" => c.res[q] = "BOT"
                 /\ pc[q] = "D2" => c.res[q] = "BOT"
                 /\ pc[q] = "D3" => c.res[q] = v[q]}

-----------------------------------------------------------------------------
(***************************************************************************)
(* Plausibility set theorem 1: Q is non-empty is an invariant of ASpec.    *)
(***************************************************************************)
THEOREM PlausSetThm1 == ASpec => [](Q # {})

-----------------------------------------------------------------------------
(***************************************************************************)
(* Plausibility set lemma 2.1: Q is initally the same as the singleton P.  *)
(***************************************************************************)
THEOREM PlausSetInitLemma == AInit => Q = P

-----------------------------------------------------------------------------
(***************************************************************************)
(* Plausibility set lemma 2.2: If an invocation action takes place, then   *)
(* the new plausibility set Q' is a subset of the evolution of             *)
(* Invoke(Q, p, PCtoOp(pc'[p]), arg'[p]).                                  *)
(***************************************************************************)
(* Note that PCtoOp(pc'[p]) is the operation being invoked by p, and       *)
(* arg'[p] is the argument that was picked for the invocation.             *)
(***************************************************************************)
InvocProperty == 
  \A p \in ProcSet : InvocAct(p) => (Q' \in SUBSET Evolve(Invoke(Q, p, PCtoOp(pc'[p]), arg'[p])))

THEOREM InvocLemma == ASpec => [][InvocProperty]_varsP

-----------------------------------------------------------------------------
(***************************************************************************)
(* Plausibility set lemma 2.3: If an intermediate-line action takes place, *)
(* then the new plausibility set Q' is a subset of the evolution of Q.     *)
(***************************************************************************)
InterProperty == \A p \in ProcSet : InterAct(p) => (Q' \in SUBSET Evolve(Q))

THEOREM InterLemma == ASpec => [][InterProperty]_varsP

-----------------------------------------------------------------------------
(***************************************************************************)
(* Plausibility set lemma 2.4: If an intermediate-line action takes place, *)
(* then the new plausibility set Q' is a subset of the filtering of the    *)
(* evolution of Q, where the filtering is done for process p and the value *)
(* ret'[p] (which is the value to be returned by p).                       *)
(***************************************************************************)
ReturnProperty ==
  \A p \in ProcSet : ReturnAct(p) => (Q' \in SUBSET Filter(Evolve(Q), p, ret'[p]))

THEOREM ReturnLemma == ASpec => [][ReturnProperty]_varsP

-----------------------------------------------------------------------------
(***************************************************************************)
(* Plausibility set lemma 2.5: If no variable changes, Q remains the same. *)
(***************************************************************************)
THEOREM UnchangedLemma == UNCHANGED varsP => Q' = Q

-----------------------------------------------------------------------------
(***************************************************************************)
(* Plausibility set theorem 2: Q is a subset of P is an invariant of ASpec.*)
(***************************************************************************)
(* This theorem follows automatically from the five lemmas above.          *)
(***************************************************************************)
THEOREM PlausSetThm2 == ASpec => [](Q \in SUBSET P)
  <1> SUFFICES ASSUME [][InvocProperty]_varsP,
                      [][InterProperty]_varsP,
                      [][ReturnProperty]_varsP
               PROVE  ASpec => [](Q \in SUBSET P)
    BY InvocLemma, InterLemma, ReturnLemma
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
        BY <2>2, Zenon, EvolveForSubset
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
