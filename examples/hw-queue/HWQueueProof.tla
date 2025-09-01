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

Val(idx) == 
  IF 
    A[idx] # "BOT" 
  THEN 
    A[idx] 
  ELSE 
    IF 
      (\E q \in ProcSet : pc[q] = "E2" /\ l[q] = idx) 
    THEN 
      LET p == CHOOSE q \in ProcSet : pc[q] = "E2" /\ l[q] = idx IN arg[p].val
    ELSE 
      "BOT"

Justified(idxseq) == 
  \A m, n \in 1..Len(idxseq) : m < n => 
    (idxseq[m] < idxseq[n] \/ (A[idxseq[n]] # "BOT" => 
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

(* Helper lemma: TypeOK and EnqIdxInv suffice to show Q is non-empty *)
LEMMA TypeOKEIIImpliesQNE == TypeOK /\ EnqIdxInv => Q # {}
  <1> SUFFICES ASSUME TypeOK, EnqIdxInv
               PROVE  Q # {}
    OBVIOUS
  <1> DEFINE cop == [p \in ProcSet |-> PCtoOp(pc[p])]
  <1>1. cop \in [ProcSet -> OpDomain]
    BY DEF TypeOK, LineIDs, PCtoOp, OpNames, OpDomain
  <1> DEFINE carg == [p \in ProcSet |-> IF pc[p] = "RM" THEN "BOT" ELSE arg[p]]
  <1>2. carg \in [ProcSet -> ArgDomain]
    BY Zenon DEF ArgDomain, TypeOK, ArgsOf, PCtoOp
  <1> DEFINE cres == [p \in ProcSet |-> CASE pc[p] = "E3" -> "ACK"
                                          [] pc[p] = "D3" -> v[p]
                                          [] OTHER -> "BOT"]
  <1>3. cres \in [ProcSet -> ResDomain]
    BY DEF ResDomain, RetDomain, TypeOK, RetsOf, OpNames
  <1> DEFINE full_indices == {i \in 1..(L-1) : A[i] # "BOT"}
  <1>4. /\ \A m \in full_indices : Val(m) # "BOT"
        /\ \A m \in 1..(L-1) : A[m] # "BOT" => m \in full_indices
        /\ full_indices \in SUBSET 1..(L-1)
    BY DEF Val
  <1>5. IsFiniteSet(full_indices) 
    BY FS_Interval, FS_Subset DEF TypeOK
  <1>6. full_indices \in SUBSET Int
    BY DEF TypeOK
  <1>7. PICK pi \in Perm(full_indices) : \A m, n \in 1..Len(pi) : 
      m < n => pi[m] < pi[n]
    BY <1>5, <1>6, SortedPermutationOfIntegerSet
  <1>8. Justified(pi)
    BY <1>7 DEF Justified
  <1> DEFINE cstate == [i \in 1..Len(pi) |-> Val(pi[i])]
  <1>9. cstate \in StateDomain
    BY DEF StateDomain, Perm, TypeOK, Val
  <1> DEFINE c == [state |-> cstate, op |-> cop, arg |-> carg, res |-> cres]
  <1>10. c \in ConfigDomain
    BY <1>1, <1>2, <1>3, <1>9 DEF ConfigDomain
  <1> SUFFICES \E idxset \in SUBSET 1..(L-1) :
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
                     /\ pc[q] = "D3" => c.res[q] = v[q]
    BY <1>10 DEF Q
  <1> SUFFICES \E idxseq \in Perm(full_indices) :
                  /\ Justified(idxseq)
                  /\ c.state = [i \in 1..Len(idxseq) |-> Val(idxseq[i])]
                  /\ \A q \in ProcSet : 
                     /\ pc[q] = "RM" => c.res[q] = "BOT"
                     /\ pc[q] = "E1" => c.res[q] = "BOT"
                     /\ (pc[q] = "E2" /\ l[q] \notin full_indices) => c.res[q] = "BOT"
                     /\ (pc[q] = "E2" /\ l[q] \in full_indices) => c.res[q] = "ACK"
                     /\ pc[q] = "E3" => c.res[q] = "ACK"
                     /\ pc[q] = "D1" => c.res[q] = "BOT"
                     /\ pc[q] = "D2" => c.res[q] = "BOT"
                     /\ pc[q] = "D3" => c.res[q] = v[q]
    BY <1>4
  <1>11. ASSUME NEW q \in ProcSet 
         PROVE  /\ pc[q] = "RM" => c.res[q] = "BOT"
                /\ pc[q] = "E1" => c.res[q] = "BOT"
                /\ (pc[q] = "E2" /\ l[q] \notin full_indices) => c.res[q] = "BOT"
                /\ (pc[q] = "E2" /\ l[q] \in full_indices) => c.res[q] = "ACK"
                /\ pc[q] = "E3" => c.res[q] = "ACK"
                /\ pc[q] = "D1" => c.res[q] = "BOT"
                /\ pc[q] = "D2" => c.res[q] = "BOT"
                /\ pc[q] = "D3" => c.res[q] = v[q]
    BY DEF EnqIdxInv (* Invariant ensures l[q] \in full_indices does not hold when pc[q] = "E2" *)
  <1> QED
    BY <1>7, <1>8, <1>11

THEOREM PlausSetThm1 == ASpec => [](Q # {})
  <1> SUFFICES Spec => [](Q # {})
    BY ASpecImpliesSpec
  <1> SUFFICES Spec => [](TypeOK /\ EnqIdxInv)
    BY TypeOKEIIImpliesQNE, PTL
  <1> QED
    BY SpecTypeOK, SpecEnqIdxInv, PTL

-----------------------------------------------------------------------------
(***************************************************************************)
(* Plausibility set lemma 2.1: Q is initally the same as the singleton P.  *)
(***************************************************************************)
THEOREM PlausSetInitLemma == AInit => Q = P
  <1> SUFFICES ASSUME AInit
               PROVE  Q = P
    OBVIOUS
  <1>1. TypeOK /\ EnqIdxInv
    <2>1. <<>> \in Seq(EltDomain)
      OBVIOUS
    <2> QED
      BY <2>1 DEF AInit, Init, ImplInit, InitState, TypeOK, LineIDs, StateDomain, ArgDomain, EnqIdxInv
  <1>2. Q # {}
    BY <1>1, TypeOKEIIImpliesQNE
  <1>3. Q \in SUBSET ConfigDomain
    BY DEF Q
  <1> SUFFICES \A c \in Q :
      c = [state |-> InitState, 
           op    |-> [p \in ProcSet |-> "BOT"], 
           arg   |-> [p \in ProcSet |-> "BOT"], 
           res   |-> [p \in ProcSet |-> "BOT"]]
    BY <1>2, Zenon DEF AInit
  <1> SUFFICES ASSUME NEW c \in ConfigDomain,
                      c \in Q
               PROVE  /\ c.state = InitState
                      /\ c.op = [p \in ProcSet |-> "BOT"]
                      /\ c.arg = [p \in ProcSet |-> "BOT"]
                      /\ c.res = [p \in ProcSet |-> "BOT"]
    BY <1>3 DEF ConfigDomain
  <1>4. c.op = [p \in ProcSet |-> "BOT"]
    BY DEF Q, PCtoOp, AInit, Init
  <1>5. c.arg = [p \in ProcSet |-> "BOT"]
    BY DEF Q, AInit, Init
  <1>6. c.res = [p \in ProcSet |-> "BOT"]
    BY DEF Q, ConfigDomain, AInit, Init
  <1> SUFFICES c.state = InitState
    BY <1>4, <1>5, <1>6
  <1>7. PICK idxset \in SUBSET 1..(L-1) :
        /\ \A m \in idxset : Val(m) # "BOT"
        /\ \A m \in 1..(L-1) : A[m] # "BOT" => m \in idxset
        /\ \E idxseq \in Perm(idxset) :
           /\ Justified(idxseq)
           /\ c.state = [i \in 1..Len(idxseq) |-> Val(idxseq[i])]
    BY DEF Q
  <1>8. PICK idxseq \in Perm(idxset) :
        /\ Justified(idxseq)
        /\ c.state = [i \in 1..Len(idxseq) |-> Val(idxseq[i])]
    BY <1>7
  <1>9. \A m \in 1..(L-1) : A[m] # "BOT" 
    <2>1. <<>> \in Seq(EltDomain)
      OBVIOUS
    <2> QED
      BY <2>1, BotNotElt DEF AInit, Init, ImplInit, InitState, StateDomain
  <1>10. idxset = 1..(L-1)
    BY <1>7, <1>9
  <1>11. ~(\E p \in ProcSet : pc[p] = "D2")
    BY DEF AInit, Init
  <1>12. \A m, n \in 1..Len(idxseq) : m < n => idxseq[m] < idxseq[n]
    BY <1>8, <1>9, <1>11 DEF Justified, Perm
  (* Here onward, proof shows idxseq is the identity permutation *)
  <1>13. Len(idxseq) = Cardinality(1..(L-1))
    BY <1>8, <1>10 DEF Perm
  <1>14. Cardinality(1..(L-1)) = L-1
    BY FS_Interval, <1>1 DEF TypeOK
  <1>15. <<>> \in Seq(EltDomain)
    OBVIOUS
  <1>16. Len(idxseq) = Len(InitState)
    BY <1>1, <1>13, <1>14, <1>15 DEF TypeOK, AInit, Init, ImplInit, InitState, StateDomain
  <1>17. c.state = [i \in 1..Len(idxseq) |-> A[idxseq[i]]]
    BY <1>8, <1>9 DEF Val, Perm
  <1>18. c.state = [i \in 1..Len(InitState) |-> A[idxseq[i]]]
    BY <1>16, <1>17
  <1> SUFFICES \A i \in 1..Len(idxseq) : idxseq[i] = i
    BY <1>16, <1>18, <1>15 DEF AInit, Init, ImplInit, InitState, StateDomain
  <1> DEFINE R(k) == k <= Len(idxseq) => \A i \in 1..k : idxseq[i] = i
  <1> SUFFICES ASSUME Len(idxseq) > 0 
               PROVE  R(Len(idxseq))
    BY DEF Perm
  <1> DEFINE R2(k) == R(k+1)
  <1> SUFFICES R2(Len(idxseq)-1)
    BY DEF Perm
  <1> SUFFICES \A k \in Nat : R2(k)
    BY DEF Perm
  <1> SUFFICES R2(0) /\ \A n \in Nat : R2(n) => R2(n+1)
    BY NatInduction, Isa
  <1>19. R2(0)
    <2> SUFFICES idxseq[1] = 1
      BY DEF Perm
    <2> SUFFICES ASSUME idxseq[1] # 1
                 PROVE  FALSE
      OBVIOUS
    <2>1. 1 \in idxset
      BY <1>13, <1>14, <1>1, <1>10 DEF TypeOK
    <2>2. PICK z \in 1..Len(idxseq) : idxseq[z] = 1
      BY PermutationIndex, <2>1
    <2>3. idxseq[z-1] < idxseq[z]
      BY <1>12, <2>2 DEF Perm
    <2>4. idxseq[z-1] < 1
      BY <2>2, <2>3 DEF Perm
    <2> QED
      BY <2>4, <2>2, <1>10 DEF Perm
  <1>20. \A n \in Nat : R2(n) => R2(n+1)
    <2> SUFFICES ASSUME NEW n \in Nat,
                        R2(n)
                 PROVE  R2(n+1)
      OBVIOUS
    <2> SUFFICES ASSUME R(n+1)
                 PROVE  R(n+2)
      OBVIOUS
    <2> DEFINE m == n+1
    <2> m \in Nat \ {0}
      OBVIOUS
    <2> SUFFICES ASSUME R(m)
                 PROVE  R(m+1)
      OBVIOUS
    <2> HIDE DEF m, R2
    <2> SUFFICES ASSUME m+1 <= Len(idxseq),
                        NEW i \in 1..(m+1)
                 PROVE  idxseq[i] = i
      OBVIOUS
    <2>1. CASE i \in 1..m
      BY <2>1 DEF Perm
    <2> SUFFICES idxseq[m+1] = m+1
      BY <2>1 DEF Perm
    <2> SUFFICES ASSUME idxseq[m+1] # m+1
                 PROVE  FALSE
      OBVIOUS
    <2>2. m+1 \in idxset
      BY <1>13, <1>14, <1>10
    <2>3. PICK z \in 1..Len(idxseq) : idxseq[z] = m+1
      BY PermutationIndex, <2>2
    <2>4. z # m+1
      BY <2>3
    <2>5. ~(z < m+1)
      BY <2>3 DEF Perm
    <2>6. m+1 < z
      BY <2>4, <2>5
    <2>7. idxseq[m+1] < idxseq[z]
      BY <1>12, <2>6 DEF Perm
    <2>8. idxseq[m+1] > m+1
      <3> SUFFICES ASSUME idxseq[m+1] \in 1..m
                   PROVE  FALSE
        BY DEF Perm
      <3>1. idxseq[m] = m /\ idxseq[m+1] \in 1..m
        BY DEF Perm
      <3> QED
        BY <1>12, <3>1 DEF Perm
    <2> QED
      BY <2>3, <2>7, <2>8, <1>12 DEF Perm
  <1> HIDE DEF R2
  <1> QED
    BY <1>19, <1>20

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
  <1> SUFFICES ASSUME []TypeOK
               PROVE  ASpec => [][InvocProperty]_varsP
    BY ASpecImpliesSpec, SpecTypeOK
  <1>1. TypeOK
    BY PTL
  <1> SUFFICES ASSUME ANext
               PROVE  InvocProperty
    BY PTL DEF ASpec
  <1> SUFFICES ASSUME NEW p \in ProcSet,
                      InvocAct(p)
               PROVE  Q' \in SUBSET Evolve(Invoke(Q, p, PCtoOp(pc'[p]), arg'[p]))
    BY DEF InvocProperty
  <1> SUFFICES ASSUME NEW c \in ConfigDomain,
                      c \in Q'
               PROVE  c \in Evolve(Invoke(Q, p, PCtoOp(pc'[p]), arg'[p]))
    BY Zenon DEF Q
  <1>2. Q \in SUBSET ConfigDomain
    BY Zenon DEF Q
  <1>3. c.op[p] = PCtoOp(pc'[p])
    BY DEF Q
  <1>4. c.arg[p] = arg'[p]
    <2> SUFFICES pc'[p] # "RM"
      BY DEF Q
    <2>1. TypeOK
      BY PTL
    <2> QED
      BY <2>1 DEF InvocAct, OpToFirstLine, OpNames, TypeOK
  <1>5. c.res[p] = "BOT"
    <2> SUFFICES pc'[p] = "E1" \/ pc'[p] = "D1"
      BY DEF Q
    <2>1. TypeOK
      BY PTL
    <2> QED
      BY <2>1 DEF Q, InvocAct, OpToFirstLine, OpNames, TypeOK
  <1> DEFINE c_prev == [c EXCEPT !.op = [c.op EXCEPT ![p] = "BOT"],
                                 !.arg = [c.arg EXCEPT ![p] = "BOT"]]
  <1> SUFFICES c_prev \in Q
    BY <1>2, <1>3, <1>4, <1>5, InvokeAndEvolveFromUninvoked
  <1>6. c_prev \in ConfigDomain
    BY DEF ConfigDomain, OpDomain, ArgDomain
  <1>7. c_prev.op = [q \in ProcSet |-> PCtoOp(pc[q])]
    <2>1. PCtoOp(pc[p]) = "BOT"
      BY DEF InvocAct, PCtoOp
    <2> SUFFICES ASSUME NEW q \in ProcSet,
                        q # p
                 PROVE  c_prev.op[q] = PCtoOp(pc[q])
      BY <2>1 DEF ConfigDomain
    <2>2. c_prev.op[q] = PCtoOp(pc'[q])
      BY DEF Q, ConfigDomain
    <2> SUFFICES pc'[q] = pc[q]
      BY <2>2
    <2>3. TypeOK
      BY PTL
    <2> QED
      BY <2>3 DEF InvocAct, TypeOK
  <1>8. c_prev.arg = [q \in ProcSet |-> IF pc[q] = "RM" THEN "BOT" ELSE arg[q]]
    <2>1. pc[p] = "RM"
      BY DEF InvocAct
    <2> SUFFICES ASSUME NEW q \in ProcSet,
                        q # p
                 PROVE  c_prev.arg[q] = IF pc[q] = "RM" THEN "BOT" ELSE arg[q]
      BY <2>1 DEF ConfigDomain
    <2>2. c_prev.arg[q] = IF pc'[q] = "RM" THEN "BOT" ELSE arg'[q]
      BY DEF Q, ConfigDomain
    <2> SUFFICES pc'[q] = pc[q] /\ arg'[q] = arg[q]
      BY <2>2
    <2>3. TypeOK
      BY PTL
    <2> QED
      BY <2>3 DEF InvocAct, TypeOK
  <1> SUFFICES \E idxset \in SUBSET 1..(L-1) :
               /\ \A m \in idxset : Val(m) # "BOT"
               /\ \A m \in 1..(L-1) : A[m] # "BOT" => m \in idxset
               /\ \E idxseq \in Perm(idxset) :
                  /\ Justified(idxseq)
                  /\ c_prev.state = [i \in 1..Len(idxseq) |-> Val(idxseq[i])]
                  /\ \A q \in ProcSet : 
                     /\ pc[q] = "RM" => c_prev.res[q] = "BOT"
                     /\ pc[q] = "E1" => c_prev.res[q] = "BOT"
                     /\ (pc[q] = "E2" /\ l[q] \notin idxset) => c_prev.res[q] = "BOT"
                     /\ (pc[q] = "E2" /\ l[q] \in idxset) => c_prev.res[q] = "ACK"
                     /\ pc[q] = "E3" => c_prev.res[q] = "ACK"
                     /\ pc[q] = "D1" => c_prev.res[q] = "BOT"
                     /\ pc[q] = "D2" => c_prev.res[q] = "BOT"
                     /\ pc[q] = "D3" => c_prev.res[q] = v[q]
    BY <1>6, <1>7, <1>8 DEF Q
  <1>9. PICK idxset \in SUBSET 1..(L-1) :
        /\ \A m \in idxset : Val(m)' # "BOT"
        /\ \A m \in 1..(L-1) : A[m] # "BOT" => m \in idxset
        /\ \E idxseq \in Perm(idxset) :
           /\ Justified(idxseq)'
           /\ c.state = [i \in 1..Len(idxseq) |-> Val(idxseq[i])']
           /\ \A q \in ProcSet : 
              /\ pc'[q] = "RM" => c.res[q] = "BOT"
              /\ pc'[q] = "E1" => c.res[q] = "BOT"
              /\ (pc'[q] = "E2" /\ l[q] \notin idxset) => c.res[q] = "BOT"
              /\ (pc'[q] = "E2" /\ l[q] \in idxset) => c.res[q] = "ACK"
              /\ pc'[q] = "E3" => c.res[q] = "ACK"
              /\ pc'[q] = "D1" => c.res[q] = "BOT"
              /\ pc'[q] = "D2" => c.res[q] = "BOT"
              /\ pc'[q] = "D3" => c.res[q] = v'[q]
    BY DEF Q, InvocAct, implvars, Val
  <1>10. PICK idxseq \in Perm(idxset) :
         /\ Justified(idxseq)'
         /\ c.state = [i \in 1..Len(idxseq) |-> Val(idxseq[i])']
         /\ \A q \in ProcSet : 
            /\ pc'[q] = "RM" => c.res[q] = "BOT"
            /\ pc'[q] = "E1" => c.res[q] = "BOT"
            /\ (pc'[q] = "E2" /\ l[q] \notin idxset) => c.res[q] = "BOT"
            /\ (pc'[q] = "E2" /\ l[q] \in idxset) => c.res[q] = "ACK"
            /\ pc'[q] = "E3" => c.res[q] = "ACK"
            /\ pc'[q] = "D1" => c.res[q] = "BOT"
            /\ pc'[q] = "D2" => c.res[q] = "BOT"
            /\ pc'[q] = "D3" => c.res[q] = v'[q]
    BY <1>9
  <1> SUFFICES /\ \A m \in idxset : Val(m) # "BOT"
               /\ \A m \in 1..(L-1) : A[m] # "BOT" => m \in idxset
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
                  /\ pc[q] = "D3" => c.res[q] = v[q]
    BY <1>9, <1>10 DEF ConfigDomain
  <1>11. \A m \in idxset : Val(m) # "BOT"
    <2> SUFFICES ASSUME NEW m \in idxset
                 PROVE  Val(m) # "BOT"
      OBVIOUS
    <2>1. Val(m)' # "BOT"
      BY <1>9
    <2>2. CASE A'[m] # "BOT"
      BY <2>2 DEF Val, implvars, InvocAct
    <2> SUFFICES ASSUME A'[m] = "BOT",
                        \E r \in ProcSet : pc'[r] = "E2" /\ l'[r] = m,
                        NEW q, q = CHOOSE r \in ProcSet : pc'[r] = "E2" /\ l'[r] = m,
                        Val(m)' = arg'[q].val
                 PROVE  Val(m) # "BOT"
      BY <2>1, <2>2 DEF Val
    <2>3. A[m] = "BOT"
      BY DEF implvars, InvocAct
    <2>4. q \in ProcSet /\ pc[q] = "E2" /\ l[q] = m
      BY <1>1 DEF implvars, InvocAct, TypeOK, OpToFirstLine, OpNames
    <2>5. \A r \in ProcSet : (pc'[r] = "E2" /\ l'[r] = m) <=> (pc[r] = "E2" /\ l[r] = m)
      BY <1>1 DEF implvars, InvocAct, TypeOK, OpToFirstLine, OpNames
    <2>6. q = CHOOSE r \in ProcSet : pc[r] = "E2" /\ l[r] = m
      BY <2>5, Zenon
    <2>7. Val(m) = arg[q].val
      BY <2>3, <2>4, <2>6 DEF Val
    <2>8. arg[q].val \in EltDomain
      BY <1>1, <2>4 DEF TypeOK, ArgsOf, PCtoOp
    <2> QED
      BY <2>7, <2>8, BotNotElt
  <1>12. \A m \in 1..(L-1) : A[m] # "BOT" => m \in idxset
    BY <1>9
  <1>13. Justified(idxseq)
    BY <1>1, <1>10 DEF Justified, implvars, InvocAct, TypeOK, OpToFirstLine, OpNames
  <1>14. c.state = [i \in 1..Len(idxseq) |-> Val(idxseq[i])]
    <2> SUFFICES ASSUME NEW i \in 1..Len(idxseq)
                 PROVE  Val(idxseq[i])' = Val(idxseq[i])
      BY <1>10
    <2>1. CASE A'[idxseq[i]] # "BOT"
      BY <2>1 DEF Val, implvars, InvocAct
    <2>2. CASE A'[idxseq[i]] = "BOT"
      <3>1. CASE (\E r \in ProcSet : pc'[r] = "E2" /\ l'[r] = idxseq[i])
        <4>1. \A r \in ProcSet : (pc'[r] = "E2" /\ l'[r] = idxseq[i]) <=> (pc[r] = "E2" /\ l[r] = idxseq[i])
          BY <1>1 DEF implvars, InvocAct, TypeOK, OpToFirstLine, OpNames
        <4> DEFINE q == CHOOSE r \in ProcSet : pc'[r] = "E2" /\ l'[r] = idxseq[i]
        <4>2. q \in ProcSet /\ pc'[q] = "E2" /\ l'[q] = idxseq[i]
          BY <2>2, <3>1 DEF Val
        <4>3. q = CHOOSE r \in ProcSet : pc[r] = "E2" /\ l[r] = idxseq[i]
          BY <4>1, <4>2, Zenon
        <4>4. A[idxseq[i]] = "BOT"
          BY <2>2 DEF implvars, InvocAct
        <4>5. \E r \in ProcSet : pc[r] = "E2" /\ l[r] = idxseq[i]
          BY <3>1, <4>1
        <4>6. Val(idxseq[i]) = arg[q].val
          BY <4>3, <4>4, <4>5 DEF Val
        <4>7. Val(idxseq[i])' = arg'[q].val
          BY <2>2, <3>1 DEF Val
        <4>8. q # p
          BY <4>2, <4>1 DEF InvocAct
        <4>9. PICK newarg : arg' = [arg EXCEPT ![p] = newarg] 
          BY DEF InvocAct
        <4>10. TypeOK'
          BY PTL
        <4> HIDE DEF q
        <4>11. arg'[q] = arg[q]
          BY <4>2, <4>8, <4>9, <4>10 DEF TypeOK
        <4> QED
          BY <4>6, <4>7, <4>11
      <3>2. CASE ~(\E r \in ProcSet : pc'[r] = "E2" /\ l'[r] = idxseq[i])
        <4>1. Val(idxseq[i])' = "BOT"
          BY <2>2, <3>2 DEF Val
        <4>2. A[idxseq[i]] = "BOT"
          BY <2>2 DEF implvars, InvocAct
        <4>3. \A r \in ProcSet : (pc'[r] = "E2" /\ l'[r] = idxseq[i]) <=> (pc[r] = "E2" /\ l[r] = idxseq[i])
          BY <1>1 DEF implvars, InvocAct, TypeOK, OpToFirstLine, OpNames
        <4>4. ~(\E r \in ProcSet : pc[r] = "E2" /\ l[r] = idxseq[i])
          BY <3>2, <4>3
        <4>5. Val(idxseq[i]) = "BOT"
          BY <4>2, <4>4 DEF Val
        <4> QED
          BY <4>5, <4>1
      <3> QED
        BY <3>1, <3>2
    <2> QED
      BY <2>1, <2>2
  <1>15. \A q \in ProcSet : 
         /\ pc[q] = "RM" => c.res[q] = "BOT"
         /\ pc[q] = "E1" => c.res[q] = "BOT"
         /\ (pc[q] = "E2" /\ l[q] \notin idxset) => c.res[q] = "BOT"
         /\ (pc[q] = "E2" /\ l[q] \in idxset) => c.res[q] = "ACK"
         /\ pc[q] = "E3" => c.res[q] = "ACK"
         /\ pc[q] = "D1" => c.res[q] = "BOT"
         /\ pc[q] = "D2" => c.res[q] = "BOT"
         /\ pc[q] = "D3" => c.res[q] = v[q]
    BY <1>10, <1>1 DEF TypeOK, implvars, InvocAct, OpToFirstLine, OpNames
  <1> QED
    BY <1>11, <1>12, <1>13, <1>14, <1>15

-----------------------------------------------------------------------------
(***************************************************************************)
(* Plausibility set lemma 2.3: If an intermediate-line action takes place, *)
(* then the new plausibility set Q' is a subset of the evolution of Q.     *)
(***************************************************************************)
InterProperty == \A p \in ProcSet : InterAct(p) => (Q' \in SUBSET Evolve(Q))

THEOREM InterLemma == ASpec => [][InterProperty]_varsP
  <1> SUFFICES ASSUME []TypeOK, []FinActive, []BotPastL, []EnqIdxInv, []DeqIdxInv
               PROVE  ASpec => [][InterProperty]_varsP
    BY ASpecImpliesSpec, SpecTypeOK, SpecFinActive, SpecBotPastL, SpecEnqIdxInv, SpecDeqIdxInv
  <1> SUFFICES ASSUME ANext
               PROVE  InterProperty
    BY PTL DEF ASpec
  <1> SUFFICES ASSUME NEW p \in ProcSet,
                      InterAct(p)
               PROVE  Q' \in SUBSET Evolve(Q)
    BY DEF InterProperty
  <1>1. ASSUME E1(p),
               NEW c \in ConfigDomain,
               c \in Q'
        PROVE  c \in Evolve(Q)
  <1>2. ASSUME E2(p),
               NEW c \in ConfigDomain,
               c \in Q'
        PROVE  c \in Evolve(Q)
    <2> USE <1>2
    <2> SUFFICES c \in Q
      BY EmptySeqEvolve DEF Q
    <2>1. TypeOK
      BY PTL
    <2>2. c.op = [q \in ProcSet |-> PCtoOp(pc[q])]
      <3>1. c.op = [q \in ProcSet |-> PCtoOp(pc'[q])]
        BY DEF Q
      <3>2. PCtoOp(pc'[p]) = PCtoOp(pc[p])
        BY <2>1 DEF E2, PCtoOp, TypeOK
      <3> SUFFICES ASSUME NEW q \in ProcSet, q # p
                   PROVE  pc'[q] = pc[q]
        BY <3>1, <3>2
      <3> QED
        BY <2>1 DEF E2, TypeOK
    <2>3. c.arg = [q \in ProcSet |-> IF pc[q] = "RM" THEN "BOT" ELSE arg[q]]
      <3>1. c.arg = [q \in ProcSet |-> IF pc'[q] = "RM" THEN "BOT" ELSE arg'[q]]
        BY DEF Q
      <3> SUFFICES pc'[p] # "RM" /\ pc[p] # "RM"
        BY <3>1, <2>1 DEF E2, TypeOK
      <3> QED
        BY <2>1 DEF E2, TypeOK
    <2> SUFFICES \E idxset \in SUBSET 1..(L-1) :
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
              /\ pc[q] = "D3" => c.res[q] = v[q]
      BY <2>2, <2>3 DEF Q
    <2>4. PICK idxset \in SUBSET 1..(L-1) :
          /\ \A m \in idxset : Val(m)' # "BOT"
          /\ \A m \in 1..(L-1) : A'[m] # "BOT" => m \in idxset
          /\ \E idxseq \in Perm(idxset) :
             /\ Justified(idxseq)'
             /\ c.state = [i \in 1..Len(idxseq) |-> Val(idxseq[i])']
             /\ \A q \in ProcSet : 
                /\ pc'[q] = "RM" => c.res[q] = "BOT"
                /\ pc'[q] = "E1" => c.res[q] = "BOT"
                /\ (pc'[q] = "E2" /\ l[q] \notin idxset) => c.res[q] = "BOT"
                /\ (pc'[q] = "E2" /\ l[q] \in idxset) => c.res[q] = "ACK"
                /\ pc'[q] = "E3" => c.res[q] = "ACK"
                /\ pc'[q] = "D1" => c.res[q] = "BOT"
                /\ pc'[q] = "D2" => c.res[q] = "BOT"
                /\ pc'[q] = "D3" => c.res[q] = v[q]
      BY DEF Q, E2
    <2>5. PICK idxseq \in Perm(idxset) :
          /\ Justified(idxseq)'
          /\ c.state = [i \in 1..Len(idxseq) |-> Val(idxseq[i])']
          /\ \A q \in ProcSet : 
              /\ pc'[q] = "RM" => c.res[q] = "BOT"
              /\ pc'[q] = "E1" => c.res[q] = "BOT"
              /\ (pc'[q] = "E2" /\ l[q] \notin idxset) => c.res[q] = "BOT"
              /\ (pc'[q] = "E2" /\ l[q] \in idxset) => c.res[q] = "ACK"
              /\ pc'[q] = "E3" => c.res[q] = "ACK"
              /\ pc'[q] = "D1" => c.res[q] = "BOT"
              /\ pc'[q] = "D2" => c.res[q] = "BOT"
              /\ pc'[q] = "D3" => c.res[q] = v[q]
      BY <2>4
    <2>6. \A m \in idxset : Val(m) # "BOT"
      <3> SUFFICES ASSUME NEW m \in idxset
                   PROVE  Val(m) # "BOT"
        OBVIOUS
      <3>1. Val(m)' # "BOT"
        BY <2>4
      <3>2. CASE A'[m] # "BOT"
        <4> SUFFICES ASSUME A'[m] # A[m], A[m] = "BOT"
                     PROVE  Val(m) # "BOT"
          BY <3>1, <3>2 DEF Val
        <4>1. pc[p] = "E2" /\ l[p] = m
          BY <2>1, <3>2 DEF E2, TypeOK
        <4>2. EnqIdxInv
          BY PTL
        <4>3. \A r \in ProcSet : (pc[r] = "E2" /\ l[r] = l[p]) <=> r = p
          BY <4>2, <4>1 DEF EnqIdxInv
        <4>4. Val(m) = arg[p].val
          BY <4>1, <4>3 DEF Val
        <4>5. arg[p].val \in EltDomain
          BY <2>1, <4>1 DEF TypeOK, ArgsOf, PCtoOp
        <4> QED
          BY <4>4, <4>5, BotNotElt
      <3>3. CASE A'[m] = "BOT" /\ (\E q \in ProcSet : pc'[q] = "E2" /\ l'[q] = m)
        <4> DEFINE r == CHOOSE q \in ProcSet : pc'[q] = "E2" /\ l'[q] = m
        <4>1. r \in ProcSet /\ pc'[r] = "E2" /\ l'[r] = m
          BY <3>3 DEF Val
        <4>2. r # p
          BY <2>1, <4>1 DEF E2, TypeOK
        <4>3. pc[r] = "E2" /\ l[r] = m
          BY <2>1, <4>1 DEF E2, TypeOK
        <4>4. EnqIdxInv
          BY PTL
        <4>5. A[l[r]] = "BOT"
          BY <2>1, <4>1, <4>3, <4>4 DEF EnqIdxInv
        <4>6. \A q \in ProcSet : (pc[q] = "E2" /\ l[q] = l[r]) <=> q = r
          BY <4>4, <4>3, <4>1 DEF EnqIdxInv
        <4>7. Val(m) = arg[r].val
          BY <4>1, <4>3, <4>5, <4>6 DEF Val
        <4>8. arg[r].val \in EltDomain
          BY <2>1, <4>1, <4>3 DEF TypeOK, ArgsOf, PCtoOp
        <4> QED
          BY <4>7, <4>8, BotNotElt
      <3> QED
        BY <3>1, <3>2, <3>3 DEF Val
    <2>7. \A m \in 1..(L-1) : A[m] # "BOT" => m \in idxset
      <3> SUFFICES ASSUME NEW m \in 1..(L-1), A[m] # "BOT"
                   PROVE  m \in idxset
        OBVIOUS
      <3>1. A'[m] # "BOT" => m \in idxset
        BY <2>4
      <3> SUFFICES ASSUME m = l[p]
                   PROVE  A'[m] # "BOT"
        BY <3>1, <2>1 DEF E2, TypeOK
      <3>2. A'[l[p]] # "BOT"
        BY <2>1, BotNotElt DEF E2, TypeOK, ArgsOf, PCtoOp
      <3> QED
        BY <3>2            
    <2> SUFFICES /\ Justified(idxseq)
                 /\ c.state = [i \in 1..Len(idxseq) |-> Val(idxseq[i])]
                 /\ \A q \in ProcSet : 
                    /\ pc[q] = "RM" => c.res[q] = "BOT"
                    /\ pc[q] = "E1" => c.res[q] = "BOT"
                    /\ (pc[q] = "E2" /\ l[q] \notin idxset) => c.res[q] = "BOT"
                    /\ (pc[q] = "E2" /\ l[q] \in idxset) => c.res[q] = "ACK"
                    /\ pc[q] = "E3" => c.res[q] = "ACK"
                    /\ pc[q] = "D1" => c.res[q] = "BOT"
                    /\ pc[q] = "D2" => c.res[q] = "BOT"
                    /\ pc[q] = "D3" => c.res[q] = v[q]
      BY <2>6, <2>7
    <2>8. Justified(idxseq)
      <3> SUFFICES ASSUME NEW m \in 1..Len(idxseq),
                          NEW n \in 1..Len(idxseq),
                          m < n
                   PROVE  \/ idxseq[m] < idxseq[n]
                          \/ A[idxseq[n]] # "BOT" => (\E r \in ProcSet : pc[r] = "D2" /\ idxseq[n] < j[r] /\ idxseq[m] < l[r])
        BY DEF Justified
      <3>1. idxseq[m] \in idxset /\ idxseq[n] \in idxset
        BY DEF Perm
      <3>2. idxseq[m] \in 1..(L-1) /\ idxseq[n] \in 1..(L-1)
        BY <3>1 
      <3> SUFFICES ASSUME (idxseq[m] > idxseq[n]), A[idxseq[n]] # "BOT"
                   PROVE  \E r \in ProcSet : pc[r] = "D2" /\ idxseq[n] < j[r] /\ idxseq[m] < l[r]
        BY <2>5, <3>2 DEF Perm
      <3>3. EnqIdxInv
        BY PTL
      <3>4. idxseq[n] # l[p]
        BY <3>3 DEF EnqIdxInv, E2
      <3>5. A[idxseq[n]] = A'[idxseq[n]]
        BY <2>1, <3>2, <3>4 DEF E2, TypeOK
      <3>6. PICK q \in ProcSet : pc'[q] = "D2" /\ idxseq[n] < j'[q] /\ idxseq[m] < l'[q]
        BY <2>5, <3>2, <3>5 DEF Justified
      <3>7. q # p
        BY <2>1, <3>6 DEF E2, TypeOK
      <3>8. pc[q] = "D2" /\ idxseq[n] < j[q] /\ idxseq[m] < l[q]
        BY <2>1, <3>6, <3>7 DEF E2, TypeOK
      <3> QED
        BY <3>6, <3>8      
    <2>9. c.state = [i \in 1..Len(idxseq) |-> Val(idxseq[i])]
      <3> SUFFICES ASSUME NEW i \in 1..Len(idxseq)
                   PROVE  Val(idxseq[i])' = Val(idxseq[i])
        BY <2>5
      <3>1. CASE idxseq[i] = l[p]
        <4>1. A'[idxseq[i]] = arg[p].val
          BY <2>1, <3>1 DEF E2, TypeOK
        <4>2. arg[p].val # "BOT"
          BY <2>1, BotNotElt DEF E2, TypeOK, ArgsOf, PCtoOp
        <4>3. A'[idxseq[i]] # "BOT"
          BY <4>1, <4>2
        <4>4. Val(idxseq[i])' = arg[p].val
          BY <4>1, <4>3 DEF Val
        <4>5. EnqIdxInv
          BY PTL
        <4>6. A[l[p]] = "BOT"
          BY <3>1, <4>5 DEF EnqIdxInv, E2
        <4>7. pc[p] = "E2" /\ l[p] = idxseq[i]
          BY <3>1 DEF E2
        <4>8. \A q \in ProcSet : (pc[q] = "E2" /\ l[q] = idxseq[i]) <=> q = p
          BY <3>1, <4>5, <4>7 DEF EnqIdxInv
        <4>9. p = CHOOSE q \in ProcSet : pc[q] = "E2" /\ l[q] = idxseq[i]
          BY <4>8, <4>7, Zenon
        <4>10. Val(idxseq[i]) = arg[p].val
          BY <4>6, <4>7, <4>9 DEF Val
        <4> QED
          BY <4>4, <4>10
      <3> SUFFICES ASSUME idxseq[i] # l[p]
                   PROVE  Val(idxseq[i])' = Val(idxseq[i])
        BY <3>1
      <3>2. A'[idxseq[i]] = A[idxseq[i]]
        BY <2>1 DEF E2, TypeOK, Perm
      <3>3. CASE A[idxseq[i]] # "BOT"
        BY <3>2, <3>3 DEF Val, Perm
      <3> SUFFICES ASSUME A[idxseq[i]] = "BOT"
                   PROVE  Val(idxseq[i])' = Val(idxseq[i])
        BY <3>3
      <3>4. CASE (\E q \in ProcSet : pc[q] = "E2" /\ l[q] = idxseq[i])
        <4>1. PICK q \in ProcSet : pc[q] = "E2" /\ l[q] = idxseq[i]
          BY <3>4
        <4>2. q # p
          BY <4>1
        <4>3. EnqIdxInv
          BY PTL
        <4>4. \A r \in ProcSet : (pc[r] = "E2" /\ l[r] = idxseq[i]) <=> r = q
          BY <4>3, <4>1 DEF EnqIdxInv
        <4>5. q = CHOOSE r \in ProcSet : pc[r] = "E2" /\ l[r] = idxseq[i]
          BY <4>4, <4>1, Zenon
        <4>6. Val(idxseq[i]) = arg[q].val
          BY <3>4, <4>5 DEF Val
        <4>7. EnqIdxInv'
          BY PTL
        <4>8. \A r \in ProcSet : (pc'[r] = "E2" /\ l'[r] = idxseq[i]) <=> r = q
          BY <4>7, <4>1, <4>2, <2>1 DEF EnqIdxInv, E2, TypeOK
        <4>9. A'[idxseq[i]] = "BOT"
          BY <3>2
        <4>10. pc'[q] = "E2" /\ l'[q] = idxseq[i]
          BY <4>1, <2>1 DEF E2, TypeOK
        <4>11. Val(idxseq[i])' = arg'[q].val
          BY <4>10, <4>8, <4>9 DEF Val
        <4> QED
          BY <4>6, <4>11 DEF E2
      <3> SUFFICES ASSUME ~(\E q \in ProcSet : pc[q] = "E2" /\ l[q] = idxseq[i])
                   PROVE  Val(idxseq[i])' = Val(idxseq[i])
        BY <3>4
      <3>4. Val(idxseq[i]) = "BOT"
        BY <3>2, <3>3 DEF Val
      <3>5. Val(idxseq[i])' = "BOT"
        BY <3>2, <3>3, <2>1 DEF Val, Perm, TypeOK, E2
      <3> QED
        BY <3>4, <3>5
    <2>10. \A q \in ProcSet : 
              /\ pc[q] = "RM" => c.res[q] = "BOT"
              /\ pc[q] = "E1" => c.res[q] = "BOT"
              /\ (pc[q] = "E2" /\ l[q] \notin idxset) => c.res[q] = "BOT"
              /\ (pc[q] = "E2" /\ l[q] \in idxset) => c.res[q] = "ACK"
              /\ pc[q] = "E3" => c.res[q] = "ACK"
              /\ pc[q] = "D1" => c.res[q] = "BOT"
              /\ pc[q] = "D2" => c.res[q] = "BOT"
              /\ pc[q] = "D3" => c.res[q] = v[q]
      <3> SUFFICES l[p] \in idxset
        BY <2>1, <2>5 DEF E2, TypeOK
      <3>0. EnqIdxInv
        BY PTL
      <3>1. l[p] \in idxset
        BY <2>1, <2>4, <3>0, BotNotElt DEF E2, TypeOK, Val, EnqIdxInv, ArgsOf, PCtoOp
      <3> QED
        BY <3>1
    <2> QED
      BY <2>8, <2>9, <2>10
  <1>3. ASSUME D1(p),
               NEW c \in ConfigDomain,
               c \in Q'
        PROVE  c \in Evolve(Q)
  <1>4. ASSUME D2(p),
               NEW c \in ConfigDomain,
               c \in Q'
        PROVE  c \in Evolve(Q)
  <1> QED
    BY <1>1, <1>2, <1>3, <1>4, Zenon DEF InterAct, InterLines, Q

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
  BY Isa DEF Q, varsP, vars, implvars, Justified, Val

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
