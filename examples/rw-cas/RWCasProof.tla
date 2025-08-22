----------------------------- MODULE RWCasProof -----------------------------
(***************************************************************************)
EXTENDS RWCas, FiniteSetTheorems, FinitePermutations, TLAPS
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
  \* /\ arg = [p \in ProcSet |-> "BOT"]
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
ASSUME RegDomainNE == RegDomain # {}

-----------------------------------------------------------------------------
(***************************************************************************)
(* INVARIANTS                                                              *)
(***************************************************************************)
TypeOK == /\ X \in RegDomain
          /\ x \in [ProcSet -> RegDomain]
          /\ arg \in [ProcSet -> ArgDomain]
          /\ \A p \in ProcSet : pc[p] # "RM" => arg[p] \in ArgsOf(PCtoOp(pc[p]))
          /\ ret \in [ProcSet -> RetDomain]
          /\ pc \in [ProcSet -> LineIDs]

LEMMA SpecTypeOK == Spec => []TypeOK
  <1>1. Init => TypeOK
    BY RegDomainNE DEF Init, ImplInit, InitState, TypeOK, LineIDs, StateDomain, ArgDomain
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
      <3>1. CASE R1(p)
        BY <3>1 DEF TypeOK, R1, LineIDs, ArgsOf, PCtoOp
      <3>2. CASE W1(p)
        BY <3>2 DEF TypeOK, W1, LineIDs, ArgsOf, PCtoOp
      <3>3. CASE W2(p)
        BY <3>3 DEF TypeOK, W2, LineIDs, ArgsOf, PCtoOp
      <3> QED 
        BY <2>2, <3>1, <3>2, <3>3 DEF InterLines
    <2>3. ASSUME NEW p \in ProcSet,
                 NEW LineAct \in ReturnLines(p),
                 LineAct
          PROVE  TypeOK'
      <3>1. CASE R2(p)
        BY <3>1 DEF TypeOK, R2, LineIDs, ArgsOf, PCtoOp, OpNames, RetDomain, RetsOf
      <3>2. CASE W3(p)
        BY <3>2 DEF TypeOK, W3, LineIDs, ArgsOf, PCtoOp, OpNames, RetDomain, RetsOf
      <3> QED
        BY <2>3, <3>1, <3>2 DEF ReturnLines
    <2>4. CASE UNCHANGED vars
      BY <2>4 DEF vars, implvars, TypeOK
    <2>5. QED
      BY <2>1, <2>2, <2>3, <2>4 DEF InterAct, Next, ReturnAct
  <1> QED
    BY <1>1, <1>2, PTL DEF Spec

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
      <3>2. CASE R1(p)
        BY <3>2, FS_Subset DEF FinActive, TypeOK, R1
      <3>3. CASE W1(p)
        BY <3>3, FS_Subset DEF FinActive, TypeOK, W1
      <3>4. CASE W2(p)
        BY <3>4, FS_Subset DEF FinActive, TypeOK, W2
      <3> QED
        BY <2>2, <3>2, <3>3, <3>4 DEF InterLines
    <2>3. ASSUME NEW p \in ProcSet,
                 NEW LineAct \in ReturnLines(p),
                 LineAct
          PROVE  FinActive'
      <3>1. TypeOK
        BY PTL
      <3> USE <3>1
      <3>2. CASE R2(p)
        BY <3>2, FS_Subset DEF FinActive, TypeOK, R2
      <3>3. CASE W3(p)
        BY <3>3, FS_Subset DEF FinActive, TypeOK, W3
      <3> QED
        BY <2>3, <3>2, <3>3 DEF ReturnLines
    <2>4. CASE UNCHANGED vars
      BY <2>4 DEF vars, FinActive
    <2>5. QED
      BY <2>1, <2>2, <2>3, <2>4 DEF InterAct, Next, ReturnAct
  <1> QED
    BY <1>1, <1>2, PTL DEF Spec

-----------------------------------------------------------------------------
(***************************************************************************)
(* Plausibility set definition                                             *)
(***************************************************************************)
Q == {c \in ConfigDomain : 
        /\ c.state = X
        /\ c.op = [q \in ProcSet |-> PCtoOp(pc[q])]
        /\ c.arg = [q \in ProcSet |-> IF pc[q] = "RM" 
                                         THEN "BOT" ELSE arg[q]]
        /\ \A q \in ProcSet : 
           /\ pc[q] = "RM" => c.res[q] = "BOT"
           /\ pc[q] = "R1" => c.res[q] = "BOT"
           /\ pc[q] = "R2" => c.res[q] = x[q]
           /\ pc[q] = "W1" => c.res[q] = "BOT"
           /\ pc[q] = "W2" => \/ c.res[q] = "BOT"
                              \/ (c.res[q] = "ACK" /\ X # x[q])
           /\ pc[q] = "W3" => c.res[q] = "ACK"} 

-----------------------------------------------------------------------------
(***************************************************************************)
(* Plausibility set theorem 1: Q is non-empty is an invariant of ASpec.    *)
(***************************************************************************)
LEMMA TypeOKImpliesQNE == TypeOK => Q # {}
  <1> SUFFICES ASSUME TypeOK 
               PROVE  Q # {}
    OBVIOUS
  <1>1. PICK val \in StateDomain : val = X
    BY DEF TypeOK, StateDomain
  <1> DEFINE cop == [p \in ProcSet |-> PCtoOp(pc[p])]
  <1>2. cop \in [ProcSet -> OpDomain]
    BY DEF OpDomain, OpNames, PCtoOp, TypeOK, LineIDs
  <1> DEFINE carg == [p \in ProcSet |-> IF pc[p] = "RM" THEN "BOT" ELSE arg[p]]
  <1>3. carg \in [ProcSet -> ArgDomain]
    BY Zenon DEF ArgDomain, TypeOK, ArgsOf, PCtoOp
  <1> DEFINE cres == [p \in ProcSet |-> CASE pc[p] = "R2" -> x[p]
                                          [] pc[p] = "W3" -> "ACK"
                                          [] OTHER -> "BOT"]
  <1>4. cres \in [ProcSet -> ResDomain]
    BY DEF ResDomain, RetDomain, TypeOK, RetsOf, OpNames
  <1> DEFINE c == [state |-> val, op |-> cop, arg |-> carg, res |-> cres]
  <1>5. c \in ConfigDomain
    BY <1>1, <1>2, <1>3, <1>4 DEF ConfigDomain
  <1> SUFFICES c \in Q
    OBVIOUS
  <1> QED
    BY <1>1, <1>5, Zenon DEF Q, PCtoOp, TypeOK


THEOREM PlausSetThm1 == ASpec => [](Q # {})
  <1> SUFFICES Spec => [](Q # {})
    BY ASpecImpliesSpec
  <1> SUFFICES Spec => []TypeOK 
    BY PTL, TypeOKImpliesQNE
  <1> QED
    BY SpecTypeOK

-----------------------------------------------------------------------------
(***************************************************************************)
(* Plausibility set lemma 2.1: Q is initally the same as the singleton P.  *)
(***************************************************************************)
LEMMA PlausSetInitLemma == AInit => Q = P
  <1> SUFFICES ASSUME AInit
               PROVE  Q = P
    OBVIOUS
  <1>1. Q # {}
    <2>1. TypeOK
      BY RegDomainNE DEF AInit, Init, ImplInit, InitState, TypeOK, LineIDs, StateDomain, ArgDomain
    <2> QED
      BY <2>1, TypeOKImpliesQNE
  <1>2. Q \in SUBSET ConfigDomain
    BY DEF Q
  <1> SUFFICES \A c \in Q : 
        c = [state |-> InitState,
             op    |-> [p \in ProcSet |-> "BOT"],
             arg   |-> [p \in ProcSet |-> "BOT"],
             res   |-> [p \in ProcSet |-> "BOT"]]
    BY <1>1, Zenon DEF AInit
  <1> SUFFICES ASSUME NEW c \in ConfigDomain,
                      c \in Q
               PROVE  /\ c.state = InitState
                      /\ c.op = [p \in ProcSet |-> "BOT"]
                      /\ c.arg = [p \in ProcSet |-> "BOT"]
                      /\ c.res = [p \in ProcSet |-> "BOT"]
    BY <1>2 DEF ConfigDomain
  <1>3. c.state = InitState
    BY DEF AInit, Init, ImplInit, Q
  <1>4. c.op = [p \in ProcSet |-> "BOT"]
    BY DEF Q, PCtoOp, AInit, Init
  <1>5. c.arg = [p \in ProcSet |-> "BOT"]
    BY DEF Q, AInit, Init
  <1>6. c.res = [p \in ProcSet |-> "BOT"]
    BY DEF Q, ConfigDomain, AInit, Init 
  <1> QED
    BY <1>3, <1>4, <1>5, <1>6

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

LEMMA InvocLemma == ASpec => [][InvocProperty]_varsP
  <1> SUFFICES ASSUME []TypeOK
               PROVE  ASpec => [][InvocProperty]_varsP
    BY ASpecImpliesSpec, SpecTypeOK
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
  <1>1. Q \in SUBSET ConfigDomain
    BY Zenon DEF Q
  <1>2. c.op[p] = PCtoOp(pc'[p])
    BY DEF Q
  <1>3. c.arg[p] = arg'[p]
    <2> SUFFICES pc'[p] # "RM"
      BY DEF Q
    <2>1. TypeOK
      BY PTL
    <2> QED
      BY <2>1 DEF InvocAct, OpToFirstLine, OpNames, TypeOK
  <1>4. c.res[p] = "BOT"
    <2> SUFFICES pc'[p] = "W1" \/ pc'[p] = "R1"
      BY DEF Q
    <2>1. TypeOK
      BY PTL
    <2> QED
      BY <2>1 DEF Q, InvocAct, OpToFirstLine, OpNames, TypeOK
  <1> DEFINE c_prev == [c EXCEPT !.op = [c.op EXCEPT ![p] = "BOT"],
                                 !.arg = [c.arg EXCEPT ![p] = "BOT"]]
  <1> SUFFICES c_prev \in Q
    BY <1>1, <1>2, <1>3, <1>4, InvokeAndEvolveFromUninvoked
  <1>5. c_prev \in ConfigDomain
    BY DEF ConfigDomain, OpDomain, ArgDomain
  <1>6. c_prev.state = X
    BY DEF Q, InvocAct, implvars, ConfigDomain
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
  <1> SUFFICES /\ \A q \in ProcSet : 
                  /\ pc[q] = "RM" => c_prev.res[q] = "BOT"
                  /\ pc[q] = "R1" => c_prev.res[q] = "BOT"
                  /\ pc[q] = "R2" => c_prev.res[q] = x[q]
                  /\ pc[q] = "W1" => c_prev.res[q] = "BOT"
                  /\ pc[q] = "W2" => \/ c_prev.res[q] = "BOT"
                                     \/ (c_prev.res[q] = "ACK" /\ X # x[q])
                  /\ pc[q] = "W3" => c_prev.res[q] = "ACK"
    BY <1>5, <1>6, <1>7, <1>8 DEF Q
  <1>9. c_prev.res = c.res BY DEF ConfigDomain
  <1> SUFFICES /\ \A q \in ProcSet : 
                  /\ pc[q] = "RM" => c.res[q] = "BOT"
                  /\ pc[q] = "R1" => c.res[q] = "BOT"
                  /\ pc[q] = "R2" => c.res[q] = x[q]
                  /\ pc[q] = "W1" => c.res[q] = "BOT"
                  /\ pc[q] = "W2" => \/ c.res[q] = "BOT"
                                     \/ (c.res[q] = "ACK" /\ X # x[q])
                  /\ pc[q] = "W3" => c.res[q] = "ACK"
    BY <1>9
  <1>10. pc[p] = "RM" /\ c.res[p] = "BOT"
    BY <1>4 DEF InvocAct
  <1> SUFFICES ASSUME NEW q \in ProcSet,
                      q # p
               PROVE  /\ pc[q] = "RM" => c.res[q] = "BOT"
                      /\ pc[q] = "R1" => c.res[q] = "BOT"
                      /\ pc[q] = "R2" => c.res[q] = x[q]
                      /\ pc[q] = "W1" => c.res[q] = "BOT"
                      /\ pc[q] = "W2" => \/ c.res[q] = "BOT"
                                         \/ (c.res[q] = "ACK" /\ X # x[q])
                      /\ pc[q] = "W3" => c.res[q] = "ACK"
    BY <1>10
  <1>11. /\ \A q1 \in ProcSet : 
            /\ pc'[q1] = "RM" => c.res[q1] = "BOT"
            /\ pc'[q1] = "R1" => c.res[q1] = "BOT"
            /\ pc'[q1] = "R2" => c.res[q1] = x'[q1]
            /\ pc'[q1] = "W1" => c.res[q1] = "BOT"
            /\ pc'[q1] = "W2" => \/ c.res[q1] = "BOT"
                                 \/ (c.res[q1] = "ACK" /\ X' # x'[q1])
            /\ pc'[q1] = "W3" => c.res[q1] = "ACK"
    BY DEF Q
  <1>12. pc'[q] = pc[q] /\ x'[q] = x[q] /\ X' = X
    <2>1. TypeOK
      BY PTL
    <2> QED
      BY <2>1 DEF InvocAct, TypeOK, implvars
  <1> QED
    BY <1>11, <1>12

-----------------------------------------------------------------------------
(***************************************************************************)
(* Plausibility set lemma 2.3: If an intermediate-line action takes place, *)
(* then the new plausibility set Q' is a subset of the evolution of Q.     *)
(***************************************************************************)
InterProperty == \A p \in ProcSet : InterAct(p) => (Q' \in SUBSET Evolve(Q))

LEMMA InterLemma == ASpec => [][InterProperty]_varsP
  <1> SUFFICES ASSUME []TypeOK, []FinActive
               PROVE  ASpec => [][InterProperty]_varsP
    BY ASpecImpliesSpec, SpecTypeOK, SpecFinActive
  <1> SUFFICES ASSUME ANext
               PROVE  InterProperty
    BY PTL DEF ASpec
  <1> SUFFICES ASSUME NEW p \in ProcSet,
                      InterAct(p)
               PROVE  Q' \in SUBSET Evolve(Q)
    BY DEF InterProperty
  <1>1. ASSUME R1(p),
               NEW c \in ConfigDomain,
               c \in Q'
        PROVE  c \in Evolve(Q)
    <2> USE <1>1
    <2> DEFINE c_prev == [c EXCEPT !.res = [c.res EXCEPT ![p] = "BOT"]]
    <2>1. c_prev \in ConfigDomain
      BY DEF ConfigDomain, ResDomain
    <2>2. Q \in SUBSET ConfigDomain
      BY DEF Q
    <2> SUFFICES c_prev \in Q /\ Delta(c_prev, p, c)
      BY <2>1, <2>2, SingleDeltaEvolve
    <2>3. c_prev \in Q
      <3>1. c_prev.state = X
        BY DEF ConfigDomain, Q, R1
      <3>2. c_prev.op = [q \in ProcSet |-> PCtoOp(pc[q])]
        <4>1. c_prev.op = [q \in ProcSet |-> PCtoOp(pc'[q])]
          BY DEF Q, ConfigDomain
        <4>2. TypeOK
          BY PTL
        <4>3. PCtoOp(pc[p]) = PCtoOp(pc'[p])
          BY <4>2 DEF R1, PCtoOp, TypeOK
        <4> SUFFICES ASSUME NEW q \in ProcSet, q # p
                     PROVE  pc'[q] = pc[q]
          BY <4>1, <4>3
        <4> QED
          BY <4>2 DEF R1, TypeOK
      <3>3. c_prev.arg = [q \in ProcSet |-> IF pc[q] = "RM" THEN "BOT" ELSE arg[q]]
        <4>1. c_prev.arg = [q \in ProcSet |-> IF pc'[q] = "RM" THEN "BOT" ELSE arg'[q]]
          BY DEF Q, ConfigDomain
        <4>2. TypeOK
          BY PTL
        <4>3. arg' = arg /\ \A q \in ProcSet : q # p => pc'[q] = pc[q]
          BY <4>2 DEF R1, TypeOK
        <4> SUFFICES pc[p] # "RM" /\ pc'[p] # "RM"
          BY <4>1, <4>3
        <4> QED
          BY <4>2 DEF R1, TypeOK
      <3>4. pc[p] = "R1" /\ c_prev.res[p] = "BOT"
        BY DEF R1, ConfigDomain
      <3> SUFFICES ASSUME NEW q \in ProcSet, q # p
                   PROVE  /\ pc[q] = "RM" => c_prev.res[q] = "BOT"
                          /\ pc[q] = "R1" => c_prev.res[q] = "BOT"
                          /\ pc[q] = "R2" => c_prev.res[q] = x[q]
                          /\ pc[q] = "W1" => c_prev.res[q] = "BOT"
                          /\ pc[q] = "W2" => \/ c_prev.res[q] = "BOT"
                                             \/ (c_prev.res[q] = "ACK" /\ X # x[q])
                          /\ pc[q] = "W3" => c_prev.res[q] = "ACK"
        BY <2>1, <3>1, <3>2, <3>3, <3>4 DEF Q
      <3> SUFFICES pc'[q] = pc[q] /\ x'[q] = x[q] /\ X' = X
        BY DEF Q, ConfigDomain
      <3>5. TypeOK
        BY PTL
      <3> QED
        BY <3>5 DEF R1, TypeOK
    <2>4. Delta(c_prev, p, c)
      <3> SUFFICES /\ c_prev.op[p] = "Read"
                   /\ c_prev.arg[p] \in ArgsOf("Read")
                   /\ c.res = [c_prev.res EXCEPT ![p] = c_prev.state]
        BY DEF Delta, ConfigDomain
      <3>1. TypeOK
        BY PTL
      <3>2. c_prev.op[p] = "Read" /\ c_prev.arg[p] \in ArgsOf("Read")
        BY <3>1 DEF ConfigDomain, Q, PCtoOp, R1, TypeOK, ArgsOf
      <3> SUFFICES c.res = [c_prev.res EXCEPT ![p] = c_prev.state]
        BY <3>2
      <3> SUFFICES c.res[p] = X'
        BY DEF ConfigDomain, Q
      <3>3. c.res[p] = x'[p]
        BY <3>1 DEF Q, R1, TypeOK
      <3> SUFFICES x'[p] = X'
        BY <3>3
      <3> QED
        BY <3>1 DEF R1, TypeOK
    <2> QED
      BY <2>3, <2>4
  <1>2. ASSUME W1(p),
               NEW c \in ConfigDomain,
               c \in Q'
        PROVE  c \in Evolve(Q)
    <2> USE <1>2
    <2> SUFFICES c \in Q
      BY EmptySeqEvolve DEF Q
    <2>1. TypeOK
      BY PTL
    <2>2. c.state = X
      BY DEF Q, W1
    <2>3. c.op = [q \in ProcSet |-> PCtoOp(pc[q])]
      <3>1. c.op = [q \in ProcSet |-> PCtoOp(pc'[q])]
        BY DEF Q
      <3>2. PCtoOp(pc[p]) = PCtoOp(pc'[p])
        BY <2>1 DEF W1, PCtoOp, TypeOK
      <3> SUFFICES ASSUME NEW q \in ProcSet, q # p
                   PROVE  pc'[q] = pc[q]
        BY <3>1, <3>2
      <3> QED
        BY <2>1 DEF W1, TypeOK
    <2>4. c.arg = [q \in ProcSet |-> IF pc[q] = "RM" THEN "BOT" ELSE arg[q]]
      <3>1. c.arg = [q \in ProcSet |-> IF pc'[q] = "RM" THEN "BOT" ELSE arg'[q]]
        BY DEF Q
      <3> SUFFICES pc'[p] # "RM" /\ pc[p] # "RM"
        BY <3>1, <2>1 DEF W1, TypeOK
      <3> QED
        BY <2>1 DEF W1, TypeOK
    <2>5. pc'[p] = "W2" /\ X' = x'[p]
      BY <2>1 DEF W1, TypeOK
    <2>6. pc[p] = "W1" /\ c.res[p] = "BOT"
      BY <2>5 DEF Q, W1
    <2> SUFFICES ASSUME NEW q \in ProcSet, q # p
                 PROVE  /\ pc[q] = "RM" => c.res[q] = "BOT"
                        /\ pc[q] = "R1" => c.res[q] = "BOT"
                        /\ pc[q] = "R2" => c.res[q] = x[q]
                        /\ pc[q] = "W1" => c.res[q] = "BOT"
                        /\ pc[q] = "W2" => \/ c.res[q] = "BOT"
                                           \/ (c.res[q] = "ACK" /\ X # x[q])
                        /\ pc[q] = "W3" => c.res[q] = "ACK"
      BY <2>2, <2>3, <2>4, <2>6 DEF Q
    <2> SUFFICES pc'[q] = pc[q] /\ x'[q] = x[q] /\ X' = X
      BY DEF Q
    <2> QED
      BY <2>1 DEF W1, TypeOK
  <1>3. ASSUME W2(p),
               NEW c \in ConfigDomain,
               c \in Q'
        PROVE  c \in Evolve(Q)
    <2> USE <1>3
    <2>1. CASE X # x[p]
      <3> USE <2>1
      <3> SUFFICES c \in Q
        BY EmptySeqEvolve DEF Q
      <3>1. TypeOK
        BY PTL
      <3>2. c.state = X
        BY DEF Q, W2
      <3>3. c.op = [q \in ProcSet |-> PCtoOp(pc[q])]
        <4>1. c.op = [q \in ProcSet |-> PCtoOp(pc'[q])]
          BY DEF Q
        <4>2. PCtoOp(pc[p]) = PCtoOp(pc'[p])
          BY <3>1 DEF W2, PCtoOp, TypeOK
        <4> SUFFICES ASSUME NEW q \in ProcSet, q # p
                     PROVE  pc'[q] = pc[q]
          BY <4>1, <4>2
        <4> QED
          BY <3>1 DEF W2, TypeOK
      <3>4. c.arg = [q \in ProcSet |-> IF pc[q] = "RM" THEN "BOT" ELSE arg[q]]
        <4>1. c.arg = [q \in ProcSet |-> IF pc'[q] = "RM" THEN "BOT" ELSE arg'[q]]
          BY DEF Q
        <4> SUFFICES pc'[p] # "RM" /\ pc[p] # "RM"
          BY <4>1, <3>1 DEF W2, TypeOK
        <4> QED
          BY <3>1 DEF W2, TypeOK
      <3>5. pc'[p] = "W3" 
        BY <3>1 DEF W2, TypeOK
      <3>6. pc[p] = "W2" /\ c.res[p] = "ACK" /\ X # x[p]
        BY <3>5 DEF Q, W2
      <3> SUFFICES ASSUME NEW q \in ProcSet, q # p
                   PROVE  /\ pc[q] = "RM" => c.res[q] = "BOT"
                          /\ pc[q] = "R1" => c.res[q] = "BOT"
                          /\ pc[q] = "R2" => c.res[q] = x[q]
                          /\ pc[q] = "W1" => c.res[q] = "BOT"
                          /\ pc[q] = "W2" => \/ c.res[q] = "BOT"
                                             \/ (c.res[q] = "ACK" /\ X # x[q])
                          /\ pc[q] = "W3" => c.res[q] = "ACK"
        BY <3>2, <3>3, <3>4, <3>6 DEF Q
      <3> SUFFICES pc'[q] = pc[q] /\ x'[q] = x[q] /\ X' = X
        BY DEF Q
      <3> QED
        BY <3>1 DEF W2, TypeOK
    <2>2. CASE X = x[p]
      <3> USE <2>2
      <3> DEFINE c_prev == 
        [c EXCEPT !.state = X,
                  !.res = [q \in ProcSet |-> IF pc[q] = "W2" THEN "BOT" ELSE c.res[q]]]
      <3> SUFFICES /\ c_prev \in ConfigDomain 
                   /\ c_prev \in Q
                   /\ \E alpha \in Seq(ProcSet) : TransitionsOK(c_prev, alpha, c)
        BY DEF Evolve
      <3>1. TypeOK
        BY PTL
      <3>2. c_prev \in ConfigDomain
        BY <3>1 DEF ConfigDomain, TypeOK, StateDomain, ResDomain
      <3>3. c_prev \in Q
        <4>1. c_prev.state = X
          BY DEF ConfigDomain
        <4>2. c_prev.op = [q \in ProcSet |-> PCtoOp(pc[q])]
          <5>1. c_prev.op = [q \in ProcSet |-> PCtoOp(pc'[q])]
            BY DEF Q, ConfigDomain
          <5>2. PCtoOp(pc[p]) = PCtoOp(pc'[p])
            BY <3>1 DEF W2, PCtoOp, TypeOK
          <5> SUFFICES ASSUME NEW q \in ProcSet, q # p
                       PROVE  pc'[q] = pc[q]
            BY <5>1, <5>2
          <5> QED
            BY <3>1 DEF W2, TypeOK
        <4>3. c_prev.arg = [q \in ProcSet |-> IF pc[q] = "RM" THEN "BOT" ELSE arg[q]]
          <5>1. c_prev.arg = [q \in ProcSet |-> IF pc'[q] = "RM" THEN "BOT" ELSE arg'[q]]
            BY DEF Q, ConfigDomain
          <5> SUFFICES pc'[p] # "RM" /\ pc[p] # "RM"
            BY <5>1, <3>1 DEF W2, TypeOK
          <5> QED
            BY <3>1 DEF W2, TypeOK
        <4> SUFFICES ASSUME NEW q \in ProcSet
                     PROVE  /\ pc[q] = "RM" => c_prev.res[q] = "BOT"
                            /\ pc[q] = "R1" => c_prev.res[q] = "BOT"
                            /\ pc[q] = "R2" => c_prev.res[q] = x[q]
                            /\ pc[q] = "W1" => c_prev.res[q] = "BOT"
                            /\ pc[q] = "W2" => c_prev.res[q] = "BOT"
                            /\ pc[q] = "W3" => c_prev.res[q] = "ACK"
          BY <3>2, <4>1, <4>2, <4>3 DEF Q
        <4> QED
          BY <3>1 DEF W2, TypeOK, Q, ConfigDomain
      <3> DEFINE FailedWrites == {q \in ProcSet : pc[q] = "W2" /\ c.res[q] = "ACK" /\ q # p}
      <3>4. IsFiniteSet(FailedWrites)
        <4> SUFFICES IsFiniteSet({q \in ProcSet : pc[q] = "W2"})
          BY FS_Subset
        <4>1. {q \in ProcSet : pc[q] = "W2"} \in SUBSET {q \in ProcSet : pc[q] # "RM"}
          OBVIOUS
        <4> SUFFICES IsFiniteSet({q \in ProcSet : pc[q] # "RM"})
          BY <4>1, FS_Subset
        <4>2. FinActive
          BY PTL
        <4> QED
          BY <4>2 DEF FinActive
      <3>5. PICK alpha \in Perm(FailedWrites) : TRUE
        BY <3>4, PermutationExists
      <3> DEFINE alpha_p == alpha \o <<p>>
      <3>6. alpha_p \in Seq(ProcSet)
        BY <3>5 DEF Perm
      <3> SUFFICES TransitionsOK(c_prev, alpha_p, c)
        BY <3>2, <3>3, <3>6
      <3> DEFINE BetaRest(i) == [state |-> arg[alpha_p[i]].newval, 
                                 op    |-> c_prev.op,
                                 arg   |-> c_prev.arg,
                                 res   |-> [q \in ProcSet |-> IF \E j \in 1..i : alpha_p[j] = q 
                                                                 THEN "ACK" 
                                                                 ELSE c_prev.res[q]]]
      <3> DEFINE beta_rest == [i \in 1..Len(alpha_p) |-> BetaRest(i)]
      <3> DEFINE beta == <<c_prev>> \o beta_rest
      <3>7. beta_rest \in Seq(ConfigDomain)
        <4> SUFFICES ASSUME NEW i \in 1..Len(alpha_p)
                     PROVE  BetaRest(i) \in ConfigDomain
          BY <3>5, <3>6 
        <4> SUFFICES arg[alpha_p[i]].newval \in StateDomain
          BY <3>2 DEF BetaRest, ConfigDomain, ResDomain, RetsOf, OpNames
        <4>1. alpha_p \in Seq({q \in ProcSet : pc[q] = "W2"})
          BY <3>5 DEF Perm, W2
        <4>2. alpha_p[i] \in ProcSet /\ pc[alpha_p[i]] = "W2"
          BY <4>1
        <4>3. arg[alpha_p[i]] \in ArgsOf("Write")
          BY <3>1, <4>2 DEF PCtoOp, TypeOK
        <4> QED
          BY <4>3 DEF ArgsOf, StateDomain
      <3>8. beta \in Seq(ConfigDomain)
        BY <3>7, <3>2
      <3>9. beta[1] = c_prev 
        BY <3>7
      <3>10. Len(beta) = Len(alpha_p) + 1
        BY <3>6
      <3> SUFFICES /\ \A i \in 1..Len(alpha_p) : Delta(beta[i], alpha_p[i], beta[i+1])
                   /\ beta[Len(beta)] = c
        BY Zenon, <3>8, <3>9, <3>10 DEF TransitionsOK
      <3>11. ASSUME NEW i \in 1..Len(alpha_p)
             PROVE  Delta(beta[i], alpha_p[i], beta[i+1])
        <4> USE <3>11
        <4> DEFINE bi == beta[i]
                   q == alpha_p[i]
                   bi1 == beta[i+1]
        <4> HIDE DEF beta
        <4> SUFFICES /\ bi.op[q] = "Write" 
                     /\ bi.arg[q] \in ArgsOf("Write") 
                     /\ bi.res[q] = "BOT"
                     /\ bi1.state = bi.arg[q].newval
                     /\ bi1.op = bi.op
                     /\ bi1.arg = bi.arg 
                     /\ bi1.res = [bi.res EXCEPT ![q] = "ACK"]
          BY DEF Delta
        <4>1. bi1.op = bi.op /\ bi1.arg = bi.arg
          BY <3>7 DEF beta
        <4>2. bi.op = c_prev.op /\ bi.arg = c_prev.arg
          BY <3>7 DEF beta
        <4>3. q = p \/ q \in {r \in ProcSet : pc[r] = "W2" /\ c.res[r] = "ACK" /\ r # p}
          BY <3>5 DEF alpha_p, Perm, W2
        <4>4. c_prev.op = [r \in ProcSet |-> PCtoOp(pc[r])]
          BY <3>3 DEF Q, ConfigDomain
        <4>5. c_prev.op[q] = "Write"
          BY <4>3, <4>4 DEF PCtoOp, W2
        <4>6. c_prev.arg = [r \in ProcSet |-> IF pc[r] = "RM" THEN "BOT" ELSE arg[r]]
          BY <3>3 DEF Q, ConfigDomain
        <4>7. c_prev.arg[q] \in ArgsOf("Write")
          BY <3>1, <4>3, <4>6 DEF TypeOK, W2, PCtoOp
        <4> SUFFICES /\ bi.res[q] = "BOT"
                     /\ bi1.state = bi.arg[q].newval
                     /\ bi1.res = [bi.res EXCEPT ![q] = "ACK"]
          BY <4>1, <4>2, <4>5, <4>6, <4>7
        <4>8. /\ i = 1 => bi.res = c_prev.res
              /\ i # 1 => bi.res = [r \in ProcSet |-> IF \E j \in 1..(i-1) : alpha_p[j] = r THEN "ACK" ELSE c_prev.res[r]]
          BY <3>7 DEF beta
        <4>9. c_prev.res = [r \in ProcSet |-> IF pc[r] = "W2" THEN "BOT" ELSE c.res[r]]
          BY DEF ConfigDomain, Q, W2
        <4>10. c_prev.res[q] = "BOT"
          BY <4>3, <4>9 DEF W2
        <4>11. bi.res[q] = "BOT"
          <5> SUFFICES ASSUME i # 1
                       PROVE  ~(\E j \in 1..(i-1) : alpha_p[j] = q)
            BY <4>3, <4>8, <4>10
          <5> SUFFICES \A j \in 1..(i-1) : alpha_p[j] # q
            OBVIOUS
          <5>1. i \in 1..Len(alpha) \/ i = Len(alpha) + 1
            BY DEF Perm
          <5>2. CASE i = Len(alpha) + 1
            BY <4>3, <5>2 DEF alpha_p, Perm
          <5>3. CASE i \in 1..Len(alpha)
            BY <4>3, <5>3 DEF alpha_p, Perm
          <5> QED
            BY <5>1, <5>2, <5>3
        <4>12. bi1.state = bi.arg[q].newval
          <5>1. bi1.state = arg[q].newval
            BY <3>7 DEF beta
          <5> SUFFICES arg[q].newval = bi.arg[q].newval
            BY <5>1
          <5>2. bi.arg = c_prev.arg
            BY <3>7 DEF beta
          <5>3. c_prev.arg[q] = arg[q]
            BY <3>1, <4>3, <4>6 DEF TypeOK, W2, PCtoOp
          <5> QED
            BY <5>2, <5>3
        <4>13. bi1.res = [bi.res EXCEPT ![q] = "ACK"]
          <5>1. bi1.res = [r \in ProcSet |-> IF \E j \in 1..i : alpha_p[j] = r THEN "ACK" ELSE c_prev.res[r]]
            BY <3>7 DEF beta
          <5>2. /\ i = 1 => bi.res = c_prev.res
                /\ i # 1 => bi.res = [r \in ProcSet |-> IF \E j \in 1..(i-1) : alpha_p[j] = r THEN "ACK" ELSE c_prev.res[r]]
            BY <4>8
          <5>3. CASE i = 1
            <6> USE <5>3
            <6> SUFFICES bi1.res = [c_prev.res EXCEPT ![q] = "ACK"]
              BY <5>2
            <6> SUFFICES ASSUME NEW r \in ProcSet
                         PROVE  /\ r = q => bi1.res[r] = "ACK"
                                /\ r # q => bi1.res[r] = c_prev.res[r]
              BY <5>1, <4>9
            <6>1. bi1.res[q] = "ACK"
              BY <4>3, <5>1
            <6> SUFFICES ASSUME r # q
                         PROVE  bi1.res[r] = c_prev.res[r]
              BY <6>1
            <6> SUFFICES ~(\E j \in 1..1 : alpha_p[j] = r)
              BY <5>1
            <6> QED
              OBVIOUS
          <5> SUFFICES ASSUME i # 1,
                              NEW r \in ProcSet
                       PROVE  /\ r = q => bi1.res[r] = "ACK"
                              /\ r # q => bi1.res[r] = bi.res[r]
            BY <5>1, <5>2, <5>3
          <5>4. bi1.res[q] = "ACK"
            BY <4>3, <5>1
          <5> SUFFICES ASSUME r # q
                       PROVE  bi1.res[r] = bi.res[r]
            BY <5>4
          <5>5. CASE \E j \in 1..i : alpha_p[j] = r
            BY <5>1, <5>2
          <5> SUFFICES ASSUME ~(\E j \in 1..i : alpha_p[j] = r)
                       PROVE  bi1.res[r] = bi.res[r]
            BY <5>5
          <5>6. bi1.res[r] = c_prev.res[r]
            BY <5>1
          <5>7. bi.res[r] = c_prev.res[r]
            BY <4>8
          <5> QED
            BY <5>6, <5>7
        <4> QED
          BY <4>11, <4>12, <4>13
      <3> SUFFICES beta[Len(beta)] = c
        BY <3>11, Zenon
      <3>12. beta[Len(beta)] \in ConfigDomain
        BY <3>8, <3>6, SMTT(30)
      <3> SUFFICES /\ beta[Len(beta)].state = c.state
                   /\ beta[Len(beta)].op = c.op
                   /\ beta[Len(beta)].arg = c.arg
                   /\ beta[Len(beta)].res = c.res
        <4> HIDE DEF beta
        <4> QED BY <3>12 DEF ConfigDomain
      <3>13. beta_rest # <<>>
        BY <3>5 DEF Perm
      <3>14. beta[Len(beta)] = BetaRest(Len(alpha_p))
        <4> HIDE DEF c_prev, BetaRest
        <4> QED BY <3>6, <3>13
      <3> SUFFICES /\ arg[alpha_p[Len(alpha_p)]].newval = c.state
                   /\ c_prev.op = c.op
                   /\ c_prev.arg = c.arg
                   /\ [q \in ProcSet |-> IF \E j \in 1..Len(alpha_p) : alpha_p[j] = q 
                                            THEN "ACK" 
                                            ELSE c_prev.res[q]] = c.res
        <4> HIDE DEF c_prev
        <4> QED BY <3>14 DEF BetaRest
      <3>15. c_prev.op = c.op /\ c_prev.arg = c.arg /\ c.state = X'
        BY <3>3 DEF Q, ConfigDomain
      <3>16. alpha_p[Len(alpha_p)] = p
        BY <3>5 DEF alpha_p, Perm, W2
      <3>17. X' = arg[p].newval
        BY <3>1 DEF W2, TypeOK
      <3> SUFFICES ASSUME NEW q \in ProcSet
                   PROVE  (IF \E j \in 1..Len(alpha_p) : alpha_p[j] = q THEN "ACK" ELSE c_prev.res[q]) = c.res[q]
        BY <3>15, <3>16, <3>17 DEF Q, ConfigDomain
      <3>18. CASE (\E j \in 1..Len(alpha_p) : alpha_p[j] = q)
        <4> USE <3>18
        <4> SUFFICES c.res[q] = "ACK"
          OBVIOUS 
        <4>1. q = p \/ q \in {r \in ProcSet : pc[r] = "W2" /\ c.res[r] = "ACK" /\ r # p}
          BY <3>5 DEF alpha_p, Perm, W2
        <4> SUFFICES c.res[p] = "ACK"
          BY <4>1
        <4> SUFFICES pc'[p] = "W3"
          BY DEF Q
        <4> QED
          BY <3>1 DEF W2, TypeOK
      <3> SUFFICES ASSUME ~(\E j \in 1..Len(alpha_p) : alpha_p[j] = q)
                   PROVE  c_prev.res[q] = c.res[q]
        BY <3>18
      <3>19. c_prev.res[q] = IF pc[q] = "W2" THEN "BOT" ELSE c.res[q]
        BY DEF ConfigDomain
      <3> SUFFICES ASSUME pc[q] = "W2"
                   PROVE  c.res[q] = "BOT"
        BY <3>19
      <3>20. ~(\E j \in 1..Len(alpha) : alpha[j] = q)
        BY <3>5, <3>6 DEF alpha_p, Perm
      <3>21. \A r1 \in {r2 \in ProcSet : pc[r2] = "W2" /\ c.res[r2] = "ACK" /\ r2 # p} : (\E j \in 1..Len(alpha) : alpha[j] = r1)
        BY <3>5, PermutationIndex, SMTT(30)
      <3>22. q \notin {r \in ProcSet : pc[r] = "W2" /\ c.res[r] = "ACK" /\ r # p}
        BY <3>20, <3>21
      <3>23. \E j \in 1..Len(alpha_p) : alpha_p[j] = p
        BY <3>16, <3>5, <3>6 DEF alpha_p, Perm
      <3>24. q # p
        BY <3>23
      <3>25. q # p /\ pc[q] = "W2"
        BY <3>24
      <3>26. q \notin {r \in ProcSet : c.res[r] = "ACK"}
        BY <3>22, <3>25
      <3>27. pc'[q] = pc[q]
        BY <3>1, <3>24 DEF W2, TypeOK
      <3>28. c.res[q] = "BOT" \/ c.res[q] = "ACK"
        BY <3>27 DEF Q, ConfigDomain
      <3> QED
        BY <3>26, <3>28
    <2> QED
      BY <2>1, <2>2
  <1> QED
    BY <1>1, <1>2, <1>3, Zenon DEF InterAct, InterLines, Q

-----------------------------------------------------------------------------
(***************************************************************************)
(* Plausibility set lemma 2.4: If an intermediate-line action takes place, *)
(* then the new plausibility set Q' is a subset of the filtering of the    *)
(* evolution of Q, where the filtering is done for process p and the value *)
(* ret'[p] (which is the value to be returned by p).                       *)
(***************************************************************************)
ReturnProperty ==
  \A p \in ProcSet : ReturnAct(p) => (Q' \in SUBSET Filter(Evolve(Q), p, ret'[p]))

LEMMA ReturnLemma == ASpec => [][ReturnProperty]_varsP
  <1> SUFFICES ASSUME []TypeOK
               PROVE  ASpec => [][ReturnProperty]_varsP
    BY ASpecImpliesSpec, SpecTypeOK
  <1> SUFFICES ASSUME ANext
               PROVE  ReturnProperty
    BY PTL DEF ASpec
  <1> SUFFICES ASSUME NEW p \in ProcSet,
                      ReturnAct(p)
               PROVE  Q' \in SUBSET Filter(Evolve(Q), p, ret'[p])
    BY DEF ReturnProperty
  <1>1. ASSUME R2(p),
               NEW c \in ConfigDomain,
               c \in Q'
        PROVE  c \in Filter(Evolve(Q), p, ret'[p])
    <2> USE <1>1
    <2>1. TypeOK
      BY PTL
    <2>2. c.res[p] = "BOT"
      BY <2>1 DEF Q, R2, TypeOK
    <2>3. c.op[p] = "BOT"
      BY <2>1 DEF Q, R2, TypeOK, PCtoOp
    <2>4. c.arg[p] = "BOT"
      BY <2>1 DEF Q, R2, TypeOK
    <2> DEFINE c_prev == 
      [c EXCEPT !.op = [c.op EXCEPT ![p] = PCtoOp(pc[p])],
                !.arg = [c.arg EXCEPT ![p] = IF pc[p] = "RM" THEN "BOT" ELSE arg[p]],
                !.res = [c.res EXCEPT ![p] = ret'[p]]]
    <2> SUFFICES c_prev \in Q
      BY <2>2, <2>3, <2>4, EvolveAndFilterFromUnfiltered DEF Q
    <2>5. c_prev \in ConfigDomain
      <3> SUFFICES /\ PCtoOp(pc[p]) \in OpDomain
                   /\ (IF pc[p] = "RM" THEN "BOT" ELSE arg[p]) \in ArgDomain
                   /\ ret'[p] \in ResDomain
        BY DEF Q, ConfigDomain
      <3> QED
        BY <2>1 DEF TypeOK, PCtoOp, R2, OpDomain, ArgDomain, ResDomain, OpNames, LineIDs, RetsOf
    <2> SUFFICES /\ c_prev.state = X
                 /\ c_prev.op = [q \in ProcSet |-> PCtoOp(pc[q])]
                 /\ c_prev.arg = [q \in ProcSet |-> IF pc[q] = "RM" THEN "BOT" ELSE arg[q]]
                 /\ \A q \in ProcSet :
                    /\ pc[q] = "RM" => c_prev.res[q] = "BOT"
                    /\ pc[q] = "R1" => c_prev.res[q] = "BOT"
                    /\ pc[q] = "R2" => c_prev.res[q] = x[q]
                    /\ pc[q] = "W1" => c_prev.res[q] = "BOT"
                    /\ pc[q] = "W2" => \/ c_prev.res[q] = "BOT"
                                       \/ (c_prev.res[q] = "ACK" /\ X # x[q])
                    /\ pc[q] = "W3" => c_prev.res[q] = "ACK"
      BY <2>5 DEF Q
    <2>6. c_prev.state = X
      BY DEF Q, ConfigDomain, R2
    <2>7. c_prev.op = [q \in ProcSet |-> PCtoOp(pc[q])]
      <3> SUFFICES ASSUME NEW q \in ProcSet, q # p
                   PROVE  pc'[q] = pc[q]
        BY DEF Q, ConfigDomain
      <3> QED
        BY <2>1 DEF TypeOK, R2
    <2>8. c_prev.arg = [q \in ProcSet |-> IF pc[q] = "RM" THEN "BOT" ELSE arg[q]]
      <3> SUFFICES ASSUME NEW q \in ProcSet, q # p
                   PROVE  pc'[q] = pc[q] /\ arg'[q] = arg[q]
        BY DEF Q, ConfigDomain
      <3> QED
        BY <2>1 DEF TypeOK, R2
    <2>9. ASSUME NEW q \in ProcSet
          PROVE  /\ pc[q] = "RM" => c_prev.res[q] = "BOT"
                 /\ pc[q] = "R1" => c_prev.res[q] = "BOT"
                 /\ pc[q] = "R2" => c_prev.res[q] = x[q]
                 /\ pc[q] = "W1" => c_prev.res[q] = "BOT"
                 /\ pc[q] = "W2" => \/ c_prev.res[q] = "BOT"
                                    \/ (c_prev.res[q] = "ACK" /\ X # x[q])
                 /\ pc[q] = "W3" => c_prev.res[q] = "ACK"
      <3> USE <2>9
      <3>1. CASE q = p
        <4> USE <3>1
        <4> SUFFICES ret'[p] = x[p]
          BY <3>1 DEF R2, Q, ConfigDomain
        <4> QED
          BY <2>1 DEF TypeOK, R2
      <3> SUFFICES ASSUME q # p
                   PROVE  pc'[q] = pc[q] /\ x'[q] = x[q] /\ X' = X
        BY <3>1 DEF Q, ConfigDomain
      <3> QED
        BY <2>1 DEF TypeOK, R2
    <2> QED
      BY <2>6, <2>7, <2>8, <2>9
  <1>2. ASSUME W3(p),
               NEW c \in ConfigDomain,
               c \in Q'
        PROVE  c \in Filter(Evolve(Q), p, ret'[p])
    <2> USE <1>2
    <2>1. TypeOK
      BY PTL
    <2>2. c.res[p] = "BOT"
      BY <2>1 DEF Q, W3, TypeOK
    <2>3. c.op[p] = "BOT"
      BY <2>1 DEF Q, W3, TypeOK, PCtoOp
    <2>4. c.arg[p] = "BOT"
      BY <2>1 DEF Q, W3, TypeOK
    <2> DEFINE c_prev == 
      [c EXCEPT !.op = [c.op EXCEPT ![p] = PCtoOp(pc[p])],
                !.arg = [c.arg EXCEPT ![p] = IF pc[p] = "RM" THEN "BOT" ELSE arg[p]],
                !.res = [c.res EXCEPT ![p] = ret'[p]]]
    <2> SUFFICES c_prev \in Q
      BY <2>2, <2>3, <2>4, EvolveAndFilterFromUnfiltered DEF Q
    <2>5. c_prev \in ConfigDomain
      <3> SUFFICES /\ PCtoOp(pc[p]) \in OpDomain
                   /\ (IF pc[p] = "RM" THEN "BOT" ELSE arg[p]) \in ArgDomain
                   /\ ret'[p] \in ResDomain
        BY DEF Q, ConfigDomain
      <3> QED
        BY <2>1 DEF TypeOK, PCtoOp, W3, OpDomain, ArgDomain, ResDomain, OpNames, LineIDs, RetsOf
    <2> SUFFICES /\ c_prev.state = X
                 /\ c_prev.op = [q \in ProcSet |-> PCtoOp(pc[q])]
                 /\ c_prev.arg = [q \in ProcSet |-> IF pc[q] = "RM" THEN "BOT" ELSE arg[q]]
                 /\ \A q \in ProcSet :
                    /\ pc[q] = "RM" => c_prev.res[q] = "BOT"
                    /\ pc[q] = "R1" => c_prev.res[q] = "BOT"
                    /\ pc[q] = "R2" => c_prev.res[q] = x[q]
                    /\ pc[q] = "W1" => c_prev.res[q] = "BOT"
                    /\ pc[q] = "W2" => \/ c_prev.res[q] = "BOT"
                                       \/ (c_prev.res[q] = "ACK" /\ X # x[q])
                    /\ pc[q] = "W3" => c_prev.res[q] = "ACK"
      BY <2>5, SMTT(30) DEF Q
    <2>6. c_prev.state = X
      BY DEF Q, ConfigDomain, W3
    <2>7. c_prev.op = [q \in ProcSet |-> PCtoOp(pc[q])]
      <3> SUFFICES ASSUME NEW q \in ProcSet, q # p
                   PROVE  pc'[q] = pc[q]
        BY DEF Q, ConfigDomain
      <3> QED
        BY <2>1 DEF TypeOK, W3
    <2>8. c_prev.arg = [q \in ProcSet |-> IF pc[q] = "RM" THEN "BOT" ELSE arg[q]]
      <3> SUFFICES ASSUME NEW q \in ProcSet, q # p
                   PROVE  pc'[q] = pc[q] /\ arg'[q] = arg[q]
        BY DEF Q, ConfigDomain
      <3> QED
        BY <2>1 DEF TypeOK, W3
    <2>9. ASSUME NEW q \in ProcSet
          PROVE  /\ pc[q] = "RM" => c_prev.res[q] = "BOT"
                 /\ pc[q] = "R1" => c_prev.res[q] = "BOT"
                 /\ pc[q] = "R2" => c_prev.res[q] = x[q]
                 /\ pc[q] = "W1" => c_prev.res[q] = "BOT"
                 /\ pc[q] = "W2" => \/ c_prev.res[q] = "BOT"
                                    \/ (c_prev.res[q] = "ACK" /\ X # x[q])
                 /\ pc[q] = "W3" => c_prev.res[q] = "ACK"
      <3> USE <2>9
      <3>1. CASE q = p
        <4> USE <3>1
        <4> SUFFICES ret'[p] = "ACK"
          BY <3>1 DEF W3, Q, ConfigDomain
        <4> QED
          BY <2>1 DEF TypeOK, W3
      <3> SUFFICES ASSUME q # p
                   PROVE  pc'[q] = pc[q] /\ x'[q] = x[q] /\ X' = X
        BY <3>1 DEF Q, ConfigDomain
      <3> QED
        BY <2>1 DEF TypeOK, W3
    <2> QED
      BY <2>6, <2>7, <2>8, <2>9
  <1> QED
    BY <1>1, <1>2, Zenon DEF ReturnAct, ReturnLines, Q

-----------------------------------------------------------------------------
(***************************************************************************)
(* Plausibility set lemma 2.5: If no variable changes, Q remains the same. *)
(***************************************************************************)
LEMMA UnchangedLemma == UNCHANGED varsP => Q' = Q
  BY DEF varsP, vars, implvars, Q

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
