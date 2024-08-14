----------------------------- MODULE MemSnap_Proof -----------------------------
EXTENDS MemSnap_Impl,
        Integers, Sequences, FiniteSets, Permutations,
        TLAPS
INSTANCE Augmentation \* Sets constants BOT, ConfigDomain, Delta(_, _, _), ProcSet 
                      \* in Augmentation, to those specified in Checkpointable_Type
                      \* which itself is imported by extending CptableJJJ_Implementation

VARIABLES P, xhat
vars == algvars \o <<pc, arg, ret, P, xhat>>

ASSUME BotDef == /\ BOT \notin OpNames
                 /\ BOT \notin WordDomain
                 /\ BOT # ACK
                 
ASSUME RemDef == RemainderID = "L0"

\* Augmented initial state
AInit == /\ Init
         /\ xhat = [p \in ProcSet |-> 0]
         /\ P = {[state |-> InitState,
                  op    |-> [p \in ProcSet |-> BOT],
                  arg   |-> [p \in ProcSet |-> BOT],
                  res   |-> [p \in ProcSet |-> BOT]]}
                 
L0(p) == /\ pc[p] = RemainderID
         /\ \E op \in OpNames :
            /\ pc' = [pc EXCEPT ![p] = OpToInvocLine(op)]
            /\ \E arg_val \in ArgsOf(op) : 
               /\ arg' = [arg EXCEPT ![p] = arg_val]
               /\ P' = Evolve(Invoke(P, p, op, arg_val))
               /\ xhat' = [xhat EXCEPT ![p] = X]
         /\ UNCHANGED algvars
         /\ UNCHANGED ret

IntLine(p) == \E Line \in IntLines(p) : /\ Line
                                        /\ P' = Evolve(P)
                                        /\ xhat' = xhat
                                        
RetLine(p) == \E Line \in RetLines(p) : /\ Line
                                        /\ P' = Filter(Evolve(P), p, ret'[p])
                                        /\ xhat' = xhat

Next == \E p \in ProcSet : \/ L0(p)
                           \/ IntLine(p)
                           \/ RetLine(p)

Spec == AInit /\ [][Next]_vars

\* Type correctness
PTypeOK == P \in SUBSET ConfigDomain

\* StateDomain is not empty
LEMMA StateDomainNE == StateDomain # {}
  <1>1. PICK word \in WordDomain : TRUE
    BY WordDomainNE
  <1> DEFINE state == [val  |-> [i \in 1..M |-> word],
                       snap |-> [i \in 1..M |-> word]]
  <1>2. state \in StateDomain
    BY <1>1 DEF StateDomain
  <1> QED  BY <1>2

\* There is indeed an initial state 
\* (it is defined via Hilbert's epsilon so existence is needed to guarantee well-definedness)
LEMMA InitStateExists == \E state \in StateDomain : state.val = state.snap
  <1>1. PICK st \in StateDomain : TRUE
    BY StateDomainNE
  <1> DEFINE state == [val  |-> st.val,
                       snap |-> st.val]
  <1>2. state \in StateDomain
    BY <1>1 DEF StateDomain 
  <1> QED  BY <1>2

\* Type correctness of P held by the initial state (of augmented specification)
LEMMA InitPTypeOK == AInit => PTypeOK
  <1> SUFFICES ASSUME AInit,
                      NEW c \in P
               PROVE  /\ c.state \in StateDomain
                      /\ c.op \in [ProcSet -> OpDomain]
                      /\ c.arg \in [ProcSet -> ArgDomain]
                      /\ c.res \in [ProcSet -> ResDomain]
    BY DEF AInit, PTypeOK, ConfigDomain
  <1>1. c.state \in StateDomain
    BY InitStateExists DEF AInit, InitState
  <1>2. c.op \in [ProcSet -> OpDomain]
    BY DEF OpDomain, AInit
  <1>3. c.arg \in [ProcSet -> ArgDomain]
    BY DEF ArgDomain, AInit
  <1>4. c.res \in [ProcSet -> ResDomain]
    BY DEF ResDomain, AInit
  <1> QED
    BY <1>1, <1>2, <1>3, <1>4

\* Type correctness of P preserved by the next-state relation
LEMMA NextPTypeOK == PTypeOK /\ [Next]_vars => PTypeOK'
  <1> USE DEF PTypeOK, ConfigDomain, OpDomain, ArgDomain, ResDomain, StateDomain
  <1> SUFFICES ASSUME PTypeOK,
                      [Next]_vars
               PROVE  PTypeOK'
    OBVIOUS
  <1>1. CASE Next
    <2>1. ASSUME NEW p \in ProcSet, 
                 L0(p)
          PROVE  PTypeOK'
      BY <2>1 DEF L0, Evolve, Invoke
    <2>2. ASSUME NEW p \in ProcSet, 
                 IntLine(p)
          PROVE  PTypeOK'
      <3> SUFFICES ASSUME NEW Line \in IntLines(p),
                          Line,
                          P' = Evolve(P)
                   PROVE  PTypeOK'
        BY <2>2, Zenon DEF IntLine
      <3> USE DEF Evolve
      <3>1.  CASE Line = C1(p)  BY <3>1  DEF C1
      <3>2.  CASE Line = O1A(p) BY <3>2  DEF O1A
      <3>3.  CASE Line = O1B(p) BY <3>3  DEF O1B
      <3>4.  CASE Line = O1C(p) BY <3>4  DEF O1C
      <3>5.  CASE Line = O1D(p) BY <3>5  DEF O1D
      <3>6.  CASE Line = O2(p)  BY <3>6  DEF O2
      <3>7.  CASE Line = U1A(p) BY <3>7  DEF U1A
      <3>8.  CASE Line = U1B(p) BY <3>8  DEF U1B
      <3>9.  CASE Line = U1C(p) BY <3>9  DEF U1C
      <3>10. CASE Line = U1D(p) BY <3>10 DEF U1D
      <3>11. CASE Line = U2(p)  BY <3>11 DEF U2
      <3> QED
        BY Zenon, <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9, <3>10, <3>11
    <2>3. ASSUME NEW p \in ProcSet, 
                 RetLine(p)
          PROVE  PTypeOK'
      <3> SUFFICES ASSUME NEW Line \in RetLines(p),
                          Line,
                          P' = Filter(Evolve(P), p, ret'[p])
                   PROVE  PTypeOK'
        BY <2>3, Zenon DEF RetLine
      <3> USE DEF Evolve, Filter
      <3>1. CASE Line = C2(p) BY <3>1 DEF C2
      <3>2. CASE Line = O3(p) BY <3>2 DEF O3
      <3>3. CASE Line = U3(p) BY <3>3 DEF U3
      <3> QED
        BY Zenon, <3>1, <3>2, <3>3 DEF RetLines
    <2> QED
      BY <1>1, <2>1, <2>2, <2>3 DEF Next
  <1>2. CASE UNCHANGED vars
    BY <1>2 DEF vars, algvars
  <1> QED
    BY <1>1, <1>2

TypeOK == /\ pc \in [ProcSet -> LineIDs]
          /\ A \in [1..M -> WordDomain]
          /\ B \in [1..M -> [val: WordDomain, seq: Nat]]
          /\ X \in Nat
          /\ a \in [ProcSet -> WordDomain]
          /\ b \in [ProcSet -> [val: WordDomain, seq: Nat]]
          /\ x \in [ProcSet -> Nat]
          /\ k \in [ProcSet -> 1..3]
          /\ \A p \in ProcSet : pc[p] \in {"O1B", "O1C", "O1D", "U1B", "U1C", "U1D"}
                                => k[p] \in 1..2
          /\ r \in [ProcSet -> WordDomain \union UOpRetDomain]
          /\ arg \in [ProcSet -> ArgDomain]
          /\ ret \in [ProcSet -> ResDomain]
          /\ xhat \in [ProcSet -> Nat]
          /\ \A p \in ProcSet : (pc[p] # RemainderID) => arg[p] \in ArgsOf(LineIDtoOp(pc[p]))

LEMMA InitTypeOK == AInit => TypeOK
  <1> SUFFICES ASSUME AInit
               PROVE  TypeOK
    OBVIOUS
  <1> USE RemDef, InitPTypeOK, InitStateExists
      DEF TypeOK, AInit, Init, InitState, LineIDs, StateDomain
  <1>1. pc \in [ProcSet -> LineIDs]
    OBVIOUS
  <1>2. A \in [1..M -> WordDomain]
    OBVIOUS
  <1>3. B \in [1..M -> [val: WordDomain, seq: Nat]]  
    OBVIOUS
  <1>4. X \in Nat
    OBVIOUS
  <1>5. a \in [ProcSet -> WordDomain]
    OBVIOUS
  <1>6. b \in [ProcSet -> [val: WordDomain, seq: Nat]]
    OBVIOUS      
  <1>7. x \in [ProcSet -> Nat]
    OBVIOUS
  <1>8. k \in [ProcSet -> 1..3]
    OBVIOUS
  <1>9. \A p \in ProcSet : pc[p] \in {"O1B", "O1C", "O1D", "U1B", "U1C", "U1D"} => k[p] \in 1..2
    OBVIOUS
  <1>10. r \in [ProcSet -> WordDomain \union UOpRetDomain]
    OBVIOUS
  <1>11. arg \in [ProcSet -> ArgDomain]
    OBVIOUS
  <1>12. ret \in [ProcSet -> ResDomain]
    OBVIOUS
  <1>13. xhat \in [ProcSet -> Nat]
    OBVIOUS
  <1>14. \A p \in ProcSet : (pc[p] # RemainderID) => arg[p] \in ArgsOf(LineIDtoOp(pc[p]))
    OBVIOUS  
  <1> QED
    BY <1>1, <1>11, <1>12, <1>13, <1>14, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10 DEF TypeOK

LEMMA NextTypeOK == TypeOK /\ [Next]_vars => TypeOK'
  <1> SUFFICES ASSUME TypeOK, [Next]_vars
               PROVE  TypeOK'
    OBVIOUS
  <1>1. CASE Next
    <2>1. ASSUME NEW p \in ProcSet, 
                 L0(p)
          PROVE  TypeOK'
      <3> USE RemDef DEF TypeOK, algvars, L0
      <3>1. (pc \in [ProcSet -> LineIDs])'
        BY <2>1 DEF OpNames, OpToInvocLine, LineIDs
      <3>2. (A \in [1..M -> WordDomain])'
        BY <2>1
      <3>3. (B \in [1..M -> [val: WordDomain, seq: Nat]])'
        BY <2>1
      <3>4. (X \in Nat)'
        BY <2>1
      <3>5. (a \in [ProcSet -> WordDomain])'
        BY <2>1
      <3>6. (b \in [ProcSet -> [val: WordDomain, seq: Nat]])'
        BY <2>1
      <3>7. (x \in [ProcSet -> Nat])'
        BY <2>1
      <3>8. (k \in [ProcSet -> 1..3])'
        BY <2>1
      <3>9. (\A p_1 \in ProcSet : pc[p_1] \in {"O1B", "O1C", "O1D", "U1B", "U1C", "U1D"}
                                  => k[p_1] \in 1..2)'
        BY <2>1
      <3>10. (r \in [ProcSet -> WordDomain \union UOpRetDomain])'
        BY <2>1
      <3>11. (arg \in [ProcSet -> ArgDomain])'
        BY <2>1 DEF ArgDomain, ArgsOf, OpNames
      <3>12. (ret \in [ProcSet -> ResDomain])'
        BY <2>1
      <3>13. (xhat \in [ProcSet -> Nat])'
        BY <2>1
      <3>14. (\A p_1 \in ProcSet : (pc[p_1] # RemainderID) => arg[p_1] \in ArgsOf(LineIDtoOp(pc[p_1])))'
        <4> USE <2>1
        <4> SUFFICES arg'[p] \in ArgsOf(LineIDtoOp(pc'[p]))
          BY <2>1, Zenon
\*        <4>1. 
        <4> QED
      <3>15. QED
        BY <3>1, <3>10, <3>11, <3>12, <3>13, <3>14, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9 DEF TypeOK
    <2>2. ASSUME NEW p \in ProcSet, 
                 IntLine(p)
          PROVE  TypeOK'
      <3> SUFFICES ASSUME NEW Line \in IntLines(p),
                          Line,
                          P' = Evolve(P),
                          xhat' = xhat
                   PROVE  TypeOK'
        BY <2>2, Zenon DEF IntLine
      <3> USE RemDef DEF TypeOK
      <3>1. CASE Line = C1(p)
        <4>1. (pc \in [ProcSet -> LineIDs])'
          BY <3>1, Zenon DEF C1, LineIDs
        <4>2. (A \in [1..M -> WordDomain])'
          BY <3>1 DEF C1
        <4>3. (B \in [1..M -> [val: WordDomain, seq: Nat]])'
          BY <3>1 DEF C1
        <4>4. (X \in Nat)'
          BY <3>1, Isa DEF C1
        <4>5. (a \in [ProcSet -> WordDomain])'
          BY <3>1 DEF C1
        <4>6. (b \in [ProcSet -> [val: WordDomain, seq: Nat]])'
          BY <3>1 DEF C1
        <4>7. (x \in [ProcSet -> Nat])'
          BY <3>1 DEF C1
        <4>8. (k \in [ProcSet -> 1..3])'
          BY <3>1 DEF C1
        <4>9. (\A p_1 \in ProcSet : pc[p_1] \in {"O1B", "O1C", "O1D", "U1B", "U1C", "U1D"} => k[p_1] \in 1..2)'
          BY <3>1, Zenon DEF C1
        <4>10. (r \in [ProcSet -> WordDomain \union UOpRetDomain])'
          BY <3>1 DEF C1
        <4>11. (arg \in [ProcSet -> ArgDomain])'
          BY <3>1 DEF C1
        <4>12. (ret \in [ProcSet -> ResDomain])'
          BY <3>1, Zenon DEF C1
        <4>13. (xhat \in [ProcSet -> Nat])'
          BY <3>1 DEF C1
        <4>14. (\A p_1 \in ProcSet : (pc[p_1] # RemainderID) => arg[p_1] \in ArgsOf(LineIDtoOp(pc[p_1])))'
          BY <3>1, RemDef, ZenonT(90) DEF C1, LineIDtoOp
        <4>15. QED
          BY <4>1, <4>11, <4>12, <4>13, <4>14, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, <4>10 DEF TypeOK
      <3>2. CASE Line = O1A(p)
        <4>1. (pc \in [ProcSet -> LineIDs])'
          BY <3>2, Zenon DEF O1A, LineIDs
        <4>2. (A \in [1..M -> WordDomain])'
          BY <3>2 DEF O1A
        <4>3. (B \in [1..M -> [val: WordDomain, seq: Nat]])'
          BY <3>2 DEF O1A
        <4>4. (X \in Nat)'
          BY <3>2, Isa DEF O1A
        <4>5. (a \in [ProcSet -> WordDomain])'
          BY <3>2 DEF O1A
        <4>6. (b \in [ProcSet -> [val: WordDomain, seq: Nat]])'
          <5> USE <3>2 DEF O1A
          <5> SUFFICES B[arg[p].i] \in [val: WordDomain, seq: Nat]
            BY Zenon
          <5> SUFFICES arg[p].i \in 1..M
            BY Zenon
          <5> QED
            BY Zenon DEF LineIDtoOp, ArgsOf
        <4>7. (x \in [ProcSet -> Nat])'
          BY <3>2 DEF O1A
        <4>8. (k \in [ProcSet -> 1..3])'
          <5> USE <3>2 DEF O1A
          <5> SUFFICES k'[p] \in 1..3
            BY Zenon
          <5>1. k'[p] = 1 \/ k'[p] = k[p]
            BY Zenon
          <5> QED
            BY <5>1
        <4>9. (\A p_1 \in ProcSet : pc[p_1] \in {"O1B", "O1C", "O1D", "U1B", "U1C", "U1D"} => k[p_1] \in 1..2)'
          <5> USE <3>2 DEF O1A
          <5> SUFFICES ASSUME pc'[p] = "O1B"
                       PROVE  k'[p] \in 1..2
            BY Zenon
          <5>1. ~(k[p] > 2)
            BY Zenon
          <5>2. k[p] \in 1..2
            BY <5>1
          <5> QED
            BY <5>2, Zenon
        <4>10. (r \in [ProcSet -> WordDomain \union UOpRetDomain])'
          BY <3>2 DEF O1A
        <4>11. (arg \in [ProcSet -> ArgDomain])'
          BY <3>2 DEF O1A
        <4>12. (ret \in [ProcSet -> ResDomain])'
          BY <3>2, Zenon DEF O1A
        <4>13. (xhat \in [ProcSet -> Nat])'
          BY <3>2 DEF O1A
        <4>14. (\A p_1 \in ProcSet : (pc[p_1] # RemainderID) => arg[p_1] \in ArgsOf(LineIDtoOp(pc[p_1])))'
          BY <3>2, Zenon DEF O1A, LineIDtoOp
        <4>15. QED
          BY <4>1, <4>11, <4>12, <4>13, <4>14, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, <4>10 DEF TypeOK
      <3>3. CASE Line = O1B(p)
        <4>1. (pc \in [ProcSet -> LineIDs])'
          BY <3>3, Zenon DEF O1B, LineIDs
        <4>2. (A \in [1..M -> WordDomain])'
          BY <3>3 DEF O1B
        <4>3. (B \in [1..M -> [val: WordDomain, seq: Nat]])'
          BY <3>3 DEF O1B
        <4>4. (X \in Nat)'
          BY <3>3, Isa DEF O1B
        <4>5. (a \in [ProcSet -> WordDomain])'
          BY <3>3 DEF O1B
        <4>6. (b \in [ProcSet -> [val: WordDomain, seq: Nat]])'
          BY <3>3 DEF O1B
        <4>7. (x \in [ProcSet -> Nat])'
          BY <3>3 DEF O1B
        <4>8. (k \in [ProcSet -> 1..3])'
          <5> USE <3>3 DEF O1B
          <5> SUFFICES k'[p] \in 1..3
            BY Zenon
          <5>1. k'[p] = 1 \/ k'[p] = k[p]
            BY Zenon
          <5> QED
            BY <5>1
        <4>9. (\A p_1 \in ProcSet : pc[p_1] \in {"O1B", "O1C", "O1D", "U1B", "U1C", "U1D"} => k[p_1] \in 1..2)'
          BY <3>3, Zenon DEF O1B
        <4>10. (r \in [ProcSet -> WordDomain \union UOpRetDomain])'
          BY <3>3 DEF O1B
        <4>11. (arg \in [ProcSet -> ArgDomain])'
          BY <3>3 DEF O1B
        <4>12. (ret \in [ProcSet -> ResDomain])'
          BY <3>3, Zenon DEF O1B
        <4>13. (xhat \in [ProcSet -> Nat])'
          BY <3>3 DEF O1B
        <4>14. (\A p_1 \in ProcSet : (pc[p_1] # RemainderID) => arg[p_1] \in ArgsOf(LineIDtoOp(pc[p_1])))'
          BY <3>3, RemDef, ZenonT(90) DEF O1B, LineIDtoOp
        <4>15. QED
          BY <4>1, <4>11, <4>12, <4>13, <4>14, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, <4>10 DEF TypeOK
      <3>4. CASE Line = O1C(p)
        <4>1. (pc \in [ProcSet -> LineIDs])'
          BY <3>4, Zenon DEF O1C, LineIDs
        <4>2. (A \in [1..M -> WordDomain])'
          BY <3>4 DEF O1C
        <4>3. (B \in [1..M -> [val: WordDomain, seq: Nat]])'
          BY <3>4 DEF O1C
        <4>4. (X \in Nat)'
          BY <3>4, Isa DEF O1C
        <4>5. (a \in [ProcSet -> WordDomain])'
          <5> USE <3>4 DEF O1C
          <5> SUFFICES A[arg[p].i] \in WordDomain
            BY Zenon
          <5> SUFFICES arg[p].i \in 1..M
            BY Zenon
          <5> QED
            BY Zenon DEF LineIDtoOp, ArgsOf
        <4>6. (b \in [ProcSet -> [val: WordDomain, seq: Nat]])'
          BY <3>4 DEF O1C
        <4>7. (x \in [ProcSet -> Nat])'
          BY <3>4 DEF O1C
        <4>8. (k \in [ProcSet -> 1..3])'
          BY <3>4 DEF O1C
        <4>9. (\A p_1 \in ProcSet : pc[p_1] \in {"O1B", "O1C", "O1D", "U1B", "U1C", "U1D"} => k[p_1] \in 1..2)'
          BY <3>4, Zenon DEF O1C
        <4>10. (r \in [ProcSet -> WordDomain \union UOpRetDomain])'
          BY <3>4 DEF O1C
        <4>11. (arg \in [ProcSet -> ArgDomain])'
          BY <3>4 DEF O1C
        <4>12. (ret \in [ProcSet -> ResDomain])'
          BY <3>4, Zenon DEF O1C
        <4>13. (xhat \in [ProcSet -> Nat])'
          BY <3>4 DEF O1C
        <4>14. (\A p_1 \in ProcSet : (pc[p_1] # RemainderID) => arg[p_1] \in ArgsOf(LineIDtoOp(pc[p_1])))'
          BY <3>4, RemDef, ZenonT(90) DEF O1C, LineIDtoOp
        <4>15. QED
          BY <4>1, <4>11, <4>12, <4>13, <4>14, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, <4>10 DEF TypeOK
      <3>5. CASE Line = O1D(p)
        <4>1. (pc \in [ProcSet -> LineIDs])'
          BY <3>5, Zenon DEF O1D, LineIDs
        <4>2. (A \in [1..M -> WordDomain])'
          BY <3>5 DEF O1D
        <4>3. (B \in [1..M -> [val: WordDomain, seq: Nat]])'
          <5> USE <3>5 DEF O1D
          <5>A. \A idx \in 1..M : idx # arg[p].i => B'[idx] = B[idx]
            BY Zenon
          <5> SUFFICES B'[arg[p].i] \in [val: WordDomain, seq: Nat]
            BY <5>A, Zenon
          <5> SUFFICES /\ arg[p].i \in 1..M
                       /\ [val |-> a[p], seq |-> x[p]] \in [val: WordDomain, seq: Nat]
            BY Zenon
          <5> SUFFICES /\ arg[p].i \in 1..M
                       /\ a[p] \in WordDomain
                       /\ x[p] \in Nat
            OBVIOUS
          <5> QED
            BY Zenon DEF LineIDtoOp, ArgsOf
        <4>4. (X \in Nat)'
          BY <3>5, Isa DEF O1D
        <4>5. (a \in [ProcSet -> WordDomain])'
          BY <3>5 DEF O1D
        <4>6. (b \in [ProcSet -> [val: WordDomain, seq: Nat]])'
          BY <3>5 DEF O1D
        <4>7. (x \in [ProcSet -> Nat])'
          BY <3>5 DEF O1D
        <4>8. (k \in [ProcSet -> 1..3])'
          <5> USE <3>5 DEF O1D
          <5> SUFFICES k'[p] \in 1..3
            BY Zenon
          <5>1. k'[p] = 1 \/ k'[p] = k[p]+1
            BY Zenon
          <5>2. k[p] \in 1..2
            BY Zenon
          <5> QED
            BY <5>1, <5>2
        <4>9. (\A p_1 \in ProcSet : pc[p_1] \in {"O1B", "O1C", "O1D", "U1B", "U1C", "U1D"} => k[p_1] \in 1..2)'
          BY <3>5, Zenon DEF O1D
        <4>10. (r \in [ProcSet -> WordDomain \union UOpRetDomain])'
          BY <3>5 DEF O1D
        <4>11. (arg \in [ProcSet -> ArgDomain])'
          BY <3>5 DEF O1D
        <4>12. (ret \in [ProcSet -> ResDomain])'
          BY <3>5, Zenon DEF O1D
        <4>13. (xhat \in [ProcSet -> Nat])'
          BY <3>5 DEF O1D
        <4>14. (\A p_1 \in ProcSet : (pc[p_1] # RemainderID) => arg[p_1] \in ArgsOf(LineIDtoOp(pc[p_1])))'
          BY <3>5, RemDef, ZenonT(90) DEF O1D, LineIDtoOp
        <4>15. QED
          BY <4>1, <4>11, <4>12, <4>13, <4>14, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, <4>10 DEF TypeOK
      <3>6. CASE Line = O2(p)
        <4>1. (pc \in [ProcSet -> LineIDs])'
          BY <3>6, Zenon DEF O2, LineIDs
        <4>2. (A \in [1..M -> WordDomain])'
          BY <3>6 DEF O2
        <4>3. (B \in [1..M -> [val: WordDomain, seq: Nat]])'
          BY <3>6 DEF O2
        <4>4. (X \in Nat)'
          BY <3>6, Isa DEF O2
        <4>5. (a \in [ProcSet -> WordDomain])'
          BY <3>6 DEF O2
        <4>6. (b \in [ProcSet -> [val: WordDomain, seq: Nat]])'
          BY <3>6 DEF O2
        <4>7. (x \in [ProcSet -> Nat])'
          BY <3>6 DEF O2
        <4>8. (k \in [ProcSet -> 1..3])'
          BY <3>6 DEF O2
        <4>9. (\A p_1 \in ProcSet : pc[p_1] \in {"O1B", "O1C", "O1D", "U1B", "U1C", "U1D"} => k[p_1] \in 1..2)'
          BY <3>6, Zenon DEF O2
        <4>10. (r \in [ProcSet -> WordDomain \union UOpRetDomain])'
          <5> USE <3>6 DEF O2
          <5> SUFFICES B[arg[p].i].val \in WordDomain \union UOpRetDomain
            BY Zenon
          <5> SUFFICES arg[p].i \in 1..M
            OBVIOUS
          <5> QED
            BY Zenon DEF LineIDtoOp, ArgsOf
        <4>11. (arg \in [ProcSet -> ArgDomain])'
          BY <3>6 DEF O2
        <4>12. (ret \in [ProcSet -> ResDomain])'
          BY <3>6, Zenon DEF O2
        <4>13. (xhat \in [ProcSet -> Nat])'
          BY <3>6 DEF O2
        <4>14. (\A p_1 \in ProcSet : (pc[p_1] # RemainderID) => arg[p_1] \in ArgsOf(LineIDtoOp(pc[p_1])))'
          BY <3>6, RemDef, ZenonT(90) DEF O2, LineIDtoOp
        <4>15. QED
          BY <4>1, <4>11, <4>12, <4>13, <4>14, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, <4>10 DEF TypeOK
      <3>7. CASE Line = U1A(p)
        <4>1. (pc \in [ProcSet -> LineIDs])'
          BY <3>7, Zenon DEF U1A, LineIDs
        <4>2. (A \in [1..M -> WordDomain])'
          BY <3>7 DEF U1A
        <4>3. (B \in [1..M -> [val: WordDomain, seq: Nat]])'
          BY <3>7 DEF U1A
        <4>4. (X \in Nat)'
          BY <3>7, Isa DEF U1A
        <4>5. (a \in [ProcSet -> WordDomain])'
          BY <3>7 DEF U1A
        <4>6. (b \in [ProcSet -> [val: WordDomain, seq: Nat]])'
          <5> USE <3>7 DEF U1A
          <5> SUFFICES B[arg[p].i] \in [val: WordDomain, seq: Nat]
            BY Zenon
          <5> SUFFICES arg[p].i \in 1..M
            BY Zenon
          <5> QED
            BY Zenon DEF LineIDtoOp, ArgsOf
        <4>7. (x \in [ProcSet -> Nat])'
          BY <3>7 DEF U1A
        <4>8. (k \in [ProcSet -> 1..3])'
          <5> USE <3>7 DEF U1A
          <5> SUFFICES k'[p] \in 1..3
            BY Zenon
          <5>1. k'[p] = 1 \/ k'[p] = k[p]
            BY Zenon
          <5> QED
            BY <5>1
        <4>9. (\A p_1 \in ProcSet : pc[p_1] \in {"O1B", "O1C", "O1D", "U1B", "U1C", "U1D"} => k[p_1] \in 1..2)'
          <5> USE <3>7 DEF U1A
          <5> SUFFICES ASSUME pc'[p] = "U1B"
                       PROVE  k'[p] \in 1..2
            BY Zenon
          <5>1. ~(k[p] > 2)
            BY Zenon
          <5>2. k[p] \in 1..2
            BY <5>1
          <5> QED
            BY <5>2, Zenon
        <4>10. (r \in [ProcSet -> WordDomain \union UOpRetDomain])'
          BY <3>7 DEF U1A
        <4>11. (arg \in [ProcSet -> ArgDomain])'
          BY <3>7 DEF U1A
        <4>12. (ret \in [ProcSet -> ResDomain])'
          BY <3>7, Zenon DEF U1A
        <4>13. (xhat \in [ProcSet -> Nat])'
          BY <3>7 DEF U1A
        <4>14. (\A p_1 \in ProcSet : (pc[p_1] # RemainderID) => arg[p_1] \in ArgsOf(LineIDtoOp(pc[p_1])))'
          BY <3>7, Zenon DEF U1A, LineIDtoOp
        <4>15. QED
          BY <4>1, <4>11, <4>12, <4>13, <4>14, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, <4>10 DEF TypeOK
      <3>8. CASE Line = U1B(p)
        <4>1. (pc \in [ProcSet -> LineIDs])'
          BY <3>8, Zenon DEF U1B, LineIDs
        <4>2. (A \in [1..M -> WordDomain])'
          BY <3>8 DEF U1B
        <4>3. (B \in [1..M -> [val: WordDomain, seq: Nat]])'
          BY <3>8 DEF U1B
        <4>4. (X \in Nat)'
          BY <3>8, Isa DEF U1B
        <4>5. (a \in [ProcSet -> WordDomain])'
          BY <3>8 DEF U1B
        <4>6. (b \in [ProcSet -> [val: WordDomain, seq: Nat]])'
          BY <3>8 DEF U1B
        <4>7. (x \in [ProcSet -> Nat])'
          BY <3>8 DEF U1B
        <4>8. (k \in [ProcSet -> 1..3])'
          <5> USE <3>8 DEF U1B
          <5> SUFFICES k'[p] \in 1..3
            BY Zenon
          <5>1. k'[p] = 1 \/ k'[p] = k[p]
            BY Zenon
          <5> QED
            BY <5>1
        <4>9. (\A p_1 \in ProcSet : pc[p_1] \in {"O1B", "O1C", "O1D", "U1B", "U1C", "U1D"} => k[p_1] \in 1..2)'
          BY <3>8, Zenon DEF U1B
        <4>10. (r \in [ProcSet -> WordDomain \union UOpRetDomain])'
          BY <3>8 DEF U1B
        <4>11. (arg \in [ProcSet -> ArgDomain])'
          BY <3>8 DEF U1B
        <4>12. (ret \in [ProcSet -> ResDomain])'
          BY <3>8, Zenon DEF U1B
        <4>13. (xhat \in [ProcSet -> Nat])'
          BY <3>8 DEF U1B
        <4>14. (\A p_1 \in ProcSet : (pc[p_1] # RemainderID) => arg[p_1] \in ArgsOf(LineIDtoOp(pc[p_1])))'
          BY <3>8, RemDef, ZenonT(90) DEF U1B, LineIDtoOp
        <4>15. QED
          BY <4>1, <4>11, <4>12, <4>13, <4>14, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, <4>10 DEF TypeOK
      <3>9. CASE Line = U1C(p)
        <4>1. (pc \in [ProcSet -> LineIDs])'
          BY <3>9, Zenon DEF U1C, LineIDs
        <4>2. (A \in [1..M -> WordDomain])'
          BY <3>9 DEF U1C
        <4>3. (B \in [1..M -> [val: WordDomain, seq: Nat]])'
          BY <3>9 DEF U1C
        <4>4. (X \in Nat)'
          BY <3>9, Isa DEF U1C
        <4>5. (a \in [ProcSet -> WordDomain])'
          <5> USE <3>9 DEF U1C
          <5> SUFFICES A[arg[p].i] \in WordDomain
            BY Zenon
          <5> SUFFICES arg[p].i \in 1..M
            BY Zenon
          <5> QED
            BY Zenon DEF LineIDtoOp, ArgsOf
        <4>6. (b \in [ProcSet -> [val: WordDomain, seq: Nat]])'
          BY <3>9 DEF U1C
        <4>7. (x \in [ProcSet -> Nat])'
          BY <3>9 DEF U1C
        <4>8. (k \in [ProcSet -> 1..3])'
          BY <3>9 DEF U1C
        <4>9. (\A p_1 \in ProcSet : pc[p_1] \in {"O1B", "O1C", "O1D", "U1B", "U1C", "U1D"} => k[p_1] \in 1..2)'
          BY <3>9, Zenon DEF U1C
        <4>10. (r \in [ProcSet -> WordDomain \union UOpRetDomain])'
          BY <3>9 DEF U1C
        <4>11. (arg \in [ProcSet -> ArgDomain])'
          BY <3>9 DEF U1C
        <4>12. (ret \in [ProcSet -> ResDomain])'
          BY <3>9, Zenon DEF U1C
        <4>13. (xhat \in [ProcSet -> Nat])'
          BY <3>9 DEF U1C
        <4>14. (\A p_1 \in ProcSet : (pc[p_1] # RemainderID) => arg[p_1] \in ArgsOf(LineIDtoOp(pc[p_1])))'
          BY <3>9, RemDef, ZenonT(90) DEF U1C, LineIDtoOp
        <4>15. QED
          BY <4>1, <4>11, <4>12, <4>13, <4>14, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, <4>10 DEF TypeOK
      <3>10. CASE Line = U1D(p)
        <4>1. (pc \in [ProcSet -> LineIDs])'
          BY <3>10, Zenon DEF U1D, LineIDs
        <4>2. (A \in [1..M -> WordDomain])'
          BY <3>10 DEF U1D
        <4>3. (B \in [1..M -> [val: WordDomain, seq: Nat]])'
          <5> USE <3>10 DEF U1D
          <5>1. \A idx \in 1..M : idx # arg[p].i => B'[idx] = B[idx]
            BY Zenon
          <5> SUFFICES B'[arg[p].i] \in [val: WordDomain, seq: Nat]
            BY <5>1, Zenon
          <5> SUFFICES /\ arg[p].i \in 1..M
                       /\ [val |-> a[p], seq |-> x[p]] \in [val: WordDomain, seq: Nat]
            BY Zenon
          <5> SUFFICES /\ arg[p].i \in 1..M
                       /\ a[p] \in WordDomain
                       /\ x[p] \in Nat
            OBVIOUS
          <5> QED
            BY Zenon DEF LineIDtoOp, ArgsOf
        <4>4. (X \in Nat)'
          BY <3>10, Isa DEF U1D
        <4>5. (a \in [ProcSet -> WordDomain])'
          BY <3>10 DEF U1D
        <4>6. (b \in [ProcSet -> [val: WordDomain, seq: Nat]])'
          BY <3>10 DEF U1D
        <4>7. (x \in [ProcSet -> Nat])'
          BY <3>10 DEF U1D
        <4>8. (k \in [ProcSet -> 1..3])'
          <5> USE <3>10 DEF U1D
          <5> SUFFICES k'[p] \in 1..3
            BY Zenon
          <5>1. k'[p] = 1 \/ k'[p] = k[p]+1
            BY Zenon
          <5>2. k[p] \in 1..2
            BY Zenon
          <5> QED
            BY <5>1, <5>2
        <4>9. (\A p_1 \in ProcSet : pc[p_1] \in {"O1B", "O1C", "O1D", "U1B", "U1C", "U1D"} => k[p_1] \in 1..2)'
          BY <3>10, Zenon DEF U1D
        <4>10. (r \in [ProcSet -> WordDomain \union UOpRetDomain])'
          BY <3>10 DEF U1D
        <4>11. (arg \in [ProcSet -> ArgDomain])'
          BY <3>10 DEF U1D
        <4>12. (ret \in [ProcSet -> ResDomain])'
          BY <3>10, Zenon DEF U1D
        <4>13. (xhat \in [ProcSet -> Nat])'
          BY <3>10 DEF U1D
        <4>14. (\A p_1 \in ProcSet : (pc[p_1] # RemainderID) => arg[p_1] \in ArgsOf(LineIDtoOp(pc[p_1])))'
          BY <3>10, RemDef, ZenonT(90) DEF U1D, LineIDtoOp
        <4>15. QED
          BY <4>1, <4>11, <4>12, <4>13, <4>14, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, <4>10 DEF TypeOK
      <3>11. CASE Line = U2(p)
        <4>1. (pc \in [ProcSet -> LineIDs])'
          BY <3>11, Zenon DEF U2, LineIDs
        <4>2. (A \in [1..M -> WordDomain])'
          <5> USE <3>11 DEF U2
          <5>1. \A idx \in 1..M : idx # arg[p].i => A'[idx] = A[idx]
            BY Zenon
          <5> SUFFICES A'[arg[p].i] \in WordDomain
            BY <5>1, Zenon
          <5> SUFFICES /\ arg[p].i \in 1..M
                       /\ arg[p].uop[A[arg[p].i]][1] \in WordDomain
            BY Zenon
          <5>2. /\ arg[p].i \in 1..M
                /\ arg[p].uop \in UOpSet
            BY Zenon DEF LineIDtoOp, ArgsOf
          <5> PICK RetValues : /\ RetValues # {}
                               /\ UOpSet \in SUBSET [WordDomain -> WordDomain \X RetValues]
            BY UOpSet_WF, Zenon
          <5>3. arg[p].uop[A[arg[p].i]][1] \in WordDomain
            BY <5>2
          <5> QED 
            BY <5>2, <5>3
        <4>3. (B \in [1..M -> [val: WordDomain, seq: Nat]])'
          BY <3>11 DEF U2
        <4>4. (X \in Nat)'
          BY <3>11, Isa DEF U2
        <4>5. (a \in [ProcSet -> WordDomain])'
          BY <3>11 DEF U2
        <4>6. (b \in [ProcSet -> [val: WordDomain, seq: Nat]])'
          BY <3>11 DEF U2
        <4>7. (x \in [ProcSet -> Nat])'
          BY <3>11 DEF U2
        <4>8. (k \in [ProcSet -> 1..3])'
          BY <3>11 DEF U2
        <4>9. (\A p_1 \in ProcSet : pc[p_1] \in {"O1B", "O1C", "O1D", "U1B", "U1C", "U1D"} => k[p_1] \in 1..2)'
          BY <3>11, Zenon DEF U2
        <4>10. (r \in [ProcSet -> WordDomain \union UOpRetDomain])'
          <5> USE <3>11 DEF U2
          <5> SUFFICES arg[p].uop[A[arg[p].i]][2] \in WordDomain \union UOpRetDomain
            BY Zenon
          <5>2. /\ arg[p].i \in 1..M
                /\ arg[p].uop \in UOpSet
            BY Zenon DEF LineIDtoOp, ArgsOf
          <5> PICK RetValues : /\ RetValues # {}
                               /\ UOpSet \in SUBSET [WordDomain -> WordDomain \X RetValues]
            BY UOpSet_WF, Zenon
          <5>3. arg[p].uop[A[arg[p].i]][2] \in RetValues
            BY <5>2
          <5>4. RetValues = UOpRetDomain
            BY DEF UOpRetDomain
          <5> QED
            BY <5>3, <5>4
        <4>11. (arg \in [ProcSet -> ArgDomain])'
          BY <3>11 DEF U2
        <4>12. (ret \in [ProcSet -> ResDomain])'
          BY <3>11, Zenon DEF U2
        <4>13. (xhat \in [ProcSet -> Nat])'
          BY <3>11 DEF U2
        <4>14. (\A p_1 \in ProcSet : (pc[p_1] # RemainderID) => arg[p_1] \in ArgsOf(LineIDtoOp(pc[p_1])))'
          BY <3>11, RemDef, ZenonT(90) DEF U2, LineIDtoOp
        <4>15. QED
          BY <4>1, <4>11, <4>12, <4>13, <4>14, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, <4>10 DEF TypeOK
      <3> QED
        BY Zenon, <3>1, <3>2, <3>3, <3>4, <3>5, <3>6,
           <3>7, <3>8, <3>9, <3>10, <3>11 DEF IntLines
    <2>3. ASSUME NEW p \in ProcSet, 
                 RetLine(p)
          PROVE  TypeOK'
      <3> SUFFICES ASSUME NEW Line \in RetLines(p),
                          Line,
                          P' = Filter(Evolve(P), p, ret'[p]),
                          xhat' = xhat
                   PROVE  TypeOK'
        BY <2>3, Zenon DEF RetLine
      <3> USE RemDef DEF TypeOK, ResDomain
      <3>1. CASE Line = C2(p)
        <4>1. (pc \in [ProcSet -> LineIDs])'
          BY <3>1, Zenon DEF C2, LineIDs
        <4>2. (A \in [1..M -> WordDomain])'
          BY <3>1 DEF C2
        <4>3. (B \in [1..M -> [val: WordDomain, seq: Nat]])'
          BY <3>1 DEF C2
        <4>4. (X \in Nat)'
          BY <3>1, Isa DEF C2
        <4>5. (a \in [ProcSet -> WordDomain])'
          BY <3>1 DEF C2
        <4>6. (b \in [ProcSet -> [val: WordDomain, seq: Nat]])'
          BY <3>1 DEF C2
        <4>7. (x \in [ProcSet -> Nat])'
          BY <3>1 DEF C2
        <4>8. (k \in [ProcSet -> 1..3])'
          BY <3>1 DEF C2
        <4>9. (\A p_1 \in ProcSet : pc[p_1] \in {"O1B", "O1C", "O1D", "U1B", "U1C", "U1D"} => k[p_1] \in 1..2)'
          BY <3>1, Zenon DEF C2
        <4>10. (r \in [ProcSet -> WordDomain \union UOpRetDomain])'
          BY <3>1 DEF C2
        <4>11. (arg \in [ProcSet -> ArgDomain])'
          BY <3>1 DEF C2
        <4>12. (ret \in [ProcSet -> ResDomain])'
          BY <3>1, Zenon DEF C2
        <4>13. (xhat \in [ProcSet -> Nat])'
          BY <3>1 DEF C2
        <4>14. (\A p_1 \in ProcSet : (pc[p_1] # RemainderID) => arg[p_1] \in ArgsOf(LineIDtoOp(pc[p_1])))'
          BY <3>1, RemDef, ZenonT(90) DEF C2, LineIDtoOp
        <4>15. QED
          BY <4>1, <4>11, <4>12, <4>13, <4>14, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, <4>10 DEF TypeOK
      <3>2. CASE Line = O3(p)
        <4>1. (pc \in [ProcSet -> LineIDs])'
          BY <3>2, Zenon DEF O3, LineIDs
        <4>2. (A \in [1..M -> WordDomain])'
          BY <3>2 DEF O3
        <4>3. (B \in [1..M -> [val: WordDomain, seq: Nat]])'
          BY <3>2 DEF O3
        <4>4. (X \in Nat)'
          BY <3>2, Isa DEF O3
        <4>5. (a \in [ProcSet -> WordDomain])'
          BY <3>2 DEF O3
        <4>6. (b \in [ProcSet -> [val: WordDomain, seq: Nat]])'
          BY <3>2 DEF O3
        <4>7. (x \in [ProcSet -> Nat])'
          BY <3>2 DEF O3
        <4>8. (k \in [ProcSet -> 1..3])'
          BY <3>2 DEF O3
        <4>9. (\A p_1 \in ProcSet : pc[p_1] \in {"O1B", "O1C", "O1D", "U1B", "U1C", "U1D"} => k[p_1] \in 1..2)'
          BY <3>2, Zenon DEF O3
        <4>10. (r \in [ProcSet -> WordDomain \union UOpRetDomain])'
          BY <3>2 DEF O3
        <4>11. (arg \in [ProcSet -> ArgDomain])'
          BY <3>2 DEF O3
        <4>12. (ret \in [ProcSet -> ResDomain])'
          BY <3>2, Zenon DEF O3
        <4>13. (xhat \in [ProcSet -> Nat])'
          BY <3>2 DEF O3
        <4>14. (\A p_1 \in ProcSet : (pc[p_1] # RemainderID) => arg[p_1] \in ArgsOf(LineIDtoOp(pc[p_1])))'
          BY <3>2, RemDef, ZenonT(90) DEF O3, LineIDtoOp
        <4>15. QED
          BY <4>1, <4>11, <4>12, <4>13, <4>14, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, <4>10 DEF TypeOK
      <3>3. CASE Line = U3(p)
        <4>1. (pc \in [ProcSet -> LineIDs])'
          BY <3>3, Zenon DEF U3, LineIDs
        <4>2. (A \in [1..M -> WordDomain])'
          BY <3>3 DEF U3
        <4>3. (B \in [1..M -> [val: WordDomain, seq: Nat]])'
          BY <3>3 DEF U3
        <4>4. (X \in Nat)'
          BY <3>3, Isa DEF U3
        <4>5. (a \in [ProcSet -> WordDomain])'
          BY <3>3 DEF U3
        <4>6. (b \in [ProcSet -> [val: WordDomain, seq: Nat]])'
          BY <3>3 DEF U3
        <4>7. (x \in [ProcSet -> Nat])'
          BY <3>3 DEF U3
        <4>8. (k \in [ProcSet -> 1..3])'
          BY <3>3 DEF U3
        <4>9. (\A p_1 \in ProcSet : pc[p_1] \in {"O1B", "O1C", "O1D", "U1B", "U1C", "U1D"} => k[p_1] \in 1..2)'
          BY <3>3, Zenon DEF U3
        <4>10. (r \in [ProcSet -> WordDomain \union UOpRetDomain])'
          BY <3>3 DEF U3
        <4>11. (arg \in [ProcSet -> ArgDomain])'
          BY <3>3 DEF U3
        <4>12. (ret \in [ProcSet -> ResDomain])'
          BY <3>3, Zenon DEF U3
        <4>13. (xhat \in [ProcSet -> Nat])'
          BY <3>3 DEF U3
        <4>14. (\A p_1 \in ProcSet : (pc[p_1] # RemainderID) => arg[p_1] \in ArgsOf(LineIDtoOp(pc[p_1])))'
          BY <3>3, RemDef, ZenonT(90) DEF U3, LineIDtoOp
        <4>15. QED
          BY <4>1, <4>11, <4>12, <4>13, <4>14, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, <4>10 DEF TypeOK
      <3> QED
        BY Zenon, <3>1, <3>2, <3>3 DEF RetLines
    <2> QED
      BY <1>1, <2>1, <2>2, <2>3 DEF Next
  <1>2. CASE UNCHANGED vars
    <2> USE RemDef DEF TypeOK, vars, algvars
    <2>1. (pc \in [ProcSet -> LineIDs])'
      BY <1>2 DEF LineIDs
    <2>2. (A \in [1..M -> WordDomain])'
      BY <1>2
    <2>3. (B \in [1..M -> [val: WordDomain, seq: Nat]])'
      BY <1>2
    <2>4. (X \in Nat)'
      BY <1>2
    <2>5. (a \in [ProcSet -> WordDomain])'
      BY <1>2
    <2>6. (b \in [ProcSet -> [val: WordDomain, seq: Nat]])'
      BY <1>2
    <2>7. (x \in [ProcSet -> Nat])'
      BY <1>2
    <2>8. (k \in [ProcSet -> 1..3])'
      BY <1>2
    <2>9. (\A p \in ProcSet : pc[p] \in {"O1B", "O1C", "O1D", "U1B", "U1C", "U1D"}
                              => k[p] \in 1..2)'
      BY <1>2
    <2>10. (r \in [ProcSet -> WordDomain \union UOpRetDomain])'
      BY <1>2
    <2>11. (arg \in [ProcSet -> ArgDomain])'
      BY <1>2
    <2>12. (ret \in [ProcSet -> ResDomain])'
      BY <1>2
    <2>13. (xhat \in [ProcSet -> Nat])'
      BY <1>2
    <2>14. (\A p \in ProcSet : (pc[p] # RemainderID) => arg[p] \in ArgsOf(LineIDtoOp(pc[p])))'
      BY <1>2
    <2>15. QED
      BY <2>1, <2>10, <2>11, <2>12, <2>13, <2>14, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9 DEF TypeOK
  <1> QED
    BY <1>1, <1>2




================================================================================
\* Modification History
\* Last modified Wed Aug 14 13:13:23 EDT 2024 by uguryavuz
\* Created Wed Mar 13 19:30:05 EDT 2024 by uguryavuz
