----------------------------- MODULE MemSnap_Proof -----------------------------
EXTENDS MemSnap_Impl,
        Integers, Sequences, FiniteSets, Permutations,
        TLAPS
INSTANCE Augmentation \* Sets constants BOT, ConfigDomain, Delta(_, _, _), ProcSet 
                      \* in Augmentation, to those specified in Checkpointable_Type
                      \* which itself is imported by extending CptableJJJ_Implementation

VARIABLES xhat

ASSUME BotDef == /\ BOT \notin OpNames
                 /\ BOT \notin WordDomain
                 /\ BOT # ACK
                 
ASSUME RemDef == RemainderID = "L0"

InvokeLine(p) == /\ pc[p] = RemainderID
                 /\ \E op \in AllowedOpNames(p) :
                       /\ pc' = [pc EXCEPT ![p] = OpToInvocLine(op)]
                       /\ \E new_arg \in ArgsOf(op) : arg' = [arg EXCEPT ![p] = new_arg]
                 /\ UNCHANGED <<A, B, X, a, b, x, k, r, ret>>
                 /\ xhat' = [xhat EXCEPT ![p] = X] (* History variable *)

InvocnAction == \E p \in ProcSet : InvokeLine(p)
IntermAction == /\ \E p \in ProcSet : \E LineAction \in IntLines(p) : LineAction
                /\ UNCHANGED xhat
ReturnAction == /\ \E p \in ProcSet : \E LineAction \in RetLines(p) : LineAction
                /\ UNCHANGED xhat

Next == \/ InvocnAction
        \/ IntermAction
        \/ ReturnAction                                 
               
augvars == vars \o <<xhat>>

\* Augmented initial state
AInit == /\ Init
         /\ xhat = [p \in ProcSet |-> 0]

Spec == AInit /\ [][Next]_augvars

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

TypeOK == /\ pc \in [ProcSet -> LineIDs]
          /\ \A p \in ProcSet : /\ p = Scanner  => pc[p] \in {RemainderID, "C1", "C2", "O1A", "O1B", "O1C", "O1D", "O2", "O3"}
                                /\ p \in UpdSet => pc[p] \in {RemainderID, "U1A", "U1B", "U1C", "U1D", "U2", "U3"}
          /\ A \in [1..M -> WordDomain]
          /\ B \in [1..M -> [val: WordDomain, seq: Nat]]
          /\ X \in Nat
          /\ a \in [ProcSet -> WordDomain]
          /\ b \in [ProcSet -> [val: WordDomain, seq: Nat]]
          /\ x \in [ProcSet -> Nat]
          /\ k \in [ProcSet -> 1..2]
          /\ r \in [ProcSet -> WordDomain \union UOpRetDomain]
          /\ arg \in [ProcSet -> ArgDomain]
          /\ ret \in [ProcSet -> ResDomain]
          /\ xhat \in [ProcSet -> Nat]
          /\ \A p \in ProcSet : (pc[p] # RemainderID) => arg[p] \in ArgsOf(LineIDtoOp(pc[p]))

LEMMA InitTypeOK == AInit => TypeOK
  <1> SUFFICES ASSUME AInit
               PROVE  TypeOK
    OBVIOUS
  <1> USE RemDef, InitStateExists
      DEF TypeOK, AInit, Init, InitState, LineIDs, StateDomain
  <1>1. pc \in [ProcSet -> LineIDs]
    OBVIOUS
  <1>2. \A p \in ProcSet : /\ p = Scanner  => pc[p] \in {RemainderID, "C1", "C2", "O1A", "O1B", "O1C", "O1D", "O2", "O3"}
                           /\ p \in UpdSet => pc[p] \in {RemainderID, "U1A", "U1B", "U1C", "U1D", "U2", "U3"}
    OBVIOUS
  <1>3. A \in [1..M -> WordDomain]
    OBVIOUS
  <1>4. B \in [1..M -> [val: WordDomain, seq: Nat]]  
    OBVIOUS
  <1>5. X \in Nat
    OBVIOUS
  <1>6. a \in [ProcSet -> WordDomain]
    OBVIOUS
  <1>7. b \in [ProcSet -> [val: WordDomain, seq: Nat]]
    OBVIOUS      
  <1>8. x \in [ProcSet -> Nat]
    OBVIOUS
  <1>9. k \in [ProcSet -> 1..2]
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

LEMMA NextTypeOK == TypeOK /\ [Next]_augvars => TypeOK'
  <1> SUFFICES ASSUME TypeOK, [Next]_augvars
               PROVE  TypeOK'
    OBVIOUS
  <1>1. CASE Next
    <2> USE Next
    <2>1. CASE InvocnAction
      <3> SUFFICES ASSUME NEW p \in ProcSet,
                          InvokeLine(p)
                   PROVE  TypeOK'
        BY <2>1 DEF InvocnAction
      <3> USE RemDef DEF TypeOK, InvokeLine
      <3>1. (pc \in [ProcSet -> LineIDs])'
        BY <2>1 DEF AllowedOpNames, OpToInvocLine, LineIDs, UpdSet
      <3>2. (\A q \in ProcSet : /\ q = Scanner  => pc[q] \in {RemainderID, "C1", "C2", "O1A", "O1B", "O1C", "O1D", "O2", "O3"}
                                /\ q \in UpdSet => pc[q] \in {RemainderID, "U1A", "U1B", "U1C", "U1D", "U2", "U3"})'
        BY <2>1 DEF AllowedOpNames, OpToInvocLine, LineIDs, UpdSet
      <3>3. (A \in [1..M -> WordDomain])'
        BY <2>1
      <3>4. (B \in [1..M -> [val: WordDomain, seq: Nat]])'
        BY <2>1
      <3>5. (X \in Nat)'
        BY <2>1
      <3>6. (a \in [ProcSet -> WordDomain])'
        BY <2>1
      <3>7. (b \in [ProcSet -> [val: WordDomain, seq: Nat]])'
        BY <2>1
      <3>8. (x \in [ProcSet -> Nat])'
        BY <2>1
      <3>9. (k \in [ProcSet -> 1..2])'
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
        <4> SUFFICES arg'[p] \in ArgsOf(LineIDtoOp(pc'[p]))
          BY <2>1, Zenon
        <4>1. PICK op \in AllowedOpNames(p) : /\ pc' = [pc EXCEPT ![p] = OpToInvocLine(op)]
                                              /\ \E new_arg \in ArgsOf(op) : arg' = [arg EXCEPT ![p] = new_arg]
          BY <2>1, Zenon
        <4>2. pc'[p] = OpToInvocLine(op)
          BY <4>1, Zenon
        <4>3. PICK new_arg \in ArgsOf(op) : arg'[p] = new_arg
          BY <4>1, Zenon
        <4>4. LineIDtoOp(OpToInvocLine(op)) = op
          BY <4>1 DEF LineIDtoOp, OpToInvocLine, AllowedOpNames, UpdSet
        <4> QED
          BY <4>2, <4>3, <4>4
      <3>15. QED
        BY <3>1, <3>2, <3>10, <3>11, <3>12, <3>13, <3>14, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9 DEF TypeOK
    <2>2. CASE IntermAction
      <3> SUFFICES ASSUME NEW p \in ProcSet,
                          NEW LineAction \in IntLines(p),
                          LineAction,
                          UNCHANGED xhat
                   PROVE  TypeOK'
        BY <2>2, Zenon DEF IntermAction
      <3>1. CASE LineAction = C1(p)
        <4> USE DEF TypeOK
        <4>1. (pc \in [ProcSet -> LineIDs])'
          BY <3>1, Zenon DEF C1, LineIDs
        <4>2. (\A q \in ProcSet : /\ q = Scanner  => pc[q] \in {RemainderID, "C1", "C2", "O1A", "O1B", "O1C", "O1D", "O2", "O3"}
                                  /\ q \in UpdSet => pc[q] \in {RemainderID, "U1A", "U1B", "U1C", "U1D", "U2", "U3"})'
          BY <3>1, Zenon DEF C1, AllowedOpNames, OpToInvocLine, LineIDs, UpdSet
        <4>3. (A \in [1..M -> WordDomain])'
          BY <3>1 DEF C1
        <4>4. (B \in [1..M -> [val: WordDomain, seq: Nat]])'
          BY <3>1 DEF C1
        <4>5. (X \in Nat)'
          BY <3>1, Isa DEF C1
        <4>6. (a \in [ProcSet -> WordDomain])'
          BY <3>1 DEF C1
        <4>7. (b \in [ProcSet -> [val: WordDomain, seq: Nat]])'
          BY <3>1 DEF C1
        <4>8. (x \in [ProcSet -> Nat])'
          BY <3>1 DEF C1
        <4>9. (k \in [ProcSet -> 1..2])'
          BY <3>1 DEF C1
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
          BY <4>1, <4>2, <4>11, <4>12, <4>13, <4>14, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, <4>10 DEF TypeOK
      <3>2. CASE LineAction = O1A(p)
        <4> USE RemDef DEF TypeOK
        <4>1. (pc \in [ProcSet -> LineIDs])'
          BY <3>2, Zenon DEF O1A, LineIDs
        <4>2. (\A q \in ProcSet : /\ q = Scanner  => pc[q] \in {RemainderID, "C1", "C2", "O1A", "O1B", "O1C", "O1D", "O2", "O3"}
                                  /\ q \in UpdSet => pc[q] \in {RemainderID, "U1A", "U1B", "U1C", "U1D", "U2", "U3"})'
          BY <3>2, Zenon DEF O1A, AllowedOpNames, OpToInvocLine, LineIDs, UpdSet
        <4>3. (A \in [1..M -> WordDomain])'
          BY <3>2 DEF O1A
        <4>4. (B \in [1..M -> [val: WordDomain, seq: Nat]])'
          BY <3>2 DEF O1A
        <4>5. (X \in Nat)'
          BY <3>2, Isa DEF O1A
        <4>6. (a \in [ProcSet -> WordDomain])'
          BY <3>2 DEF O1A
        <4>7. (b \in [ProcSet -> [val: WordDomain, seq: Nat]])'
          <5> USE <3>2 DEF O1A
          <5> SUFFICES B[arg[p].i] \in [val: WordDomain, seq: Nat]
            BY Zenon
          <5> SUFFICES arg[p].i \in 1..M
            BY Zenon
          <5> QED
            BY Zenon, RemDef DEF LineIDtoOp, ArgsOf
        <4>8. (x \in [ProcSet -> Nat])'
          BY <3>2 DEF O1A
        <4>9. (k \in [ProcSet -> 1..2])'
          BY <3>2, Zenon DEF O1A
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
          BY <4>1, <4>2, <4>11, <4>12, <4>13, <4>14, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, <4>10 DEF TypeOK
      <3>3. CASE LineAction = O1B(p)
        <4> USE RemDef DEF TypeOK
        <4>1. (pc \in [ProcSet -> LineIDs])'
          BY <3>3, Zenon DEF O1B, LineIDs
        <4>2. (\A q \in ProcSet : /\ q = Scanner  => pc[q] \in {RemainderID, "C1", "C2", "O1A", "O1B", "O1C", "O1D", "O2", "O3"}
                                  /\ q \in UpdSet => pc[q] \in {RemainderID, "U1A", "U1B", "U1C", "U1D", "U2", "U3"})'
          BY <3>3, Zenon DEF O1B, AllowedOpNames, OpToInvocLine, LineIDs, UpdSet
        <4>3. (A \in [1..M -> WordDomain])'
          BY <3>3 DEF O1B
        <4>4. (B \in [1..M -> [val: WordDomain, seq: Nat]])'
          BY <3>3 DEF O1B
        <4>5. (X \in Nat)'
          BY <3>3, Isa DEF O1B
        <4>6. (a \in [ProcSet -> WordDomain])'
          BY <3>3 DEF O1B
        <4>7. (b \in [ProcSet -> [val: WordDomain, seq: Nat]])'
          BY <3>3 DEF O1B
        <4>8. (x \in [ProcSet -> Nat])'
          BY <3>3 DEF O1B
        <4>9. (k \in [ProcSet -> 1..2])'
          <5> USE <3>3 DEF O1B
          <5> SUFFICES k'[p] \in 1..2
            BY Zenon
          <5>1. k'[p] = 1 \/ k'[p] = k[p]
            BY Zenon
          <5> QED
            BY <5>1
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
          BY <4>1, <4>2, <4>11, <4>12, <4>13, <4>14, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, <4>10 DEF TypeOK
      <3>4. CASE LineAction = O1C(p)
        <4> USE RemDef DEF TypeOK
        <4>1. (pc \in [ProcSet -> LineIDs])'
          BY <3>4, Zenon DEF O1C, LineIDs
        <4>2. (\A q \in ProcSet : /\ q = Scanner  => pc[q] \in {RemainderID, "C1", "C2", "O1A", "O1B", "O1C", "O1D", "O2", "O3"}
                                  /\ q \in UpdSet => pc[q] \in {RemainderID, "U1A", "U1B", "U1C", "U1D", "U2", "U3"})'
          BY <3>4, Zenon DEF O1C, AllowedOpNames, OpToInvocLine, LineIDs, UpdSet
        <4>3. (A \in [1..M -> WordDomain])'
          BY <3>4 DEF O1C
        <4>4. (B \in [1..M -> [val: WordDomain, seq: Nat]])'
          BY <3>4 DEF O1C
        <4>5. (X \in Nat)'
          BY <3>4, Isa DEF O1C
        <4>6. (a \in [ProcSet -> WordDomain])'
          <5> USE <3>4 DEF O1C
          <5> SUFFICES A[arg[p].i] \in WordDomain
            BY Zenon
          <5> SUFFICES arg[p].i \in 1..M
            BY Zenon
          <5> QED
            BY Zenon DEF LineIDtoOp, ArgsOf
        <4>7. (b \in [ProcSet -> [val: WordDomain, seq: Nat]])'
          BY <3>4 DEF O1C
        <4>8. (x \in [ProcSet -> Nat])'
          BY <3>4 DEF O1C
        <4>9. (k \in [ProcSet -> 1..2])'
          BY <3>4 DEF O1C
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
          BY <4>1, <4>2, <4>11, <4>12, <4>13, <4>14, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, <4>10 DEF TypeOK
      <3>5. CASE LineAction = O1D(p)
        <4> USE RemDef DEF TypeOK
        <4>1. (pc \in [ProcSet -> LineIDs])'
          BY <3>5, Zenon DEF O1D, LineIDs
        <4>2. (\A q \in ProcSet : /\ q = Scanner  => pc[q] \in {RemainderID, "C1", "C2", "O1A", "O1B", "O1C", "O1D", "O2", "O3"}
                                  /\ q \in UpdSet => pc[q] \in {RemainderID, "U1A", "U1B", "U1C", "U1D", "U2", "U3"})'
          BY <3>5, Zenon DEF O1D, AllowedOpNames, OpToInvocLine, LineIDs, UpdSet
        <4>3. (A \in [1..M -> WordDomain])'
          BY <3>5 DEF O1D
        <4>4. (B \in [1..M -> [val: WordDomain, seq: Nat]])'
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
        <4>5. (X \in Nat)'
          BY <3>5, Isa DEF O1D
        <4>6. (a \in [ProcSet -> WordDomain])'
          BY <3>5 DEF O1D
        <4>7. (b \in [ProcSet -> [val: WordDomain, seq: Nat]])'
          BY <3>5 DEF O1D
        <4>8. (x \in [ProcSet -> Nat])'
          BY <3>5 DEF O1D
        <4>9. (k \in [ProcSet -> 1..2])'
          <5> USE <3>5 DEF O1D
          <5> SUFFICES k'[p] \in 1..2
            BY Zenon
          <5>1. k'[p] = 1 \/ (k[p] # 2 /\ k'[p] = k[p]+1)
            BY Zenon
          <5>2. k[p] \in 1..2
            BY Zenon
          <5> QED
            BY <5>1, <5>2
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
          BY <4>1, <4>2, <4>11, <4>12, <4>13, <4>14, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, <4>10 DEF TypeOK
      <3>6. CASE LineAction = O2(p)
        <4> USE RemDef DEF TypeOK
        <4>1. (pc \in [ProcSet -> LineIDs])'
          BY <3>6, Zenon DEF O2, LineIDs
        <4>2. (\A q \in ProcSet : /\ q = Scanner  => pc[q] \in {RemainderID, "C1", "C2", "O1A", "O1B", "O1C", "O1D", "O2", "O3"}
                                  /\ q \in UpdSet => pc[q] \in {RemainderID, "U1A", "U1B", "U1C", "U1D", "U2", "U3"})'
          BY <3>6, Zenon DEF O2, AllowedOpNames, OpToInvocLine, LineIDs, UpdSet
        <4>3. (A \in [1..M -> WordDomain])'
          BY <3>6 DEF O2
        <4>4. (B \in [1..M -> [val: WordDomain, seq: Nat]])'
          BY <3>6 DEF O2
        <4>5. (X \in Nat)'
          BY <3>6, Isa DEF O2
        <4>6. (a \in [ProcSet -> WordDomain])'
          BY <3>6 DEF O2
        <4>7. (b \in [ProcSet -> [val: WordDomain, seq: Nat]])'
          BY <3>6 DEF O2
        <4>8. (x \in [ProcSet -> Nat])'
          BY <3>6 DEF O2
        <4>9. (k \in [ProcSet -> 1..2])'
          BY <3>6 DEF O2
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
          BY <4>1, <4>2, <4>11, <4>12, <4>13, <4>14, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, <4>10 DEF TypeOK      
      <3>7. CASE LineAction = U1A(p)
        <4> USE RemDef DEF TypeOK
        <4>1. (pc \in [ProcSet -> LineIDs])'
          BY <3>7, Zenon DEF U1A, LineIDs
        <4>2. (\A q \in ProcSet : /\ q = Scanner  => pc[q] \in {RemainderID, "C1", "C2", "O1A", "O1B", "O1C", "O1D", "O2", "O3"}
                                  /\ q \in UpdSet => pc[q] \in {RemainderID, "U1A", "U1B", "U1C", "U1D", "U2", "U3"})'
          BY <3>7, Zenon DEF U1A, AllowedOpNames, OpToInvocLine, LineIDs, UpdSet
        <4>3. (A \in [1..M -> WordDomain])'
          BY <3>7 DEF U1A
        <4>4. (B \in [1..M -> [val: WordDomain, seq: Nat]])'
          BY <3>7 DEF U1A
        <4>5. (X \in Nat)'
          BY <3>7, Isa DEF U1A
        <4>6. (a \in [ProcSet -> WordDomain])'
          BY <3>7 DEF U1A
        <4>7. (b \in [ProcSet -> [val: WordDomain, seq: Nat]])'
          <5> USE <3>7 DEF U1A
          <5> SUFFICES B[arg[p].i] \in [val: WordDomain, seq: Nat]
            BY Zenon
          <5> SUFFICES arg[p].i \in 1..M
            BY Zenon
          <5> QED
            BY Zenon DEF LineIDtoOp, ArgsOf
        <4>8. (x \in [ProcSet -> Nat])'
          BY <3>7 DEF U1A
        <4>9. (k \in [ProcSet -> 1..2])'
          <5> USE <3>7 DEF U1A
          <5> SUFFICES k'[p] \in 1..2
            BY Zenon
          <5>1. k'[p] = 1 \/ k'[p] = k[p]
            BY Zenon
          <5> QED
            BY <5>1
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
          BY <4>1, <4>2, <4>11, <4>12, <4>13, <4>14, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, <4>10 DEF TypeOK
      <3>8. CASE LineAction = U1B(p)
        <4> USE RemDef DEF TypeOK
        <4>1. (pc \in [ProcSet -> LineIDs])'
          BY <3>8, Zenon DEF U1B, LineIDs
        <4>2. (\A q \in ProcSet : /\ q = Scanner  => pc[q] \in {RemainderID, "C1", "C2", "O1A", "O1B", "O1C", "O1D", "O2", "O3"}
                                  /\ q \in UpdSet => pc[q] \in {RemainderID, "U1A", "U1B", "U1C", "U1D", "U2", "U3"})'
          BY <3>8, Zenon DEF U1B, AllowedOpNames, OpToInvocLine, LineIDs, UpdSet
        <4>3. (A \in [1..M -> WordDomain])'
          BY <3>8 DEF U1B
        <4>4. (B \in [1..M -> [val: WordDomain, seq: Nat]])'
          BY <3>8 DEF U1B
        <4>5. (X \in Nat)'
          BY <3>8, Isa DEF U1B
        <4>6. (a \in [ProcSet -> WordDomain])'
          BY <3>8 DEF U1B
        <4>7. (b \in [ProcSet -> [val: WordDomain, seq: Nat]])'
          BY <3>8 DEF U1B
        <4>8. (x \in [ProcSet -> Nat])'
          BY <3>8 DEF U1B
        <4>9. (k \in [ProcSet -> 1..2])'
          <5> USE <3>8 DEF U1B
          <5> SUFFICES k'[p] \in 1..2
            BY Zenon
          <5>1. k'[p] = 1 \/ k'[p] = k[p]
            BY Zenon
          <5> QED
            BY <5>1
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
          BY <4>1, <4>2, <4>11, <4>12, <4>13, <4>14, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, <4>10 DEF TypeOK
      <3>9. CASE LineAction = U1C(p)
        <4> USE RemDef DEF TypeOK
        <4>1. (pc \in [ProcSet -> LineIDs])'
          BY <3>9, Zenon DEF U1C, LineIDs
        <4>2. (\A q \in ProcSet : /\ q = Scanner  => pc[q] \in {RemainderID, "C1", "C2", "O1A", "O1B", "O1C", "O1D", "O2", "O3"}
                                  /\ q \in UpdSet => pc[q] \in {RemainderID, "U1A", "U1B", "U1C", "U1D", "U2", "U3"})'
          BY <3>9, Zenon DEF U1C, AllowedOpNames, OpToInvocLine, LineIDs, UpdSet
        <4>3. (A \in [1..M -> WordDomain])'
          BY <3>9 DEF U1C
        <4>4. (B \in [1..M -> [val: WordDomain, seq: Nat]])'
          BY <3>9 DEF U1C
        <4>5. (X \in Nat)'
          BY <3>9, Isa DEF U1C
        <4>6. (a \in [ProcSet -> WordDomain])'
          <5> USE <3>9 DEF U1C
          <5> SUFFICES A[arg[p].i] \in WordDomain
            BY Zenon
          <5> SUFFICES arg[p].i \in 1..M
            BY Zenon
          <5> QED
            BY Zenon DEF LineIDtoOp, ArgsOf
        <4>7. (b \in [ProcSet -> [val: WordDomain, seq: Nat]])'
          BY <3>9 DEF U1C
        <4>8. (x \in [ProcSet -> Nat])'
          BY <3>9 DEF U1C
        <4>9. (k \in [ProcSet -> 1..2])'
          BY <3>9 DEF U1C
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
          BY <4>1, <4>2, <4>11, <4>12, <4>13, <4>14, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, <4>10 DEF TypeOK      
      <3>10. CASE LineAction = U1D(p)
        <4> USE RemDef DEF TypeOK
        <4>1. (pc \in [ProcSet -> LineIDs])'
          BY <3>10, Zenon DEF U1D, LineIDs
        <4>2. (\A q \in ProcSet : /\ q = Scanner  => pc[q] \in {RemainderID, "C1", "C2", "O1A", "O1B", "O1C", "O1D", "O2", "O3"}
                                  /\ q \in UpdSet => pc[q] \in {RemainderID, "U1A", "U1B", "U1C", "U1D", "U2", "U3"})'
          BY <3>10, Zenon DEF U1D, AllowedOpNames, OpToInvocLine, LineIDs, UpdSet
        <4>3. (A \in [1..M -> WordDomain])'
          BY <3>10 DEF U1D
        <4>4. (B \in [1..M -> [val: WordDomain, seq: Nat]])'
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
        <4>5. (X \in Nat)'
          BY <3>10, Isa DEF U1D
        <4>6. (a \in [ProcSet -> WordDomain])'
          BY <3>10 DEF U1D
        <4>7. (b \in [ProcSet -> [val: WordDomain, seq: Nat]])'
          BY <3>10 DEF U1D
        <4>8. (x \in [ProcSet -> Nat])'
          BY <3>10 DEF U1D
        <4>9. (k \in [ProcSet -> 1..2])'
          <5> USE <3>10 DEF U1D
          <5> SUFFICES k'[p] \in 1..2
            BY Zenon
          <5>1. k'[p] = 1 \/ (k[p] # 2 /\ k'[p] = k[p]+1)
            BY Zenon
          <5>2. k[p] \in 1..2
            BY Zenon
          <5> QED
            BY <5>1, <5>2
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
          BY <4>1, <4>2, <4>11, <4>12, <4>13, <4>14, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, <4>10 DEF TypeOK
      <3>11. CASE LineAction = U2(p)
        <4> USE RemDef DEF TypeOK
        <4>1. (pc \in [ProcSet -> LineIDs])'
          BY <3>11, Zenon DEF U2, LineIDs
        <4>2. (\A q \in ProcSet : /\ q = Scanner  => pc[q] \in {RemainderID, "C1", "C2", "O1A", "O1B", "O1C", "O1D", "O2", "O3"}
                                  /\ q \in UpdSet => pc[q] \in {RemainderID, "U1A", "U1B", "U1C", "U1D", "U2", "U3"})'
          BY <3>11, Zenon DEF U2, AllowedOpNames, OpToInvocLine, LineIDs, UpdSet
        <4>3. (A \in [1..M -> WordDomain])'
          <5> USE <3>11 DEF U2
          <5>1. \A idx \in 1..M : idx # arg[p].i => A'[idx] = A[idx]
            BY Zenon
          <5> SUFFICES A'[arg[p].i] \in WordDomain
            BY <5>1, Zenon
          <5> SUFFICES /\ arg[p].i \in 1..M
                       /\ arg[p].uop[A[arg[p].i]][1] \in WordDomain
            BY Zenon
          <5>2. /\ arg[p].i \in 1..M
                /\ arg[p].uop \in [WordDomain -> WordDomain \X UOpRetDomain]
            BY Zenon DEF LineIDtoOp, ArgsOf
          <5>3. arg[p].uop[A[arg[p].i]][1] \in WordDomain
            BY <5>2
          <5> QED 
            BY <5>2, <5>3
        <4>4. (B \in [1..M -> [val: WordDomain, seq: Nat]])'
          BY <3>11 DEF U2
        <4>5. (X \in Nat)'
          BY <3>11, Isa DEF U2
        <4>6. (a \in [ProcSet -> WordDomain])'
          BY <3>11 DEF U2
        <4>7. (b \in [ProcSet -> [val: WordDomain, seq: Nat]])'
          BY <3>11 DEF U2
        <4>8. (x \in [ProcSet -> Nat])'
          BY <3>11 DEF U2
        <4>9. (k \in [ProcSet -> 1..2])'
          BY <3>11 DEF U2
        <4>10. (r \in [ProcSet -> WordDomain \union UOpRetDomain])'
          <5> USE <3>11 DEF U2
          <5> SUFFICES arg[p].uop[A[arg[p].i]][2] \in WordDomain \union UOpRetDomain
            BY Zenon
          <5>2. /\ arg[p].i \in 1..M
                /\ arg[p].uop \in [WordDomain -> WordDomain \X UOpRetDomain]
            BY Zenon DEF LineIDtoOp, ArgsOf
          <5>3. arg[p].uop[A[arg[p].i]][2] \in UOpRetDomain
            BY <5>2
          <5> QED
            BY <5>3
        <4>11. (arg \in [ProcSet -> ArgDomain])'
          BY <3>11 DEF U2
        <4>12. (ret \in [ProcSet -> ResDomain])'
          BY <3>11, Zenon DEF U2
        <4>13. (xhat \in [ProcSet -> Nat])'
          BY <3>11 DEF U2
        <4>14. (\A p_1 \in ProcSet : (pc[p_1] # RemainderID) => arg[p_1] \in ArgsOf(LineIDtoOp(pc[p_1])))'
          BY <3>11, RemDef, ZenonT(90) DEF U2, LineIDtoOp
        <4>15. QED
          BY <4>1, <4>2, <4>11, <4>12, <4>13, <4>14, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, <4>10 DEF TypeOK
      <3> QED
        BY Zenon, <3>1, <3>2, <3>3, <3>4, <3>5, <3>6,
           <3>7, <3>8, <3>9, <3>10, <3>11 DEF IntLines
    <2>3. CASE ReturnAction
      <3> SUFFICES ASSUME NEW p \in ProcSet,
                          NEW LineAction \in RetLines(p),
                          LineAction,
                          UNCHANGED xhat
                   PROVE  TypeOK'
        BY <2>3, Zenon DEF ReturnAction
      <3> USE RemDef DEF TypeOK, ResDomain
      <3>1. CASE LineAction = C2(p)
        <4>1. (pc \in [ProcSet -> LineIDs])'
          BY <3>1, Zenon DEF C2, LineIDs
        <4>2. (\A q \in ProcSet : /\ q = Scanner  => pc[q] \in {RemainderID, "C1", "C2", "O1A", "O1B", "O1C", "O1D", "O2", "O3"}
                                  /\ q \in UpdSet => pc[q] \in {RemainderID, "U1A", "U1B", "U1C", "U1D", "U2", "U3"})'
          BY <3>1, Zenon DEF C2, AllowedOpNames, OpToInvocLine, LineIDs, UpdSet
        <4>3. (A \in [1..M -> WordDomain])'
          BY <3>1 DEF C2
        <4>4. (B \in [1..M -> [val: WordDomain, seq: Nat]])'
          BY <3>1 DEF C2
        <4>5. (X \in Nat)'
          BY <3>1, Isa DEF C2
        <4>6. (a \in [ProcSet -> WordDomain])'
          BY <3>1 DEF C2
        <4>7. (b \in [ProcSet -> [val: WordDomain, seq: Nat]])'
          BY <3>1 DEF C2
        <4>8. (x \in [ProcSet -> Nat])'
          BY <3>1 DEF C2
        <4>9. (k \in [ProcSet -> 1..2])'
          BY <3>1 DEF C2
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
          BY <4>1, <4>2, <4>11, <4>12, <4>13, <4>14, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, <4>10 DEF TypeOK
      <3>2. CASE LineAction = O3(p)
        <4>1. (pc \in [ProcSet -> LineIDs])'
          BY <3>2, Zenon DEF O3, LineIDs
        <4>2. (\A q \in ProcSet : /\ q = Scanner  => pc[q] \in {RemainderID, "C1", "C2", "O1A", "O1B", "O1C", "O1D", "O2", "O3"}
                                  /\ q \in UpdSet => pc[q] \in {RemainderID, "U1A", "U1B", "U1C", "U1D", "U2", "U3"})'
          BY <3>2, Zenon DEF O3, AllowedOpNames, OpToInvocLine, LineIDs, UpdSet
        <4>3. (A \in [1..M -> WordDomain])'
          BY <3>2 DEF O3
        <4>4. (B \in [1..M -> [val: WordDomain, seq: Nat]])'
          BY <3>2 DEF O3
        <4>5. (X \in Nat)'
          BY <3>2, Isa DEF O3
        <4>6. (a \in [ProcSet -> WordDomain])'
          BY <3>2 DEF O3
        <4>7. (b \in [ProcSet -> [val: WordDomain, seq: Nat]])'
          BY <3>2 DEF O3
        <4>8. (x \in [ProcSet -> Nat])'
          BY <3>2 DEF O3
        <4>9. (k \in [ProcSet -> 1..2])'
          BY <3>2 DEF O3
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
          BY <4>1, <4>2, <4>11, <4>12, <4>13, <4>14, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, <4>10 DEF TypeOK
      <3>3. CASE LineAction = U3(p)
        <4>1. (pc \in [ProcSet -> LineIDs])'
          BY <3>3, Zenon DEF U3, LineIDs
        <4>2. (\A q \in ProcSet : /\ q = Scanner  => pc[q] \in {RemainderID, "C1", "C2", "O1A", "O1B", "O1C", "O1D", "O2", "O3"}
                                  /\ q \in UpdSet => pc[q] \in {RemainderID, "U1A", "U1B", "U1C", "U1D", "U2", "U3"})'
          BY <3>3, Zenon DEF U3, AllowedOpNames, OpToInvocLine, LineIDs, UpdSet
        <4>3. (A \in [1..M -> WordDomain])'
          BY <3>3 DEF U3
        <4>4. (B \in [1..M -> [val: WordDomain, seq: Nat]])'
          BY <3>3 DEF U3
        <4>5. (X \in Nat)'
          BY <3>3, Isa DEF U3
        <4>6. (a \in [ProcSet -> WordDomain])'
          BY <3>3 DEF U3
        <4>7. (b \in [ProcSet -> [val: WordDomain, seq: Nat]])'
          BY <3>3 DEF U3
        <4>8. (x \in [ProcSet -> Nat])'
          BY <3>3 DEF U3
        <4>9. (k \in [ProcSet -> 1..2])'
          BY <3>3 DEF U3
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
          BY <4>1, <4>2, <4>11, <4>12, <4>13, <4>14, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, <4>10 DEF TypeOK
      <3> QED
        BY Zenon, <3>1, <3>2, <3>3 DEF RetLines
    <2> QED
      BY <2>1, <2>2, <2>3 DEF Next
  <1>2. CASE UNCHANGED augvars
    <2> USE RemDef DEF TypeOK, vars, augvars
    <2>1. (pc \in [ProcSet -> LineIDs])'
      BY <1>2 DEF LineIDs
    <2>2. (\A q \in ProcSet : /\ q = Scanner  => pc[q] \in {RemainderID, "C1", "C2", "O1A", "O1B", "O1C", "O1D", "O2", "O3"}
                              /\ q \in UpdSet => pc[q] \in {RemainderID, "U1A", "U1B", "U1C", "U1D", "U2", "U3"})'
      BY <1>2 DEF AllowedOpNames, OpToInvocLine, LineIDs, UpdSet
    <2>3. (A \in [1..M -> WordDomain])'
      BY <1>2
    <2>4. (B \in [1..M -> [val: WordDomain, seq: Nat]])'
      BY <1>2
    <2>5. (X \in Nat)'
      BY <1>2
    <2>6. (a \in [ProcSet -> WordDomain])'
      BY <1>2
    <2>7. (b \in [ProcSet -> [val: WordDomain, seq: Nat]])'
      BY <1>2
    <2>8. (x \in [ProcSet -> Nat])'
      BY <1>2
    <2>9. (k \in [ProcSet -> 1..2])'
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
      BY <2>1, <2>2, <2>10, <2>11, <2>12, <2>13, <2>14, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9 DEF TypeOK
  <1> QED
    BY <1>1, <1>2
    
InvFW1 == \A j \in 1..M : 
             X >= B[j].seq
InvFW2 == pc[Scanner] \in {"O1A", "O1B", "O1C", "O1D", "O2", "O3"} 
             => X = xhat[Scanner]
InvFW3 == \A p \in UpdSet : pc[p] \in {"U1A", "U1B", "U1C", "U1D", "U2", "U3"} 
             => X >= xhat[p]
InvFW4 == \A p \in ProcSet : pc[p] \in {"O1C", "O1D", "U1C", "U1D"} 
             => (X >= xhat[p] /\ xhat[p] > b[p].seq)
InvFW5 == \A p \in ProcSet : (pc[p] \in {"O1B", "O1C", "O1D", "U1B", "U1C", "U1D"} /\ B[arg[p].i] # b[p]) 
             => (B[arg[p].i].seq > b[p].seq)
InvFW6 == \A p \in ProcSet : (\/ (pc[p] \in {"O1A", "U1A"} /\ k[p] = 2)
                              \/ (/\ pc[p] \in {"O1B", "O1C", "O1D", "U1B", "U1C", "U1D"} 
                                  /\ B[arg[p].i] # b[p] 
                                  /\ k[p] = 1))
             => \/ B[arg[p].i].seq >= xhat[p]
                \/ (\A q \in ProcSet : (/\ pc[q] \in {"O1C", "O1D", "U1C", "U1D"}
                                        /\ arg[q].i = arg[p].i
                                        /\ b[q] = B[arg[p].i]) => x[q] >= xhat[p])
InvFW7 == \A p \in ProcSet : (pc[p] \in {"O1B", "O1C", "O1D", "U1B", "U1C", "U1D"} /\ B[arg[p].i] # b[p] /\ k[p] = 2)
             => (B[arg[p].i].seq >= xhat[p])
InvFW8 == pc[Scanner] = "O2" 
             => B[arg[Scanner].i].seq = X
InvFW9 == \A p \in UpdSet : pc[p] = "U2"
             => B[arg[p].i].seq >= xhat[p]
             
Inv == /\ TypeOK
       /\ InvFW1
       /\ InvFW2
       /\ InvFW3
       /\ InvFW4
       /\ InvFW5
       /\ InvFW6
       /\ InvFW7
       /\ InvFW8
       /\ InvFW9
       
LEMMA InitInv == AInit => Inv
  <1> SUFFICES ASSUME AInit
               PROVE  Inv
    OBVIOUS
  <1>1. TypeOK
    BY InitTypeOK
  <1> USE RemDef, ProcSetNE, <1>1 DEF AInit, Init, TypeOK, Scanner, UpdSet
  <1> \A p \in ProcSet : pc[p] = RemainderID
    OBVIOUS
  <1>2. InvFW1
    BY DEF InvFW1
  <1>3. InvFW2
    BY DEF InvFW2
  <1>4. InvFW3
    BY DEF InvFW3
  <1>5. InvFW4
    BY DEF InvFW4
  <1>6. InvFW5
    BY DEF InvFW5
  <1>7. InvFW6
    BY DEF InvFW6
  <1>8. InvFW7
    BY DEF InvFW7
  <1>9. InvFW8
    BY DEF InvFW8
  <1>10. InvFW9
    BY DEF InvFW9
  <1>11. QED
    BY <1>1, <1>10, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9 DEF Inv

LEMMA NextInv == Inv /\ [Next]_augvars => Inv'
  <1> SUFFICES ASSUME Inv, [Next]_augvars
               PROVE Inv'
    OBVIOUS
  <1>1. CASE Next
    <2> USE <1>1
    <2>1. CASE InvocnAction
    <2>2. CASE IntermAction
      <3> SUFFICES ASSUME NEW p \in ProcSet,
                          NEW LineAction \in IntLines(p),
                          LineAction,
                          UNCHANGED xhat
                   PROVE  Inv'
        BY <2>2, Zenon DEF IntermAction
      <3>1. CASE LineAction = C1(p)
        <4> USE <3>1 DEF Inv, TypeOK, C1
        <4> /\ p = Scanner 
            /\ p \notin UpdSet
            /\ UpdSet \in SUBSET ProcSet
          BY Zenon DEF C1, Scanner, UpdSet
        <4>1. TypeOK'
          BY NextTypeOK
        <4> USE <4>1
        <4>2. InvFW1'
          <5> SUFFICES ASSUME NEW j \in (1..M)
                       PROVE  X' >= B'[j].seq
            BY DEF InvFW1
          <5>1. X >= B'[j].seq
            BY Zenon DEF InvFW1
          <5>2. X' = X + 1
            BY Zenon
          <5>3. X' > X
            BY <5>2
          <5>4. X' >= B'[j].seq
            BY <5>1, <5>3, Z3T(30)
          <5> QED
            BY <5>4
        <4>3. InvFW2'
          BY Zenon DEF InvFW2
        <4>4. InvFW3'
          <5> SUFFICES ASSUME NEW q \in UpdSet,
                              pc'[q] \in {"U1A", "U1B", "U1C", "U1D", "U2", "U3"}
                       PROVE  X + 1 >= xhat[q]
            BY ZenonT(90) DEF InvFW3
          <5>1. pc[q] \in {"U1A", "U1B", "U1C", "U1D", "U2", "U3"}
            BY Zenon
          <5>2. X >= xhat[q]
            BY <5>1 DEF InvFW3
          <5> QED
            BY <5>2
        <4>5. InvFW4'
          <5> SUFFICES ASSUME NEW q \in ProcSet,
                              pc[q] \in {"O1C", "O1D", "U1C", "U1D"}
                       PROVE  X + 1 >= xhat[q] /\ xhat[q] > b[q].seq
            BY ZenonT(90) DEF InvFW4
          <5> QED
            BY DEF InvFW4
        <4>6. InvFW5'
          BY Zenon DEF InvFW5
        <4>7. InvFW6'
          BY ZenonT(90) DEF InvFW6
        <4>8. InvFW7'
          BY Zenon DEF InvFW7
        <4>9. InvFW8'
          BY Zenon DEF InvFW8
        <4>10. InvFW9'
          BY Zenon DEF InvFW9
        <4>11. QED
          BY <4>1, <4>10, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9 DEF Inv
      <3>2. CASE LineAction = O1A(p)
        <4> USE <3>2 DEF Inv, TypeOK, O1A
        <4> /\ p = Scanner 
            /\ p \notin UpdSet
            /\ UpdSet \in SUBSET ProcSet
          BY Zenon DEF O1A, Scanner, UpdSet
        <4>1. TypeOK'
          BY NextTypeOK
        <4>2. InvFW1'
          <5> SUFFICES ASSUME NEW j \in 1..M
                       PROVE  X' >= B'[j].seq
            BY DEF InvFW1
          <5>1. X >= B[j].seq
            BY DEF InvFW1
          <5> QED
            BY <5>1, Zenon
        <4>3. InvFW2'
          BY ZenonT(90) DEF InvFW2
        <4>4. InvFW3'
          <5> SUFFICES ASSUME NEW q \in UpdSet,
                              pc'[q] \in {"U1A", "U1B", "U1C", "U1D", "U2", "U3"}
                       PROVE  X' >= xhat[q]
            BY Zenon DEF InvFW3
          <5>1. pc[q] \in {"U1A", "U1B", "U1C", "U1D", "U2", "U3"}
            BY Zenon
          <5>2. X >= xhat[q]
            BY <5>1 DEF InvFW3
          <5> QED
            BY <5>2, Zenon
        <4>5. InvFW4'
          <5> SUFFICES ASSUME NEW q \in ProcSet',
                              pc'[q] \in {"O1C", "O1D", "U1C", "U1D"}
                       PROVE  X' >= xhat[q] /\ xhat[q] > b'[q].seq
            BY Zenon DEF InvFW4
          <5>1. pc[q] \in {"O1C", "O1D", "U1C", "U1D"}
            BY Zenon
          <5>2. X >= xhat[q] /\ xhat[q] > b[q].seq
            BY <5>1 DEF InvFW4
          <5> QED
            BY <5>2, Zenon
        <4>6. InvFW5'
          <5> SUFFICES ASSUME NEW q \in ProcSet,
                              pc'[q] \in {"O1B", "O1C", "O1D", "U1B", "U1C", "U1D"},
                              B'[arg[q].i] # b'[q]
                       PROVE  B'[arg[q].i].seq > b'[q].seq
            BY Zenon DEF InvFW5
          <5> SUFFICES ASSUME q = p
                       PROVE  FALSE
            BY Zenon DEF InvFW5
          <5>1. b'[p] = B[arg[p].i]
            BY Zenon
          <5>2. b'[p] = B'[arg[p].i]
            BY <5>1, Zenon
          <5> QED
            BY <5>2
        <4>7. InvFW6'
          <5> SUFFICES ASSUME NEW q \in ProcSet,
                              \/ (pc'[q] \in {"O1A", "U1A"} /\ k'[q] = 2)
                              \/ (/\ pc'[q] \in {"O1B", "O1C", "O1D", "U1B", "U1C", "U1D"} 
                                  /\ B[arg[q].i] # b'[q] 
                                  /\ k'[q] = 1)
                       PROVE  \/ B[arg[q].i].seq >= xhat[q]
                              \/ (\A q1 \in ProcSet : (/\ pc'[q1] \in {"O1C", "O1D", "U1C", "U1D"}
                                                       /\ arg[q1].i = arg[q].i
                                                       /\ b'[q1] = B[arg[q].i]) => x[q1] >= xhat[q])
            BY Zenon DEF InvFW6
          <5>1. CASE /\ pc'[q] \in {"O1A", "U1A"} 
                     /\ k'[q] = 2
            <6> USE <5>1
            <6>1. pc[q] \in {"O1A", "U1A"} /\ k[q] = 2
              BY Zenon
            <6>2. \/ B[arg[q].i].seq >= xhat[q]
                  \/ (\A q1 \in ProcSet : (/\ pc[q1] \in {"O1C", "O1D", "U1C", "U1D"}
                                           /\ arg[q1].i = arg[q].i
                                           /\ b[q1] = B[arg[q].i]) => x[q1] >= xhat[q])
              BY <6>1 DEF InvFW6
            <6>3. CASE B[arg[q].i].seq >= xhat[q]
              BY <6>3
            <6> SUFFICES ASSUME (\A q1 \in ProcSet : (/\ pc[q1] \in {"O1C", "O1D", "U1C", "U1D"}
                                                      /\ arg[q1].i = arg[q].i
                                                      /\ b[q1] = B[arg[q].i]) => x[q1] >= xhat[q])
                         PROVE  (\A q1 \in ProcSet : (/\ pc'[q1] \in {"O1C", "O1D", "U1C", "U1D"}
                                                      /\ arg[q1].i = arg[q].i
                                                      /\ b'[q1] = B[arg[q].i]) => x[q1] >= xhat[q])
              BY <6>2, <6>3
            <6> SUFFICES ASSUME NEW q1 \in ProcSet,
                                pc'[q1] \in {"O1C", "O1D", "U1C", "U1D"},
                                arg[q1].i = arg[q].i,
                                b'[q1] = B[arg[q].i]
                         PROVE  x[q1] >= xhat[q]
              OBVIOUS
            <6>4. q1 # p
              BY Zenon
            <6> QED
              BY <6>4, Zenon
          <5>2. CASE /\ pc'[q] \in {"O1B", "O1C", "O1D", "U1B", "U1C", "U1D"}
                     /\ B[arg[q].i] # b'[q]
                     /\ k'[q] = 1
            <6> USE <5>2
            <6>1. q # p
              BY ZenonT(90)
            <6>2. /\ pc[q] \in {"O1B", "O1C", "O1D", "U1B", "U1C", "U1D"}
                  /\ B[arg[q].i] # b[q]
                  /\ k[q] = 1
              BY <6>1, Zenon
            <6>3. \/ B[arg[q].i].seq >= xhat[q]
                  \/ (\A q1 \in ProcSet : (/\ pc[q1] \in {"O1C", "O1D", "U1C", "U1D"}
                                           /\ arg[q1].i = arg[q].i
                                           /\ b[q1] = B[arg[q].i]) => x[q1] >= xhat[q])
              BY <6>2 DEF InvFW6
            <6>4. CASE B[arg[q].i].seq >= xhat[q]
              BY <6>4
            <6> SUFFICES ASSUME (\A q1 \in ProcSet : (/\ pc[q1] \in {"O1C", "O1D", "U1C", "U1D"}
                                                      /\ arg[q1].i = arg[q].i
                                                      /\ b[q1] = B[arg[q].i]) => x[q1] >= xhat[q])
                         PROVE  (\A q1 \in ProcSet : (/\ pc'[q1] \in {"O1C", "O1D", "U1C", "U1D"}
                                                      /\ arg[q1].i = arg[q].i
                                                      /\ b'[q1] = B[arg[q].i]) => x[q1] >= xhat[q])
              BY <6>3, <6>4
            <6> SUFFICES ASSUME NEW q1 \in ProcSet,
                                pc'[q1] \in {"O1C", "O1D", "U1C", "U1D"},
                                arg[q1].i = arg[q].i,
                                b'[q1] = B[arg[q].i]
                         PROVE  x[q1] >= xhat[q]
              OBVIOUS
            <6>5. q1 # p
              BY Zenon
            <6> QED
              BY <6>5, Zenon
          <5>3. QED
            BY <5>1, <5>2
        <4>8. InvFW7'
          <5> SUFFICES ASSUME NEW q \in ProcSet,
                              pc'[q] \in {"O1B", "O1C", "O1D", "U1B", "U1C", "U1D"},
                              B[arg[q].i] # b'[q],
                              k'[q] = 2
                       PROVE  B[arg[q].i].seq >= xhat[q]
            BY Zenon DEF InvFW7
          <5>1. CASE q # p
            BY <5>1, Zenon DEF InvFW7
          <5> SUFFICES ASSUME q = p
                       PROVE  FALSE
            BY <5>1
          <5>2. B[arg[p].i] = b'[p]
            BY Zenon
          <5> QED
            BY <5>2
        <4>9. InvFW8'
          BY Zenon DEF InvFW8
        <4>10. InvFW9'
          BY ZenonT(90) DEF InvFW9
        <4>11. QED
          BY <4>1, <4>10, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9 DEF Inv
      <3>3. CASE LineAction = O1B(p)
        <4> USE <3>3 DEF Inv, TypeOK, O1B
        <4> /\ p = Scanner
            /\ p \notin UpdSet
            /\ UpdSet \in SUBSET ProcSet
          BY Zenon DEF O1B, Scanner, UpdSet
        <4>1. TypeOK'
          BY NextTypeOK
        <4>2. InvFW1'
          BY ZenonT(90) DEF InvFW1
        <4>3. InvFW2'
          BY ZenonT(90) DEF InvFW2
        <4>4. InvFW3'
          BY ZenonT(90) DEF InvFW3
        <4>5. InvFW4'
          <5> SUFFICES ASSUME b[p].seq # X
                       PROVE  X >= xhat[p] /\ xhat[p] > b[p].seq
            BY ZenonT(90) DEF InvFW4
          <5>1. X = xhat[p]
            BY Zenon DEF InvFW2
          <5>2. arg[p].i \in 1..M
            BY RemDef, Zenon DEF ArgsOf, LineIDtoOp
          <5>3. X >= B[arg[p].i].seq
            BY Zenon, <5>2 DEF InvFW1
          <5>4. xhat[p] >= B[arg[p].i].seq
            BY <5>1, <5>3
          <5>5. B[arg[p].i].seq = b[p].seq \/ B[arg[p].i].seq > b[p].seq
            BY Zenon DEF InvFW5
          <5>6. B[arg[p].i].seq >= b[p].seq
            BY <5>5, <5>2
          <5>7. xhat[p] >= b[p].seq
            BY <5>2, <5>4, <5>6
          <5> QED
            BY <5>1, <5>7
        <4>6. InvFW5'
          BY ZenonT(90) DEF InvFW5
        <4>7. InvFW6'
          <5> SUFFICES ASSUME NEW q \in ProcSet,
                              \/ (pc'[q] \in {"O1A", "U1A"} /\ k'[q] = 2)
                              \/ (/\ pc'[q] \in {"O1B", "O1C", "O1D", "U1B", "U1C", "U1D"} 
                                  /\ B[arg[q].i] # b[q] 
                                  /\ k'[q] = 1)
                       PROVE  (\/ B[arg[q].i].seq >= xhat[q]
                               \/ (\A q1 \in ProcSet : (/\ pc'[q1] \in {"O1C", "O1D", "U1C", "U1D"}
                                                        /\ arg[q1].i = arg[q].i
                                                        /\ b[q1] = B[arg[q].i]) => x'[q1] >= xhat[q]))
            BY Zenon DEF InvFW6
          <5>1. CASE /\ pc'[q] \in {"O1A", "U1A"} 
                     /\ k'[q] = 2
            <6> USE <5>1
            <6>1. pc[q] \in {"O1A", "U1A"} /\ k[q] = 2
              BY Zenon
            <6>2. \/ B[arg[q].i].seq >= xhat[q]
                  \/ (\A q1 \in ProcSet : (/\ pc[q1] \in {"O1C", "O1D", "U1C", "U1D"}
                                           /\ arg[q1].i = arg[q].i
                                           /\ b[q1] = B[arg[q].i]) => x[q1] >= xhat[q])
              BY <6>1 DEF InvFW6
            <6>3. CASE B[arg[q].i].seq >= xhat[q]
              BY <6>3
            <6> SUFFICES ASSUME (\A q1 \in ProcSet : (/\ pc[q1] \in {"O1C", "O1D", "U1C", "U1D"}
                                                      /\ arg[q1].i = arg[q].i
                                                      /\ b[q1] = B[arg[q].i]) => x[q1] >= xhat[q])
                         PROVE  (\A q1 \in ProcSet : (/\ pc'[q1] \in {"O1C", "O1D", "U1C", "U1D"}
                                                      /\ arg[q1].i = arg[q].i
                                                      /\ b'[q1] = B[arg[q].i]) => x[q1] >= xhat[q])
              BY <6>2, <6>3
            <6> SUFFICES ASSUME NEW q1 \in ProcSet,
                                pc'[q1] \in {"O1C", "O1D", "U1C", "U1D"},
                                arg[q1].i = arg[q].i,
                                b'[q1] = B[arg[q].i]
                         PROVE  x[q1] >= xhat[q]
              OBVIOUS
            <6>4. q1 # p
              BY Zenon
            <6> QED
              BY <6>4, Zenon
          <5>2. CASE /\ pc'[q] \in {"O1B", "O1C", "O1D", "U1B", "U1C", "U1D"} 
                     /\ B[arg[q].i] # b[q] 
                     /\ k'[q] = 1
          <5>3. QED
            BY <5>1, <5>2
        <4>8. InvFW7'
          BY ZenonT(90) DEF InvFW7
        <4>9. InvFW8'
          BY Zenon
        <4>10. InvFW9'
          BY ZenonT(90) DEF InvFW9
        <4>11. QED
          BY <4>1, <4>10, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9 DEF Inv
      <3>4. CASE LineAction = O1C(p)
      <3>5. CASE LineAction = O1D(p)
      <3>6. CASE LineAction = O2(p)
      <3>7. CASE LineAction = U1A(p)
      <3>8. CASE LineAction = U1B(p)
      <3>9. CASE LineAction = U1C(p)
      <3>10. CASE LineAction = U1D(p)
      <3>11. CASE LineAction = U2(p)
      <3> QED
        BY Zenon, <3>1, <3>2, <3>3, <3>4, <3>5, <3>6,
           <3>7, <3>8, <3>9, <3>10, <3>11 DEF IntLines
    <2>3. CASE ReturnAction
      <3> SUFFICES ASSUME NEW p \in ProcSet,
                          NEW LineAction \in RetLines(p),
                          LineAction,
                          UNCHANGED xhat
                   PROVE  Inv'
        BY <2>3, Zenon DEF ReturnAction
      <3>1. CASE LineAction = C2(p)
      <3>2. CASE LineAction = O3(p)
      <3>3. CASE LineAction = U3(p)
      <3> QED
        BY Zenon, <3>1, <3>2, <3>3 DEF RetLines
    <2> QED
      BY <2>1, <2>2, <2>3 DEF Next 
  <1>2. CASE UNCHANGED augvars
  <1> QED
    BY <1>1, <1>2

================================================================================
\* Modification History
\* Last modified Fri Aug 23 10:23:08 EDT 2024 by uguryavuz
\* Created Wed Mar 13 19:30:05 EDT 2024 by uguryavuz
