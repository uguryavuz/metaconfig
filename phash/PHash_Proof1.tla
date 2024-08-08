--------------------------- MODULE PHash_Proof1 ---------------------------
EXTENDS  PHash2_Impl, SequenceTheorems, FiniteSets, TLAPS
INSTANCE Augmentation

VARIABLE P
vars == algvars \o <<pc, arg, ret, P>>

ASSUME HashDef == Hash \in [KeyDomain -> 1..N]
ASSUME NDef    == N \in Nat \ {0}
ASSUME NULLDef == /\ NULL \notin Addrs
                  /\ NULL \notin ValDomain
ASSUME RemDef  == RemainderID \notin {"F1", "F2", "F3",
                                      "I1", "I2", "I3", "I4", "I5",
                                      "U1", "U2", "U3", "U4", "U5",
                                      "R1", "R2", "R3", "R4", "R5"}

AInit == /\ Init
         /\ P = {[state |-> [k \in KeyDomain |-> NULL],
                  op    |-> [p \in ProcSet   |-> BOT],
                  arg   |-> [p \in ProcSet   |-> BOT],
                  res   |-> [p \in ProcSet   |-> BOT]]}

L0(p) == /\ pc[p] = RemainderID
         /\ \E op \in OpNames :
            /\ pc' = [pc EXCEPT ![p] = OpToInvocLine(op)]
            /\ \E new_arg \in ArgsOf(op) :
               /\ arg' = [arg EXCEPT ![p] = new_arg]
               /\ P' = Evolve(Invoke(P, p, op, new_arg))
         /\ UNCHANGED algvars
         /\ UNCHANGED ret

IntLine(p) == \E Line \in IntLines(p) : /\ Line
                                        /\ P' = Evolve(P)

RetLine(p) == \E Line \in RetLines(p) : /\ Line
                                        /\ P' = Filter(Evolve(P), p, ret'[p])

Next == \E p \in ProcSet : \/ L0(p)
                           \/ IntLine(p)
                           \/ RetLine(p)

Spec == AInit /\ [][Next]_vars     

\* Type correctness for P

PTypeOK == P \in SUBSET ConfigDomain

LEMMA InitPTypeOK == AInit => PTypeOK
  BY DEF AInit, Init, PTypeOK, ConfigDomain, OpDomain, ArgDomain, ResDomain, StateDomain

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
      <3>1.  CASE Line = F1(p) BY <3>1  DEF F1
      <3>2.  CASE Line = F2(p) BY <3>2  DEF F2
      <3>3.  CASE Line = I1(p) BY <3>3  DEF I1
      <3>4.  CASE Line = I2(p) BY <3>4  DEF I2
      <3>5.  CASE Line = I3(p) BY <3>5  DEF I3
      <3>6.  CASE Line = I4(p) BY <3>6  DEF I4
      <3>7.  CASE Line = U1(p) BY <3>7  DEF U1
      <3>8.  CASE Line = U2(p) BY <3>8  DEF U2
      <3>9.  CASE Line = U3(p) BY <3>9  DEF U3
      <3>10. CASE Line = U4(p) BY <3>10 DEF U4
      <3>11. CASE Line = R1(p) BY <3>11 DEF R1
      <3>12. CASE Line = R2(p) BY <3>12 DEF R2
      <3>13. CASE Line = R3(p) BY <3>13 DEF R3
      <3>14. CASE Line = R4(p) BY <3>14 DEF R4
      <3> QED
        BY Zenon, <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9, <3>10, <3>11, <3>12, <3>13, <3>14
    <2>3. ASSUME NEW p \in ProcSet, 
                 RetLine(p)
          PROVE  PTypeOK'
      <3> SUFFICES ASSUME NEW Line \in RetLines(p),
                          Line,
                          P' = Filter(Evolve(P), p, ret'[p])
                   PROVE  PTypeOK'
        BY <2>3, Zenon DEF RetLine
      <3> USE DEF Evolve, Filter
      <3>1. CASE Line = F3(p) BY <3>1 DEF F3
      <3>2. CASE Line = I5(p) BY <3>2 DEF I5
      <3>3. CASE Line = U5(p) BY <3>3 DEF U5
      <3>4. CASE Line = R5(p) BY <3>4 DEF R5
      <3> QED
        BY Zenon, <3>1, <3>2, <3>3, <3>4 DEF RetLines
    <2> QED
      BY <1>1, <2>1, <2>2, <2>3 DEF Next
  <1>2. CASE UNCHANGED vars
    BY <1>2 DEF vars, algvars
  <1> QED
    BY <1>1, <1>2

AddrsOK == \A p \in ProcSet : pc[p] \in {"I4", "U4", "R4"}
              => /\ \A q \in ProcSet : (p # q => /\ newbkt[p] # bucket[q]
                                                 /\ newbkt[p] # newbkt[q])
                 /\ \A idx \in 1..N  : (A[idx] # newbkt[p])
                 /\ newbkt[p] # bucket[p]
                 /\ newbkt[p] \in AllocAddrs
             
BktOK == \A p \in ProcSet : /\ pc[p] \in {"I3", "I4"} => (/\ ~KeyInBktAtAddr(arg[p].key, bucket[p]) 
                                                          /\ r[p] = NULL)
                            /\ pc[p] \in {"U3", "U4"} => (IF KeyInBktAtAddr(arg[p].key, bucket[p])
                                                             THEN (/\ r[p] = ValOfKeyInBktAtAddr(arg[p].key, bucket[p]) 
                                                                   /\ r[p] # NULL)
                                                             ELSE r[p] = NULL)
                            /\ pc[p] \in {"R3", "R4"} => (/\ KeyInBktAtAddr(arg[p].key, bucket[p]) 
                                                          /\ r[p] = ValOfKeyInBktAtAddr(arg[p].key, bucket[p]) 
                                                          /\ r[p] # NULL)

Uniq == \A addr \in AllocAddrs : LET bucket_arr == MemLocs[addr] IN
           \A j1, j2 \in 1..Len(bucket_arr) : bucket_arr[j1].key = bucket_arr[j2].key => j1 = j2
           
NewBktOK == \A p \in ProcSet : 
               /\ pc[p] = "I4" => /\ KeyInBktAtAddr(arg[p].key, newbkt[p])
                                  /\ ValOfKeyInBktAtAddr(arg[p].key, newbkt[p]) = arg[p].val
                                  /\ \A k \in KeyDomain : k # arg[p].key => /\ KeyInBktAtAddr(k, bucket[p]) = KeyInBktAtAddr(k, newbkt[p])
                                                                            /\ KeyInBktAtAddr(k, bucket[p]) =>
                                                                               (ValOfKeyInBktAtAddr(k, bucket[p]) = ValOfKeyInBktAtAddr(k, newbkt[p]))
               /\ pc[p] = "U4" => /\ KeyInBktAtAddr(arg[p].key, newbkt[p])
                                  /\ ValOfKeyInBktAtAddr(arg[p].key, newbkt[p]) = arg[p].val
                                  /\ \A k \in KeyDomain : k # arg[p].key => /\ KeyInBktAtAddr(k, bucket[p]) = KeyInBktAtAddr(k, newbkt[p])
                                                                            /\ KeyInBktAtAddr(k, bucket[p]) =>
                                                                               (ValOfKeyInBktAtAddr(k, bucket[p]) = ValOfKeyInBktAtAddr(k, newbkt[p]))
               /\ pc[p] = "R4" => /\ ~KeyInBktAtAddr(arg[p].key, newbkt[p])
                                  /\ \A k \in KeyDomain : k # arg[p].key => /\ KeyInBktAtAddr(k, bucket[p]) = KeyInBktAtAddr(k, newbkt[p])
                                                                            /\ KeyInBktAtAddr(k, bucket[p]) =>
                                                                               (ValOfKeyInBktAtAddr(k, bucket[p]) = ValOfKeyInBktAtAddr(k, newbkt[p]))

TOK == /\ pc \in [ProcSet -> LineIDs]
       /\ A \in [1..N -> AllocAddrs \union {NULL}]
       /\ MemLocs \in [Addrs -> Seq([key: KeyDomain, val: ValDomain])]
       /\ AllocAddrs \in SUBSET Addrs
       /\ bucket \in [ProcSet -> AllocAddrs \union {NULL}]
       /\ newbkt \in [ProcSet -> AllocAddrs \union {NULL}]
       /\ r \in [ProcSet -> ValDomain \union {NULL}]
       /\ arg \in [ProcSet -> ArgDomain]
       /\ ret \in [ProcSet -> RetDomain]
       /\ \A p \in ProcSet : (pc[p] # RemainderID) => arg[p] \in ArgsOf(LineIDtoOp(pc[p]))
       
Inv == /\ PTypeOK
       /\ TOK
       /\ AddrsOK
       /\ BktOK
       /\ Uniq
       /\ NewBktOK
        
LEMMA InitInv == AInit => Inv
  <1> USE RemDef, InitPTypeOK DEF TOK, AInit, Init, LineIDs, RetDomain, AddrsOK, BktOK, NewBktOK, Uniq
  <1> SUFFICES ASSUME AInit
               PROVE  Inv
    OBVIOUS
  <1>1. PTypeOK
    OBVIOUS
  <1>2. TOK
    OBVIOUS
  <1>3. AddrsOK
    OBVIOUS
  <1>4. BktOK
    OBVIOUS
  <1>5. Uniq
    OBVIOUS
  <1>6. NewBktOK
    OBVIOUS
  <1> QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF Inv
  
LEMMA NextInv == Inv /\ [Next]_vars => Inv'
  <1> USE DEF Inv, TOK
  <1> SUFFICES ASSUME Inv, [Next]_vars
               PROVE  Inv'
    OBVIOUS
  <1>1. CASE Next
    <2>1. ASSUME NEW p \in ProcSet, 
                 L0(p)
          PROVE  Inv'
      <3> USE <2>1 DEF L0, algvars
      <3>1. PTypeOK'
        BY NextPTypeOK
      <3>2. (A       \in [1..N    -> AllocAddrs \union {NULL}])'
        OBVIOUS
      <3>3. (MemLocs \in [Addrs   -> Seq([key: KeyDomain, val: ValDomain])])'
        <4> DEFINE D == Addrs
        <4> DEFINE R == Seq([key: KeyDomain, val: ValDomain])
        <4>0. MemLocs \in [D -> R]
          BY Zenon
        <4> SUFFICES MemLocs' \in [D' -> R']
          BY Zenon
        <4>1. D = D'
          OBVIOUS
        <4>2. R = R'
          OBVIOUS
        <4>3. MemLocs = MemLocs'
          OBVIOUS
        <4> HIDE DEF D, R
        <4> QED
          BY <4>0, <4>1, <4>2, <4>3
      <3>4. (AllocAddrs \in SUBSET Addrs)'
        OBVIOUS
      <3>5. (bucket  \in [ProcSet -> AllocAddrs \union {NULL}])'
        OBVIOUS
      <3>6. (newbkt  \in [ProcSet -> AllocAddrs \union {NULL}])'
        OBVIOUS
      <3>7. (r       \in [ProcSet -> ValDomain \union {NULL}])'
        OBVIOUS
      <3>8. (ret     \in [ProcSet -> RetDomain])'
        BY DEF RetDomain
      <3> SUFFICES /\ pc' \in [ProcSet -> LineIDs]
                   /\ arg' \in [ProcSet -> ArgDomain]
                   /\ \A q \in ProcSet : (pc'[q] # RemainderID) => arg'[q] \in ArgsOf(LineIDtoOp(pc'[q]))
                   /\ AddrsOK'
                   /\ BktOK'
                   /\ Uniq'
                   /\ NewBktOK'
        BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, Zenon
      <3> PICK op \in OpNames :
                  /\ pc' = [pc EXCEPT ![p] = OpToInvocLine(op)]
                  /\ \E new_arg \in ArgsOf(op) : arg' = [arg EXCEPT ![p] = new_arg]
        BY Zenon
      <3> PICK new_arg \in ArgsOf(op) : arg' = [arg EXCEPT ![p] = new_arg]
        BY Zenon
      <3>11. CASE op = "Find"
        <4> USE <3>11
        <4>1. pc' \in [ProcSet -> LineIDs]
          BY Zenon DEF LineIDs, OpToInvocLine
        <4>2. arg' \in [ProcSet -> ArgDomain]
          BY DEF ArgsOf, ArgDomain
        <4>3. \A q \in ProcSet : (pc'[q] # RemainderID) => arg'[q] \in ArgsOf(LineIDtoOp(pc'[q]))
          <5> SUFFICES ASSUME NEW q \in ProcSet,
                              pc'[q] # RemainderID
                       PROVE  arg'[q] \in ArgsOf(LineIDtoOp(pc'[q]))
            OBVIOUS
          <5>1. CASE q = p
            <6> SUFFICES new_arg \in ArgsOf(LineIDtoOp(OpToInvocLine(op)))
              BY <5>1
            <6>1. LineIDtoOp(OpToInvocLine(op)) = "Find"
              BY DEF LineIDtoOp, OpToInvocLine
            <6> QED
              BY <6>1
          <5>2. CASE q # p
            BY <5>2
          <5> QED
            BY <5>1, <5>2
        <4>4. pc'[p] = "F1"
          BY Zenon DEF OpToInvocLine
        <4>5. AddrsOK'
          <5> SUFFICES ASSUME NEW p_1 \in ProcSet',
                              (pc[p_1] \in {"I4", "U4", "R4"})'
                       PROVE  (/\ \A q \in ProcSet : (p_1 # q => /\ newbkt[p_1] # bucket[q]
                                                                 /\ newbkt[p_1] # newbkt[q])
                               /\ \A idx \in 1..N  : (A[idx] # newbkt[p_1])
                               /\ newbkt[p_1] # bucket[p_1]
                               /\ newbkt[p_1] \in AllocAddrs)'
            BY DEF AddrsOK
          <5>1. (\A q \in ProcSet : (p_1 # q => /\ newbkt[p_1] # bucket[q]
                                                /\ newbkt[p_1] # newbkt[q]))'
            BY <4>4 DEF AddrsOK
          <5>2. (\A idx \in 1..N  : (A[idx] # newbkt[p_1]))'
            BY <4>4 DEF AddrsOK
          <5>3. (newbkt[p_1] # bucket[p_1])'
            BY <4>4 DEF AddrsOK
          <5>4. (newbkt[p_1] \in AllocAddrs)'
            BY <4>4 DEF AddrsOK
          <5>5. QED
            BY <5>1, <5>2, <5>3, <5>4
        <4>6. BktOK'
          <5> SUFFICES ASSUME NEW q \in ProcSet
                       PROVE  (/\ pc'[q] \in {"I3", "I4"} => (/\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                                                              /\ r'[q] = NULL)
                               /\ pc'[q] \in {"U3", "U4"} => (IF KeyInBktAtAddr(arg[q].key, bucket[q])'
                                                                  THEN (/\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                                                                        /\ r'[q] # NULL)
                                                                  ELSE r'[q] = NULL)
                               /\ pc'[q] \in {"R3", "R4"} => (/\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                                                              /\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                                                              /\ r'[q] # NULL))
            BY DEF BktOK
          <5> USE RemDef, <4>4
          <5>1. CASE pc'[q] \in {"I3", "I4"}
            <6> USE <5>1
            <6> SUFFICES ~KeyInBktAtAddr(arg[q].key, bucket[q])' /\ r'[q] = NULL
              OBVIOUS
            <6>1. ~KeyInBktAtAddr(arg[q].key, bucket[q]) /\ r[q] = NULL
              BY Zenon DEF BktOK
            <6> QED
              BY <6>1, Zenon DEF KeyInBktAtAddr
          <5>2. CASE pc'[q] \in {"U3", "U4"}
            <6> USE <5>2
            <6> SUFFICES IF KeyInBktAtAddr(arg[q].key, bucket[q])'
                            THEN (/\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                                  /\ r'[q] # NULL)
                            ELSE r'[q] = NULL
              OBVIOUS
            <6>1. IF KeyInBktAtAddr(arg[q].key, bucket[q])
                     THEN (/\ r[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                           /\ r[q] # NULL)
                     ELSE r[q] = NULL
              BY Zenon DEF BktOK
            <6>2. KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
              BY Zenon DEF KeyInBktAtAddr
            <6>3. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs'[bucket'[q]][CHOOSE index \in 1..Len(MemLocs'[bucket'[q]]) :
                                   MemLocs'[bucket'[q]][index].key = arg'[q].key].val
              BY DEF ValOfKeyInBktAtAddr
            <6>4. MemLocs = MemLocs' /\ arg[q] = arg'[q] /\ bucket[q] = bucket'[q]
              BY Zenon
            <6>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs[bucket'[q]][CHOOSE index \in 1..Len(MemLocs[bucket'[q]]) :
                                  MemLocs[bucket'[q]][index].key = arg[q].key].val
              BY Zenon, <6>3, <6>4
            <6>6. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs[bucket[q]][CHOOSE index \in 1..Len(MemLocs[bucket[q]]) :
                                 MemLocs[bucket[q]][index].key = arg[q].key].val
              BY <6>4, <6>5
            <6>7. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
              BY <6>6, Zenon DEF ValOfKeyInBktAtAddr
            <6> QED
              BY <6>1, <6>2, <6>7, Zenon
          <5>3. CASE pc'[q] \in {"R3", "R4"}
            <6> USE <5>3
            <6> SUFFICES /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                         /\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                         /\ r'[q] # NULL
              OBVIOUS
            <6>1. /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                  /\ r[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                  /\ r[q] # NULL
              BY Zenon DEF BktOK
            <6>2. KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
              BY Zenon DEF KeyInBktAtAddr
            <6>3. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs'[bucket'[q]][CHOOSE index \in 1..Len(MemLocs'[bucket'[q]]) :
                                   MemLocs'[bucket'[q]][index].key = arg'[q].key].val
              BY DEF ValOfKeyInBktAtAddr
            <6>4. MemLocs = MemLocs' /\ arg[q] = arg'[q] /\ bucket[q] = bucket'[q]
              BY Zenon
            <6>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs[bucket'[q]][CHOOSE index \in 1..Len(MemLocs[bucket'[q]]) :
                                  MemLocs[bucket'[q]][index].key = arg[q].key].val
              BY Zenon, <6>3, <6>4
            <6>6. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs[bucket[q]][CHOOSE index \in 1..Len(MemLocs[bucket[q]]) :
                                 MemLocs[bucket[q]][index].key = arg[q].key].val
              BY <6>4, <6>5
            <6>7. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
              BY <6>6, Zenon DEF ValOfKeyInBktAtAddr
            <6> QED
              BY <6>1, <6>2, <6>7, Zenon
          <5> QED
            BY <5>1, <5>2, <5>3
        <4>7. Uniq'
          <5> SUFFICES ASSUME NEW addr \in AllocAddrs', 
                              NEW bucket_arr, bucket_arr = MemLocs'[addr],
                              NEW j1 \in 1..Len(bucket_arr),
                              NEW j2 \in 1..Len(bucket_arr),
                              bucket_arr[j1].key = bucket_arr[j2].key
                       PROVE  j1 = j2
            BY Zenon DEF Uniq
          <5> QED
            BY Zenon DEF Uniq
        <4>8. NewBktOK'
          <5> SUFFICES ASSUME NEW q \in ProcSet
                       PROVE  /\ pc'[q] = "I4" => /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                                  /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg'[q].val
                                                  /\ \A k \in KeyDomain : k # arg'[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                             /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                                (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
                              /\ pc'[q] = "U4" => /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                                  /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg'[q].val
                                                  /\ \A k \in KeyDomain : k # arg'[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                             /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                                (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
                              /\ pc'[q] = "R4" => /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                                  /\ \A k \in KeyDomain : k # arg'[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                             /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                                (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
            BY DEF NewBktOK
          <5>0. ASSUME NEW k \in KeyDomain
                PROVE  /\ pc[q] \in {"I4", "U4", "R4"} => KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, bucket[q])'
                       /\ KeyInBktAtAddr(k, newbkt[q]) = KeyInBktAtAddr(k, newbkt[q])'
                       /\ pc[q] \in {"I4", "U4", "R4"} => ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])'
                       /\ ValOfKeyInBktAtAddr(k, newbkt[q]) = ValOfKeyInBktAtAddr(k, newbkt[q])'
            <6> USE <5>0
            <6>1. pc[q] \in {"I4", "U4", "R4"} => KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, bucket[q])'
              BY Zenon DEF KeyInBktAtAddr
            <6>2. KeyInBktAtAddr(k, newbkt[q]) = KeyInBktAtAddr(k, newbkt[q])'
              BY Zenon DEF KeyInBktAtAddr
            <6>3. pc[q] \in {"I4", "U4", "R4"} => ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])'
              <7> SUFFICES ASSUME pc[q] \in {"I4", "U4", "R4"}
                           PROVE  ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])'
                OBVIOUS
              <7> DEFINE bkt_arr == MemLocs'[bucket'[q]]
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
              <7>1. ValOfKeyInBktAtAddr(k, bucket[q])' = bkt_arr[idx].val
                BY Zenon DEF ValOfKeyInBktAtAddr
              <7>2. bkt_arr = MemLocs[bucket[q]] /\ bucket'[q] = bucket[q]
                BY Zenon
              <7>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
                BY Zenon
              <7>4. ValOfKeyInBktAtAddr(k, bucket[q]) = 
                    MemLocs[bucket[q]][CHOOSE index \in 1..Len(MemLocs[bucket[q]]) : MemLocs[bucket[q]][index].key = k].val
                BY Zenon DEF ValOfKeyInBktAtAddr
              <7>5. ValOfKeyInBktAtAddr(k, bucket[q]) = bkt_arr[idx].val
                BY <7>2, <7>3, <7>4, Zenon
              <7> QED
                BY <7>1, <7>5
            <6>4. ValOfKeyInBktAtAddr(k, newbkt[q]) = ValOfKeyInBktAtAddr(k, newbkt[q])'
              <7> DEFINE bkt_arr == MemLocs'[newbkt'[q]]
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
              <7>1. ValOfKeyInBktAtAddr(k, newbkt[q])' = bkt_arr[idx].val
                BY Zenon DEF ValOfKeyInBktAtAddr
              <7>2. bkt_arr = MemLocs[newbkt[q]]
                BY Zenon
              <7>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
                BY Zenon
              <7>4. ValOfKeyInBktAtAddr(k, newbkt[q]) = 
                    MemLocs[newbkt[q]][CHOOSE index \in 1..Len(MemLocs[newbkt[q]]) : MemLocs[newbkt[q]][index].key = k].val
                BY Zenon DEF ValOfKeyInBktAtAddr
              <7>5. ValOfKeyInBktAtAddr(k, newbkt[q]) = bkt_arr[idx].val
                BY <7>2, <7>3, <7>4, Zenon
              <7> QED
                BY <7>1, <7>5
            <6> QED
              BY <6>1, <6>2, <6>3, <6>4
          <5>1. CASE pc'[q] = "I4"
            <6> USE <5>1
            <6> arg[q] = arg'[q] /\ pc[q] = pc'[q]
              BY <4>4, Zenon
            <6> SUFFICES /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                         /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                         /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                   /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                      (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
              OBVIOUS
            <6>1A. pc'[q] = "I4" /\ arg'[q].key \in KeyDomain
              BY <4>3, Zenon, RemDef DEF ArgsOf, LineIDtoOp
            <6>1. pc[q] = "I4" /\ arg[q].key \in KeyDomain
              BY <6>1A, Zenon
            <6>2. /\ KeyInBktAtAddr(arg[q].key, newbkt[q])
                  /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q]) = arg[q].val
                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                            /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                               (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
              BY <6>1, Zenon DEF NewBktOK
            <6> QED
              BY <5>0, <6>1, <6>2, ZenonT(90)
          <5>2. CASE pc'[q] = "U4"
            <6> USE <5>2
            <6> arg[q] = arg'[q] /\ pc[q] = pc'[q]
              BY <4>4, Zenon
            <6> SUFFICES /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                         /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                         /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                   /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                      (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
              OBVIOUS
            <6>1A. pc'[q] = "U4" /\ arg'[q].key \in KeyDomain
              BY <4>3, Zenon, RemDef DEF ArgsOf, LineIDtoOp
            <6>1. pc[q] = "U4" /\ arg[q].key \in KeyDomain
              BY <6>1A, Zenon
            <6>2. /\ KeyInBktAtAddr(arg[q].key, newbkt[q])
                  /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q]) = arg[q].val
                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                            /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                               (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
              BY <6>1, Zenon DEF NewBktOK
            <6> QED
              BY <5>0, <6>1, <6>2, ZenonT(90)
          <5>3. CASE pc'[q] = "R4"
            <6> USE <5>3
            <6> arg[q] = arg'[q] /\ pc[q] = pc'[q]
              BY <4>4, Zenon
            <6> SUFFICES /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])'
                         /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                   /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                      (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
              OBVIOUS
            <6>1A. pc'[q] = "R4" /\ arg'[q].key \in KeyDomain
              BY <4>3, Zenon, RemDef DEF ArgsOf, LineIDtoOp
            <6>1. pc[q] = "R4" /\ arg[q].key \in KeyDomain
              BY <6>1A, Zenon
            <6>2. /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])
                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                            /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                               (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
              BY <6>1, Zenon DEF NewBktOK
            <6> QED
              BY <5>0, <6>1, <6>2, ZenonT(90)
          <5> QED
            BY <5>1, <5>2, <5>3
        <4> QED
          BY <4>1, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8
      <3>12. CASE op = "Insert"
        <4> USE <3>12
        <4>1. pc' \in [ProcSet -> LineIDs]
          BY Zenon DEF LineIDs, OpToInvocLine
        <4>2. arg' \in [ProcSet -> ArgDomain]
          BY DEF ArgsOf, ArgDomain
        <4>3. \A q \in ProcSet : (pc'[q] # RemainderID) => arg'[q] \in ArgsOf(LineIDtoOp(pc'[q]))
          <5> SUFFICES ASSUME NEW q \in ProcSet,
                              pc'[q] # RemainderID
                       PROVE  arg'[q] \in ArgsOf(LineIDtoOp(pc'[q]))
            OBVIOUS
          <5>1. CASE q = p
            <6> SUFFICES new_arg \in ArgsOf(LineIDtoOp(OpToInvocLine(op)))
              BY <5>1
            <6>1. LineIDtoOp(OpToInvocLine(op)) = "Insert"
              BY DEF LineIDtoOp, OpToInvocLine
            <6> QED
              BY <6>1
          <5>2. CASE q # p
            BY <5>2
          <5> QED
            BY <5>1, <5>2
        <4>4. pc'[p] = "I1"
          BY Zenon DEF OpToInvocLine
        <4>5. AddrsOK'
          <5> SUFFICES ASSUME NEW p_1 \in ProcSet',
                              (pc[p_1] \in {"I4", "U4", "R4"})'
                       PROVE  (/\ \A q \in ProcSet : (p_1 # q => /\ newbkt[p_1] # bucket[q]
                                                                 /\ newbkt[p_1] # newbkt[q])
                               /\ \A idx \in 1..N  : (A[idx] # newbkt[p_1])
                               /\ newbkt[p_1] # bucket[p_1]
                               /\ newbkt[p_1] \in AllocAddrs)'
            BY DEF AddrsOK
          <5>1. (\A q \in ProcSet : (p_1 # q => /\ newbkt[p_1] # bucket[q]
                                                /\ newbkt[p_1] # newbkt[q]))'
            BY <4>4 DEF AddrsOK
          <5>2. (\A idx \in 1..N  : (A[idx] # newbkt[p_1]))'
            BY <4>4 DEF AddrsOK
          <5>3. (newbkt[p_1] # bucket[p_1])'
            BY <4>4 DEF AddrsOK
          <5>4. (newbkt[p_1] \in AllocAddrs)'
            BY <4>4 DEF AddrsOK
          <5>5. QED
            BY <5>1, <5>2, <5>3, <5>4
        <4>6. BktOK'
          <5> SUFFICES ASSUME NEW q \in ProcSet
                       PROVE  (/\ pc'[q] \in {"I3", "I4"} => (/\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                                                              /\ r'[q] = NULL)
                               /\ pc'[q] \in {"U3", "U4"} => (IF KeyInBktAtAddr(arg[q].key, bucket[q])'
                                                                  THEN (/\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                                                                        /\ r'[q] # NULL)
                                                                  ELSE r'[q] = NULL)
                               /\ pc'[q] \in {"R3", "R4"} => (/\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                                                              /\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                                                              /\ r'[q] # NULL))
            BY DEF BktOK
          <5> USE RemDef, <4>4
          <5>1. CASE pc'[q] \in {"I3", "I4"}
            <6> USE <5>1
            <6> SUFFICES ~KeyInBktAtAddr(arg[q].key, bucket[q])' /\ r'[q] = NULL
              OBVIOUS
            <6>1. ~KeyInBktAtAddr(arg[q].key, bucket[q]) /\ r[q] = NULL
              BY Zenon DEF BktOK
            <6> QED
              BY <6>1, Zenon DEF KeyInBktAtAddr
          <5>2. CASE pc'[q] \in {"U3", "U4"}
            <6> USE <5>2
            <6> SUFFICES IF KeyInBktAtAddr(arg[q].key, bucket[q])'
                            THEN (/\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                                  /\ r'[q] # NULL)
                            ELSE r'[q] = NULL
              OBVIOUS
            <6>1. IF KeyInBktAtAddr(arg[q].key, bucket[q])
                     THEN (/\ r[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                           /\ r[q] # NULL)
                     ELSE r[q] = NULL
              BY Zenon DEF BktOK
            <6>2. KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
              BY Zenon DEF KeyInBktAtAddr
            <6>3. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs'[bucket'[q]][CHOOSE index \in 1..Len(MemLocs'[bucket'[q]]) :
                                   MemLocs'[bucket'[q]][index].key = arg'[q].key].val
              BY DEF ValOfKeyInBktAtAddr
            <6>4. MemLocs = MemLocs' /\ arg[q] = arg'[q] /\ bucket[q] = bucket'[q]
              BY Zenon
            <6>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs[bucket'[q]][CHOOSE index \in 1..Len(MemLocs[bucket'[q]]) :
                                  MemLocs[bucket'[q]][index].key = arg[q].key].val
              BY Zenon, <6>3, <6>4
            <6>6. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs[bucket[q]][CHOOSE index \in 1..Len(MemLocs[bucket[q]]) :
                                 MemLocs[bucket[q]][index].key = arg[q].key].val
              BY <6>4, <6>5
            <6>7. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
              BY <6>6, Zenon DEF ValOfKeyInBktAtAddr
            <6> QED
              BY <6>1, <6>2, <6>7, Zenon
          <5>3. CASE pc'[q] \in {"R3", "R4"}
            <6> USE <5>3
            <6> SUFFICES /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                         /\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                         /\ r'[q] # NULL
              OBVIOUS
            <6>1. /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                  /\ r[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                  /\ r[q] # NULL
              BY Zenon DEF BktOK
            <6>2. KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
              BY Zenon DEF KeyInBktAtAddr
            <6>3. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs'[bucket'[q]][CHOOSE index \in 1..Len(MemLocs'[bucket'[q]]) :
                                   MemLocs'[bucket'[q]][index].key = arg'[q].key].val
              BY DEF ValOfKeyInBktAtAddr
            <6>4. MemLocs = MemLocs' /\ arg[q] = arg'[q] /\ bucket[q] = bucket'[q]
              BY Zenon
            <6>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs[bucket'[q]][CHOOSE index \in 1..Len(MemLocs[bucket'[q]]) :
                                  MemLocs[bucket'[q]][index].key = arg[q].key].val
              BY Zenon, <6>3, <6>4
            <6>6. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs[bucket[q]][CHOOSE index \in 1..Len(MemLocs[bucket[q]]) :
                                 MemLocs[bucket[q]][index].key = arg[q].key].val
              BY <6>4, <6>5
            <6>7. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
              BY <6>6, Zenon DEF ValOfKeyInBktAtAddr
            <6> QED
              BY <6>1, <6>2, <6>7, Zenon
          <5> QED
            BY <5>1, <5>2, <5>3
        <4>7. Uniq'
          <5> SUFFICES ASSUME NEW addr \in AllocAddrs', 
                              NEW bucket_arr, bucket_arr = MemLocs'[addr],
                              NEW j1 \in 1..Len(bucket_arr),
                              NEW j2 \in 1..Len(bucket_arr),
                              bucket_arr[j1].key = bucket_arr[j2].key
                       PROVE  j1 = j2
            BY Zenon DEF Uniq
          <5> QED
            BY Zenon DEF Uniq
        <4>8. NewBktOK'
          <5> SUFFICES ASSUME NEW q \in ProcSet
                       PROVE  /\ pc'[q] = "I4" => /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                                  /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg'[q].val
                                                  /\ \A k \in KeyDomain : k # arg'[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                             /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                                (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
                              /\ pc'[q] = "U4" => /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                                  /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg'[q].val
                                                  /\ \A k \in KeyDomain : k # arg'[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                             /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                                (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
                              /\ pc'[q] = "R4" => /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                                  /\ \A k \in KeyDomain : k # arg'[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                             /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                                (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
            BY DEF NewBktOK
          <5>0. ASSUME NEW k \in KeyDomain
                PROVE  /\ pc[q] \in {"I4", "U4", "R4"} => KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, bucket[q])'
                       /\ KeyInBktAtAddr(k, newbkt[q]) = KeyInBktAtAddr(k, newbkt[q])'
                       /\ pc[q] \in {"I4", "U4", "R4"} => ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])'
                       /\ ValOfKeyInBktAtAddr(k, newbkt[q]) = ValOfKeyInBktAtAddr(k, newbkt[q])'
            <6> USE <5>0
            <6>1. pc[q] \in {"I4", "U4", "R4"} => KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, bucket[q])'
              BY Zenon DEF KeyInBktAtAddr
            <6>2. KeyInBktAtAddr(k, newbkt[q]) = KeyInBktAtAddr(k, newbkt[q])'
              BY Zenon DEF KeyInBktAtAddr
            <6>3. pc[q] \in {"I4", "U4", "R4"} => ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])'
              <7> SUFFICES ASSUME pc[q] \in {"I4", "U4", "R4"}
                           PROVE  ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])'
                OBVIOUS
              <7> DEFINE bkt_arr == MemLocs'[bucket'[q]]
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
              <7>1. ValOfKeyInBktAtAddr(k, bucket[q])' = bkt_arr[idx].val
                BY Zenon DEF ValOfKeyInBktAtAddr
              <7>2. bkt_arr = MemLocs[bucket[q]] /\ bucket'[q] = bucket[q]
                BY Zenon
              <7>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
                BY Zenon
              <7>4. ValOfKeyInBktAtAddr(k, bucket[q]) = 
                    MemLocs[bucket[q]][CHOOSE index \in 1..Len(MemLocs[bucket[q]]) : MemLocs[bucket[q]][index].key = k].val
                BY Zenon DEF ValOfKeyInBktAtAddr
              <7>5. ValOfKeyInBktAtAddr(k, bucket[q]) = bkt_arr[idx].val
                BY <7>2, <7>3, <7>4, Zenon
              <7> QED
                BY <7>1, <7>5
            <6>4. ValOfKeyInBktAtAddr(k, newbkt[q]) = ValOfKeyInBktAtAddr(k, newbkt[q])'
              <7> DEFINE bkt_arr == MemLocs'[newbkt'[q]]
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
              <7>1. ValOfKeyInBktAtAddr(k, newbkt[q])' = bkt_arr[idx].val
                BY Zenon DEF ValOfKeyInBktAtAddr
              <7>2. bkt_arr = MemLocs[newbkt[q]]
                BY Zenon
              <7>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
                BY Zenon
              <7>4. ValOfKeyInBktAtAddr(k, newbkt[q]) = 
                    MemLocs[newbkt[q]][CHOOSE index \in 1..Len(MemLocs[newbkt[q]]) : MemLocs[newbkt[q]][index].key = k].val
                BY Zenon DEF ValOfKeyInBktAtAddr
              <7>5. ValOfKeyInBktAtAddr(k, newbkt[q]) = bkt_arr[idx].val
                BY <7>2, <7>3, <7>4, Zenon
              <7> QED
                BY <7>1, <7>5
            <6> QED
              BY <6>1, <6>2, <6>3, <6>4
          <5>1. CASE pc'[q] = "I4"
            <6> USE <5>1
            <6> arg[q] = arg'[q] /\ pc[q] = pc'[q]
              BY <4>4, Zenon
            <6> SUFFICES /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                         /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                         /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                   /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                      (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
              OBVIOUS
            <6>1A. pc'[q] = "I4" /\ arg'[q].key \in KeyDomain
              BY <4>3, Zenon, RemDef DEF ArgsOf, LineIDtoOp
            <6>1. pc[q] = "I4" /\ arg[q].key \in KeyDomain
              BY <6>1A, Zenon
            <6>2. /\ KeyInBktAtAddr(arg[q].key, newbkt[q])
                  /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q]) = arg[q].val
                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                            /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                               (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
              BY <6>1, Zenon DEF NewBktOK
            <6> QED
              BY <5>0, <6>1, <6>2, ZenonT(90)
          <5>2. CASE pc'[q] = "U4"
            <6> USE <5>2
            <6> arg[q] = arg'[q] /\ pc[q] = pc'[q]
              BY <4>4, Zenon
            <6> SUFFICES /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                         /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                         /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                   /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                      (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
              OBVIOUS
            <6>1A. pc'[q] = "U4" /\ arg'[q].key \in KeyDomain
              BY <4>3, Zenon, RemDef DEF ArgsOf, LineIDtoOp
            <6>1. pc[q] = "U4" /\ arg[q].key \in KeyDomain
              BY <6>1A, Zenon
            <6>2. /\ KeyInBktAtAddr(arg[q].key, newbkt[q])
                  /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q]) = arg[q].val
                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                            /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                               (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
              BY <6>1, Zenon DEF NewBktOK
            <6> QED
              BY <5>0, <6>1, <6>2, ZenonT(90)
          <5>3. CASE pc'[q] = "R4"
            <6> USE <5>3
            <6> arg[q] = arg'[q] /\ pc[q] = pc'[q]
              BY <4>4, Zenon
            <6> SUFFICES /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])'
                         /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                   /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                      (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
              OBVIOUS
            <6>1A. pc'[q] = "R4" /\ arg'[q].key \in KeyDomain
              BY <4>3, Zenon, RemDef DEF ArgsOf, LineIDtoOp
            <6>1. pc[q] = "R4" /\ arg[q].key \in KeyDomain
              BY <6>1A, Zenon
            <6>2. /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])
                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                            /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                               (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
              BY <6>1, Zenon DEF NewBktOK
            <6> QED
              BY <5>0, <6>1, <6>2, ZenonT(90)
          <5> QED
            BY <5>1, <5>2, <5>3
        <4> QED
          BY <4>1, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8
      <3>13. CASE op = "Upsert"
        <4> USE <3>13
        <4>1. pc' \in [ProcSet -> LineIDs]
          BY Zenon DEF LineIDs, OpToInvocLine
        <4>2. arg' \in [ProcSet -> ArgDomain]
          BY DEF ArgsOf, ArgDomain
        <4>3. \A q \in ProcSet : (pc'[q] # RemainderID) => arg'[q] \in ArgsOf(LineIDtoOp(pc'[q]))
          <5> SUFFICES ASSUME NEW q \in ProcSet,
                              pc'[q] # RemainderID
                       PROVE  arg'[q] \in ArgsOf(LineIDtoOp(pc'[q]))
            OBVIOUS
          <5>1. CASE q = p
            <6> SUFFICES new_arg \in ArgsOf(LineIDtoOp(OpToInvocLine(op)))
              BY <5>1
            <6>1. LineIDtoOp(OpToInvocLine(op)) = "Upsert"
              BY DEF LineIDtoOp, OpToInvocLine
            <6> QED
              BY <6>1
          <5>2. CASE q # p
            BY <5>2
          <5> QED
            BY <5>1, <5>2
        <4>4. pc'[p] = "U1"
          BY Zenon DEF OpToInvocLine
        <4>5. AddrsOK'
          <5> SUFFICES ASSUME NEW p_1 \in ProcSet',
                              (pc[p_1] \in {"I4", "U4", "R4"})'
                       PROVE  (/\ \A q \in ProcSet : (p_1 # q => /\ newbkt[p_1] # bucket[q]
                                                                 /\ newbkt[p_1] # newbkt[q])
                               /\ \A idx \in 1..N  : (A[idx] # newbkt[p_1])
                               /\ newbkt[p_1] # bucket[p_1]
                               /\ newbkt[p_1] \in AllocAddrs)'
            BY DEF AddrsOK
          <5>1. (\A q \in ProcSet : (p_1 # q => /\ newbkt[p_1] # bucket[q]
                                                /\ newbkt[p_1] # newbkt[q]))'
            BY <4>4 DEF AddrsOK
          <5>2. (\A idx \in 1..N  : (A[idx] # newbkt[p_1]))'
            BY <4>4 DEF AddrsOK
          <5>3. (newbkt[p_1] # bucket[p_1])'
            BY <4>4 DEF AddrsOK
          <5>4. (newbkt[p_1] \in AllocAddrs)'
            BY <4>4 DEF AddrsOK
          <5>5. QED
            BY <5>1, <5>2, <5>3, <5>4
        <4>6. BktOK'
          <5> SUFFICES ASSUME NEW q \in ProcSet
                       PROVE  (/\ pc'[q] \in {"I3", "I4"} => (/\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                                                              /\ r'[q] = NULL)
                               /\ pc'[q] \in {"U3", "U4"} => (IF KeyInBktAtAddr(arg[q].key, bucket[q])'
                                                                  THEN (/\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                                                                        /\ r'[q] # NULL)
                                                                  ELSE r'[q] = NULL)
                               /\ pc'[q] \in {"R3", "R4"} => (/\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                                                              /\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                                                              /\ r'[q] # NULL))
            BY DEF BktOK
          <5> USE RemDef, <4>4
          <5>1. CASE pc'[q] \in {"I3", "I4"}
            <6> USE <5>1
            <6> SUFFICES ~KeyInBktAtAddr(arg[q].key, bucket[q])' /\ r'[q] = NULL
              OBVIOUS
            <6>1. ~KeyInBktAtAddr(arg[q].key, bucket[q]) /\ r[q] = NULL
              BY Zenon DEF BktOK
            <6> QED
              BY <6>1, Zenon DEF KeyInBktAtAddr
          <5>2. CASE pc'[q] \in {"U3", "U4"}
            <6> USE <5>2
            <6> SUFFICES IF KeyInBktAtAddr(arg[q].key, bucket[q])'
                            THEN (/\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                                  /\ r'[q] # NULL)
                            ELSE r'[q] = NULL
              OBVIOUS
            <6>1. IF KeyInBktAtAddr(arg[q].key, bucket[q])
                     THEN (/\ r[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                           /\ r[q] # NULL)
                     ELSE r[q] = NULL
              BY Zenon DEF BktOK
            <6>2. KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
              BY Zenon DEF KeyInBktAtAddr
            <6>3. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs'[bucket'[q]][CHOOSE index \in 1..Len(MemLocs'[bucket'[q]]) :
                                   MemLocs'[bucket'[q]][index].key = arg'[q].key].val
              BY DEF ValOfKeyInBktAtAddr
            <6>4. MemLocs = MemLocs' /\ arg[q] = arg'[q] /\ bucket[q] = bucket'[q]
              BY Zenon
            <6>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs[bucket'[q]][CHOOSE index \in 1..Len(MemLocs[bucket'[q]]) :
                                  MemLocs[bucket'[q]][index].key = arg[q].key].val
              BY Zenon, <6>3, <6>4
            <6>6. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs[bucket[q]][CHOOSE index \in 1..Len(MemLocs[bucket[q]]) :
                                 MemLocs[bucket[q]][index].key = arg[q].key].val
              BY <6>4, <6>5
            <6>7. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
              BY <6>6, Zenon DEF ValOfKeyInBktAtAddr
            <6> QED
              BY <6>1, <6>2, <6>7, Zenon
          <5>3. CASE pc'[q] \in {"R3", "R4"}
            <6> USE <5>3
            <6> SUFFICES /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                         /\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                         /\ r'[q] # NULL
              OBVIOUS
            <6>1. /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                  /\ r[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                  /\ r[q] # NULL
              BY Zenon DEF BktOK
            <6>2. KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
              BY Zenon DEF KeyInBktAtAddr
            <6>3. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs'[bucket'[q]][CHOOSE index \in 1..Len(MemLocs'[bucket'[q]]) :
                                   MemLocs'[bucket'[q]][index].key = arg'[q].key].val
              BY DEF ValOfKeyInBktAtAddr
            <6>4. MemLocs = MemLocs' /\ arg[q] = arg'[q] /\ bucket[q] = bucket'[q]
              BY Zenon
            <6>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs[bucket'[q]][CHOOSE index \in 1..Len(MemLocs[bucket'[q]]) :
                                  MemLocs[bucket'[q]][index].key = arg[q].key].val
              BY Zenon, <6>3, <6>4
            <6>6. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs[bucket[q]][CHOOSE index \in 1..Len(MemLocs[bucket[q]]) :
                                 MemLocs[bucket[q]][index].key = arg[q].key].val
              BY <6>4, <6>5
            <6>7. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
              BY <6>6, Zenon DEF ValOfKeyInBktAtAddr
            <6> QED
              BY <6>1, <6>2, <6>7, Zenon
          <5> QED
            BY <5>1, <5>2, <5>3
        <4>7. Uniq'
          <5> SUFFICES ASSUME NEW addr \in AllocAddrs', 
                              NEW bucket_arr, bucket_arr = MemLocs'[addr],
                              NEW j1 \in 1..Len(bucket_arr),
                              NEW j2 \in 1..Len(bucket_arr),
                              bucket_arr[j1].key = bucket_arr[j2].key
                       PROVE  j1 = j2
            BY Zenon DEF Uniq
          <5> QED
            BY Zenon DEF Uniq
        <4>8. NewBktOK'
          <5> SUFFICES ASSUME NEW q \in ProcSet
                       PROVE  /\ pc'[q] = "I4" => /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                                  /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg'[q].val
                                                  /\ \A k \in KeyDomain : k # arg'[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                             /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                                (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
                              /\ pc'[q] = "U4" => /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                                  /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg'[q].val
                                                  /\ \A k \in KeyDomain : k # arg'[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                             /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                                (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
                              /\ pc'[q] = "R4" => /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                                  /\ \A k \in KeyDomain : k # arg'[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                             /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                                (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
            BY DEF NewBktOK
          <5>0. ASSUME NEW k \in KeyDomain
                PROVE  /\ pc[q] \in {"I4", "U4", "R4"} => KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, bucket[q])'
                       /\ KeyInBktAtAddr(k, newbkt[q]) = KeyInBktAtAddr(k, newbkt[q])'
                       /\ pc[q] \in {"I4", "U4", "R4"} => ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])'
                       /\ ValOfKeyInBktAtAddr(k, newbkt[q]) = ValOfKeyInBktAtAddr(k, newbkt[q])'
            <6> USE <5>0
            <6>1. pc[q] \in {"I4", "U4", "R4"} => KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, bucket[q])'
              BY Zenon DEF KeyInBktAtAddr
            <6>2. KeyInBktAtAddr(k, newbkt[q]) = KeyInBktAtAddr(k, newbkt[q])'
              BY Zenon DEF KeyInBktAtAddr
            <6>3. pc[q] \in {"I4", "U4", "R4"} => ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])'
              <7> SUFFICES ASSUME pc[q] \in {"I4", "U4", "R4"}
                           PROVE  ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])'
                OBVIOUS
              <7> DEFINE bkt_arr == MemLocs'[bucket'[q]]
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
              <7>1. ValOfKeyInBktAtAddr(k, bucket[q])' = bkt_arr[idx].val
                BY Zenon DEF ValOfKeyInBktAtAddr
              <7>2. bkt_arr = MemLocs[bucket[q]] /\ bucket'[q] = bucket[q]
                BY Zenon
              <7>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
                BY Zenon
              <7>4. ValOfKeyInBktAtAddr(k, bucket[q]) = 
                    MemLocs[bucket[q]][CHOOSE index \in 1..Len(MemLocs[bucket[q]]) : MemLocs[bucket[q]][index].key = k].val
                BY Zenon DEF ValOfKeyInBktAtAddr
              <7>5. ValOfKeyInBktAtAddr(k, bucket[q]) = bkt_arr[idx].val
                BY <7>2, <7>3, <7>4, Zenon
              <7> QED
                BY <7>1, <7>5
            <6>4. ValOfKeyInBktAtAddr(k, newbkt[q]) = ValOfKeyInBktAtAddr(k, newbkt[q])'
              <7> DEFINE bkt_arr == MemLocs'[newbkt'[q]]
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
              <7>1. ValOfKeyInBktAtAddr(k, newbkt[q])' = bkt_arr[idx].val
                BY Zenon DEF ValOfKeyInBktAtAddr
              <7>2. bkt_arr = MemLocs[newbkt[q]]
                BY Zenon
              <7>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
                BY Zenon
              <7>4. ValOfKeyInBktAtAddr(k, newbkt[q]) = 
                    MemLocs[newbkt[q]][CHOOSE index \in 1..Len(MemLocs[newbkt[q]]) : MemLocs[newbkt[q]][index].key = k].val
                BY Zenon DEF ValOfKeyInBktAtAddr
              <7>5. ValOfKeyInBktAtAddr(k, newbkt[q]) = bkt_arr[idx].val
                BY <7>2, <7>3, <7>4, Zenon
              <7> QED
                BY <7>1, <7>5
            <6> QED
              BY <6>1, <6>2, <6>3, <6>4
          <5>1. CASE pc'[q] = "I4"
            <6> USE <5>1
            <6> arg[q] = arg'[q] /\ pc[q] = pc'[q]
              BY <4>4, Zenon
            <6> SUFFICES /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                         /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                         /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                   /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                      (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
              OBVIOUS
            <6>1A. pc'[q] = "I4" /\ arg'[q].key \in KeyDomain
              BY <4>3, Zenon, RemDef DEF ArgsOf, LineIDtoOp
            <6>1. pc[q] = "I4" /\ arg[q].key \in KeyDomain
              BY <6>1A, Zenon
            <6>2. /\ KeyInBktAtAddr(arg[q].key, newbkt[q])
                  /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q]) = arg[q].val
                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                            /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                               (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
              BY <6>1, Zenon DEF NewBktOK
            <6> QED
              BY <5>0, <6>1, <6>2, ZenonT(90)
          <5>2. CASE pc'[q] = "U4"
            <6> USE <5>2
            <6> arg[q] = arg'[q] /\ pc[q] = pc'[q]
              BY <4>4, Zenon
            <6> SUFFICES /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                         /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                         /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                   /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                      (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
              OBVIOUS
            <6>1A. pc'[q] = "U4" /\ arg'[q].key \in KeyDomain
              BY <4>3, Zenon, RemDef DEF ArgsOf, LineIDtoOp
            <6>1. pc[q] = "U4" /\ arg[q].key \in KeyDomain
              BY <6>1A, Zenon
            <6>2. /\ KeyInBktAtAddr(arg[q].key, newbkt[q])
                  /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q]) = arg[q].val
                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                            /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                               (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
              BY <6>1, Zenon DEF NewBktOK
            <6> QED
              BY <5>0, <6>1, <6>2, ZenonT(90)
          <5>3. CASE pc'[q] = "R4"
            <6> USE <5>3
            <6> arg[q] = arg'[q] /\ pc[q] = pc'[q]
              BY <4>4, Zenon
            <6> SUFFICES /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])'
                         /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                   /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                      (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
              OBVIOUS
            <6>1A. pc'[q] = "R4" /\ arg'[q].key \in KeyDomain
              BY <4>3, Zenon, RemDef DEF ArgsOf, LineIDtoOp
            <6>1. pc[q] = "R4" /\ arg[q].key \in KeyDomain
              BY <6>1A, Zenon
            <6>2. /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])
                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                            /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                               (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
              BY <6>1, Zenon DEF NewBktOK
            <6> QED
              BY <5>0, <6>1, <6>2, ZenonT(90)
          <5> QED
            BY <5>1, <5>2, <5>3
        <4> QED
          BY <4>1, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8
      <3>14. CASE op = "Remove"
        <4> USE <3>14
        <4>1. pc' \in [ProcSet -> LineIDs]
          BY Zenon DEF LineIDs, OpToInvocLine
        <4>2. arg' \in [ProcSet -> ArgDomain]
          BY DEF ArgsOf, ArgDomain
        <4>3. \A q \in ProcSet : (pc'[q] # RemainderID) => arg'[q] \in ArgsOf(LineIDtoOp(pc'[q]))
          <5> SUFFICES ASSUME NEW q \in ProcSet,
                              pc'[q] # RemainderID
                       PROVE  arg'[q] \in ArgsOf(LineIDtoOp(pc'[q]))
            OBVIOUS
          <5>1. CASE q = p
            <6> SUFFICES new_arg \in ArgsOf(LineIDtoOp(OpToInvocLine(op)))
              BY <5>1
            <6>1. LineIDtoOp(OpToInvocLine(op)) = "Remove"
              BY DEF LineIDtoOp, OpToInvocLine
            <6> QED
              BY <6>1
          <5>2. CASE q # p
            BY <5>2
          <5> QED
            BY <5>1, <5>2
        <4>4. pc'[p] = "R1"
          BY Zenon DEF OpToInvocLine
        <4>5. AddrsOK'
          <5> SUFFICES ASSUME NEW p_1 \in ProcSet',
                              (pc[p_1] \in {"I4", "U4", "R4"})'
                       PROVE  (/\ \A q \in ProcSet : (p_1 # q => /\ newbkt[p_1] # bucket[q]
                                                                 /\ newbkt[p_1] # newbkt[q])
                               /\ \A idx \in 1..N  : (A[idx] # newbkt[p_1])
                               /\ newbkt[p_1] # bucket[p_1]
                               /\ newbkt[p_1] \in AllocAddrs)'
            BY DEF AddrsOK
          <5>1. (\A q \in ProcSet : (p_1 # q => /\ newbkt[p_1] # bucket[q]
                                                /\ newbkt[p_1] # newbkt[q]))'
            BY <4>4 DEF AddrsOK
          <5>2. (\A idx \in 1..N  : (A[idx] # newbkt[p_1]))'
            BY <4>4 DEF AddrsOK
          <5>3. (newbkt[p_1] # bucket[p_1])'
            BY <4>4 DEF AddrsOK
          <5>4. (newbkt[p_1] \in AllocAddrs)'
            BY <4>4 DEF AddrsOK
          <5>5. QED
            BY <5>1, <5>2, <5>3, <5>4
        <4>6. BktOK'
          <5> SUFFICES ASSUME NEW q \in ProcSet
                       PROVE  (/\ pc'[q] \in {"I3", "I4"} => (/\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                                                              /\ r'[q] = NULL)
                               /\ pc'[q] \in {"U3", "U4"} => (IF KeyInBktAtAddr(arg[q].key, bucket[q])'
                                                                  THEN (/\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                                                                        /\ r'[q] # NULL)
                                                                  ELSE r'[q] = NULL)
                               /\ pc'[q] \in {"R3", "R4"} => (/\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                                                              /\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                                                              /\ r'[q] # NULL))
            BY DEF BktOK
          <5> USE RemDef, <4>4
          <5>1. CASE pc'[q] \in {"I3", "I4"}
            <6> USE <5>1
            <6> SUFFICES ~KeyInBktAtAddr(arg[q].key, bucket[q])' /\ r'[q] = NULL
              OBVIOUS
            <6>1. ~KeyInBktAtAddr(arg[q].key, bucket[q]) /\ r[q] = NULL
              BY Zenon DEF BktOK
            <6> QED
              BY <6>1, Zenon DEF KeyInBktAtAddr
          <5>2. CASE pc'[q] \in {"U3", "U4"}
            <6> USE <5>2
            <6> SUFFICES IF KeyInBktAtAddr(arg[q].key, bucket[q])'
                            THEN (/\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                                  /\ r'[q] # NULL)
                            ELSE r'[q] = NULL
              OBVIOUS
            <6>1. IF KeyInBktAtAddr(arg[q].key, bucket[q])
                     THEN (/\ r[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                           /\ r[q] # NULL)
                     ELSE r[q] = NULL
              BY Zenon DEF BktOK
            <6>2. KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
              BY Zenon DEF KeyInBktAtAddr
            <6>3. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs'[bucket'[q]][CHOOSE index \in 1..Len(MemLocs'[bucket'[q]]) :
                                   MemLocs'[bucket'[q]][index].key = arg'[q].key].val
              BY DEF ValOfKeyInBktAtAddr
            <6>4. MemLocs = MemLocs' /\ arg[q] = arg'[q] /\ bucket[q] = bucket'[q]
              BY Zenon
            <6>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs[bucket'[q]][CHOOSE index \in 1..Len(MemLocs[bucket'[q]]) :
                                  MemLocs[bucket'[q]][index].key = arg[q].key].val
              BY Zenon, <6>3, <6>4
            <6>6. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs[bucket[q]][CHOOSE index \in 1..Len(MemLocs[bucket[q]]) :
                                 MemLocs[bucket[q]][index].key = arg[q].key].val
              BY <6>4, <6>5
            <6>7. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
              BY <6>6, Zenon DEF ValOfKeyInBktAtAddr
            <6> QED
              BY <6>1, <6>2, <6>7, Zenon
          <5>3. CASE pc'[q] \in {"R3", "R4"}
            <6> USE <5>3
            <6> SUFFICES /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                         /\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                         /\ r'[q] # NULL
              OBVIOUS
            <6>1. /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                  /\ r[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                  /\ r[q] # NULL
              BY Zenon DEF BktOK
            <6>2. KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
              BY Zenon DEF KeyInBktAtAddr
            <6>3. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs'[bucket'[q]][CHOOSE index \in 1..Len(MemLocs'[bucket'[q]]) :
                                   MemLocs'[bucket'[q]][index].key = arg'[q].key].val
              BY DEF ValOfKeyInBktAtAddr
            <6>4. MemLocs = MemLocs' /\ arg[q] = arg'[q] /\ bucket[q] = bucket'[q]
              BY Zenon
            <6>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs[bucket'[q]][CHOOSE index \in 1..Len(MemLocs[bucket'[q]]) :
                                  MemLocs[bucket'[q]][index].key = arg[q].key].val
              BY Zenon, <6>3, <6>4
            <6>6. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs[bucket[q]][CHOOSE index \in 1..Len(MemLocs[bucket[q]]) :
                                 MemLocs[bucket[q]][index].key = arg[q].key].val
              BY <6>4, <6>5
            <6>7. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
              BY <6>6, Zenon DEF ValOfKeyInBktAtAddr
            <6> QED
              BY <6>1, <6>2, <6>7, Zenon
          <5> QED
            BY <5>1, <5>2, <5>3
        <4>7. Uniq'
          <5> SUFFICES ASSUME NEW addr \in AllocAddrs', 
                              NEW bucket_arr, bucket_arr = MemLocs'[addr],
                              NEW j1 \in 1..Len(bucket_arr),
                              NEW j2 \in 1..Len(bucket_arr),
                              bucket_arr[j1].key = bucket_arr[j2].key
                       PROVE  j1 = j2
            BY Zenon DEF Uniq
          <5> QED
            BY Zenon DEF Uniq
        <4>8. NewBktOK'
          <5> SUFFICES ASSUME NEW q \in ProcSet
                       PROVE  /\ pc'[q] = "I4" => /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                                  /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg'[q].val
                                                  /\ \A k \in KeyDomain : k # arg'[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                             /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                                (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
                              /\ pc'[q] = "U4" => /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                                  /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg'[q].val
                                                  /\ \A k \in KeyDomain : k # arg'[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                             /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                                (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
                              /\ pc'[q] = "R4" => /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                                  /\ \A k \in KeyDomain : k # arg'[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                             /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                                (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
            BY DEF NewBktOK
          <5>0. ASSUME NEW k \in KeyDomain
                PROVE  /\ pc[q] \in {"I4", "U4", "R4"} => KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, bucket[q])'
                       /\ KeyInBktAtAddr(k, newbkt[q]) = KeyInBktAtAddr(k, newbkt[q])'
                       /\ pc[q] \in {"I4", "U4", "R4"} => ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])'
                       /\ ValOfKeyInBktAtAddr(k, newbkt[q]) = ValOfKeyInBktAtAddr(k, newbkt[q])'
            <6> USE <5>0
            <6>1. pc[q] \in {"I4", "U4", "R4"} => KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, bucket[q])'
              BY Zenon DEF KeyInBktAtAddr
            <6>2. KeyInBktAtAddr(k, newbkt[q]) = KeyInBktAtAddr(k, newbkt[q])'
              BY Zenon DEF KeyInBktAtAddr
            <6>3. pc[q] \in {"I4", "U4", "R4"} => ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])'
              <7> SUFFICES ASSUME pc[q] \in {"I4", "U4", "R4"}
                           PROVE  ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])'
                OBVIOUS
              <7> DEFINE bkt_arr == MemLocs'[bucket'[q]]
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
              <7>1. ValOfKeyInBktAtAddr(k, bucket[q])' = bkt_arr[idx].val
                BY Zenon DEF ValOfKeyInBktAtAddr
              <7>2. bkt_arr = MemLocs[bucket[q]] /\ bucket'[q] = bucket[q]
                BY Zenon
              <7>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
                BY Zenon
              <7>4. ValOfKeyInBktAtAddr(k, bucket[q]) = 
                    MemLocs[bucket[q]][CHOOSE index \in 1..Len(MemLocs[bucket[q]]) : MemLocs[bucket[q]][index].key = k].val
                BY Zenon DEF ValOfKeyInBktAtAddr
              <7>5. ValOfKeyInBktAtAddr(k, bucket[q]) = bkt_arr[idx].val
                BY <7>2, <7>3, <7>4, Zenon
              <7> QED
                BY <7>1, <7>5
            <6>4. ValOfKeyInBktAtAddr(k, newbkt[q]) = ValOfKeyInBktAtAddr(k, newbkt[q])'
              <7> DEFINE bkt_arr == MemLocs'[newbkt'[q]]
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
              <7>1. ValOfKeyInBktAtAddr(k, newbkt[q])' = bkt_arr[idx].val
                BY Zenon DEF ValOfKeyInBktAtAddr
              <7>2. bkt_arr = MemLocs[newbkt[q]]
                BY Zenon
              <7>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
                BY Zenon
              <7>4. ValOfKeyInBktAtAddr(k, newbkt[q]) = 
                    MemLocs[newbkt[q]][CHOOSE index \in 1..Len(MemLocs[newbkt[q]]) : MemLocs[newbkt[q]][index].key = k].val
                BY Zenon DEF ValOfKeyInBktAtAddr
              <7>5. ValOfKeyInBktAtAddr(k, newbkt[q]) = bkt_arr[idx].val
                BY <7>2, <7>3, <7>4, Zenon
              <7> QED
                BY <7>1, <7>5
            <6> QED
              BY <6>1, <6>2, <6>3, <6>4
          <5>1. CASE pc'[q] = "I4"
            <6> USE <5>1
            <6> arg[q] = arg'[q] /\ pc[q] = pc'[q]
              BY <4>4, Zenon
            <6> SUFFICES /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                         /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                         /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                   /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                      (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
              OBVIOUS
            <6>1A. pc'[q] = "I4" /\ arg'[q].key \in KeyDomain
              BY <4>3, Zenon, RemDef DEF ArgsOf, LineIDtoOp
            <6>1. pc[q] = "I4" /\ arg[q].key \in KeyDomain
              BY <6>1A, Zenon
            <6>2. /\ KeyInBktAtAddr(arg[q].key, newbkt[q])
                  /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q]) = arg[q].val
                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                            /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                               (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
              BY <6>1, Zenon DEF NewBktOK
            <6> QED
              BY <5>0, <6>1, <6>2, ZenonT(90)
          <5>2. CASE pc'[q] = "U4"
            <6> USE <5>2
            <6> arg[q] = arg'[q] /\ pc[q] = pc'[q]
              BY <4>4, Zenon
            <6> SUFFICES /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                         /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                         /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                   /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                      (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
              OBVIOUS
            <6>1A. pc'[q] = "U4" /\ arg'[q].key \in KeyDomain
              BY <4>3, Zenon, RemDef DEF ArgsOf, LineIDtoOp
            <6>1. pc[q] = "U4" /\ arg[q].key \in KeyDomain
              BY <6>1A, Zenon
            <6>2. /\ KeyInBktAtAddr(arg[q].key, newbkt[q])
                  /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q]) = arg[q].val
                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                            /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                               (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
              BY <6>1, Zenon DEF NewBktOK
            <6> QED
              BY <5>0, <6>1, <6>2, ZenonT(90)
          <5>3. CASE pc'[q] = "R4"
            <6> USE <5>3
            <6> arg[q] = arg'[q] /\ pc[q] = pc'[q]
              BY <4>4, Zenon
            <6> SUFFICES /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])'
                         /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                   /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                      (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
              OBVIOUS
            <6>1A. pc'[q] = "R4" /\ arg'[q].key \in KeyDomain
              BY <4>3, Zenon, RemDef DEF ArgsOf, LineIDtoOp
            <6>1. pc[q] = "R4" /\ arg[q].key \in KeyDomain
              BY <6>1A, Zenon
            <6>2. /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])
                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                            /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                               (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
              BY <6>1, Zenon DEF NewBktOK
            <6> QED
              BY <5>0, <6>1, <6>2, ZenonT(90)
          <5> QED
            BY <5>1, <5>2, <5>3
        <4> QED
          BY <4>1, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8
      <3> QED
        BY <3>11, <3>12, <3>13, <3>14 DEF OpNames
    <2>2. ASSUME NEW p \in ProcSet, 
                 IntLine(p)
          PROVE  Inv'
      <3> SUFFICES ASSUME NEW Line \in IntLines(p), Line
                   PROVE  Inv'
        BY <2>2, Zenon DEF IntLine
      <3>1. CASE Line = F1(p)
        <4> USE <3>1 DEF F1
        <4>1. PTypeOK'
          BY NextPTypeOK
        <4>2. (pc \in [ProcSet -> LineIDs])'
          BY Isa DEF LineIDs
        <4>3. (A \in [1..N -> AllocAddrs \union {NULL}])'
          OBVIOUS
        <4>4. (MemLocs \in [Addrs -> Seq([key: KeyDomain, val: ValDomain])])'
          OBVIOUS
        <4>5. (AllocAddrs \in SUBSET Addrs)'
          OBVIOUS
        <4>6. (bucket \in [ProcSet -> AllocAddrs \union {NULL}])'
          <5>1. arg[p].key \in KeyDomain
            BY RemDef, Zenon DEF LineIDtoOp, ArgsOf
          <5> QED
            BY <5>1, HashDef, Zenon
        <4>7. (newbkt \in [ProcSet -> AllocAddrs \union {NULL}])'
          OBVIOUS
        <4>8. (r \in [ProcSet -> ValDomain \union {NULL}])'
          OBVIOUS
        <4>9. (arg \in [ProcSet -> ArgDomain])'
          OBVIOUS
        <4>10. (ret \in [ProcSet -> RetDomain])'
          OBVIOUS
        <4>11. (\A p_1 \in ProcSet : (pc[p_1] # RemainderID) => arg[p_1] \in ArgsOf(LineIDtoOp(pc[p_1])))'
          <5> SUFFICES arg[p] \in ArgsOf(LineIDtoOp(pc'[p]))
            BY Zenon
          <5> QED
            BY RemDef, ZenonT(30) DEF LineIDtoOp, ArgsOf
        <4>12. AddrsOK'
          <5> SUFFICES ASSUME NEW p_1 \in ProcSet',
                              (pc[p_1] \in {"I4", "U4", "R4"})'
                       PROVE  (/\ \A q \in ProcSet : (p_1 # q => /\ newbkt[p_1] # bucket[q]
                                                                 /\ newbkt[p_1] # newbkt[q])
                               /\ \A idx \in 1..N  : (A[idx] # newbkt[p_1])
                               /\ newbkt[p_1] # bucket[p_1]
                               /\ newbkt[p_1] \in AllocAddrs)'
            BY DEF AddrsOK
          <5>1. (\A q \in ProcSet : (p_1 # q => /\ newbkt[p_1] # bucket[q]
                                                /\ newbkt[p_1] # newbkt[q]))'
            <6> SUFFICES ASSUME NEW q \in ProcSet,
                                p_1 # q
                         PROVE  newbkt[p_1] # bucket'[q]
              BY ZenonT(30) DEF AddrsOK
            <6>1. CASE p = q
              <7>1. arg[p] \in [key: KeyDomain]
                BY RemDef, Zenon DEF ArgsOf, LineIDtoOp
              <7>2. Hash[arg[p].key] \in 1..N
                BY <7>1, HashDef
              <7>3. A[Hash[arg[p].key]] # newbkt[p_1]
                BY <7>2, Zenon DEF AddrsOK
              <7>4. bucket'[q] # newbkt[p_1]
                BY <6>1, <7>3, Zenon
              <7> QED
                BY <7>4
            <6>2. CASE p # q
              BY <6>2, Zenon DEF AddrsOK
            <6> QED
              BY <6>1, <6>2
          <5>2. (\A idx \in 1..N  : (A[idx] # newbkt[p_1]))'
            BY DEF AddrsOK
          <5>3. (newbkt[p_1] # bucket[p_1])'
            BY DEF AddrsOK
          <5>4. (newbkt[p_1] \in AllocAddrs)'
            BY DEF AddrsOK
          <5>5. QED
            BY <5>1, <5>2, <5>3, <5>4
        <4>13. BktOK'
          <5> SUFFICES ASSUME NEW q \in ProcSet
                       PROVE  (/\ pc'[q] \in {"I3", "I4"} => (/\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                                                              /\ r'[q] = NULL)
                               /\ pc'[q] \in {"U3", "U4"} => (IF KeyInBktAtAddr(arg[q].key, bucket[q])'
                                                                  THEN (/\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                                                                        /\ r'[q] # NULL)
                                                                  ELSE r'[q] = NULL)
                               /\ pc'[q] \in {"R3", "R4"} => (/\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                                                              /\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                                                              /\ r'[q] # NULL))
            BY DEF BktOK
          <5>1. CASE pc'[q] \in {"I3", "I4"}
            <6> USE <5>1
            <6> SUFFICES ~KeyInBktAtAddr(arg[q].key, bucket[q])' /\ r'[q] = NULL
              OBVIOUS
            <6>1. ~KeyInBktAtAddr(arg[q].key, bucket[q]) /\ r[q] = NULL
              BY Zenon DEF BktOK
            <6> QED
              BY <6>1, Zenon DEF KeyInBktAtAddr
          <5>2. CASE pc'[q] \in {"U3", "U4"}
            <6> USE <5>2
            <6> SUFFICES IF KeyInBktAtAddr(arg[q].key, bucket[q])'
                            THEN (/\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                                  /\ r'[q] # NULL)
                            ELSE r'[q] = NULL
              OBVIOUS
            <6>1. IF KeyInBktAtAddr(arg[q].key, bucket[q])
                     THEN (/\ r[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                           /\ r[q] # NULL)
                     ELSE r[q] = NULL
              BY Zenon DEF BktOK
            <6>2. KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
              BY Zenon DEF KeyInBktAtAddr
            <6>3. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs'[bucket'[q]][CHOOSE index \in 1..Len(MemLocs'[bucket'[q]]) :
                                   MemLocs'[bucket'[q]][index].key = arg'[q].key].val
              BY DEF ValOfKeyInBktAtAddr
            <6>4. MemLocs = MemLocs' /\ arg = arg' /\ bucket[q] = bucket'[q]
              BY Zenon
            <6>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs[bucket'[q]][CHOOSE index \in 1..Len(MemLocs[bucket'[q]]) :
                                  MemLocs[bucket'[q]][index].key = arg[q].key].val
              BY Zenon, <6>3, <6>4
            <6>6. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs[bucket[q]][CHOOSE index \in 1..Len(MemLocs[bucket[q]]) :
                                 MemLocs[bucket[q]][index].key = arg[q].key].val
              BY <6>4, <6>5
            <6>7. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
              BY <6>6, Zenon DEF ValOfKeyInBktAtAddr
            <6> QED
              BY <6>1, <6>2, <6>7, Zenon
          <5>3. CASE pc'[q] \in {"R3", "R4"}
            <6> USE <5>3
            <6> SUFFICES /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                         /\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                         /\ r'[q] # NULL
              OBVIOUS
            <6>1. /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                  /\ r[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                  /\ r[q] # NULL
              BY Zenon DEF BktOK
            <6>2. KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
              BY Zenon DEF KeyInBktAtAddr
            <6>3. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs'[bucket'[q]][CHOOSE index \in 1..Len(MemLocs'[bucket'[q]]) :
                                   MemLocs'[bucket'[q]][index].key = arg'[q].key].val
              BY DEF ValOfKeyInBktAtAddr
            <6>4. MemLocs = MemLocs' /\ arg = arg' /\ bucket[q] = bucket'[q]
              BY Zenon
            <6>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs[bucket'[q]][CHOOSE index \in 1..Len(MemLocs[bucket'[q]]) :
                                  MemLocs[bucket'[q]][index].key = arg[q].key].val
              BY Zenon, <6>3, <6>4
            <6>6. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs[bucket[q]][CHOOSE index \in 1..Len(MemLocs[bucket[q]]) :
                                 MemLocs[bucket[q]][index].key = arg[q].key].val
              BY <6>4, <6>5
            <6>7. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
              BY <6>6, Zenon DEF ValOfKeyInBktAtAddr
            <6> QED
              BY <6>1, <6>2, <6>7, Zenon
          <5> QED
            BY <5>1, <5>2, <5>3
        <4>14. Uniq'
          <5> SUFFICES ASSUME NEW addr \in AllocAddrs', 
                              NEW bucket_arr, bucket_arr = MemLocs'[addr],
                              NEW j1 \in 1..Len(bucket_arr),
                              NEW j2 \in 1..Len(bucket_arr),
                              bucket_arr[j1].key = bucket_arr[j2].key
                       PROVE  j1 = j2
            BY Zenon DEF Uniq
          <5> QED
            BY Zenon DEF Uniq
        <4>15. NewBktOK'
          <5> SUFFICES ASSUME NEW q \in ProcSet
                       PROVE  /\ pc'[q] = "I4" => /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                                  /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                                                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                            /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                               (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
                              /\ pc'[q] = "U4" => /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                                  /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                                                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                            /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                               (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
                              /\ pc'[q] = "R4" => /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                            /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                               (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
            BY ZenonT(60) DEF NewBktOK
          <5>0. ASSUME NEW k \in KeyDomain
                PROVE  /\ pc[q] \in {"I4", "U4", "R4"} => KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, bucket[q])'
                       /\ KeyInBktAtAddr(k, newbkt[q]) = KeyInBktAtAddr(k, newbkt[q])'
                       /\ pc[q] \in {"I4", "U4", "R4"} => ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])'
                       /\ ValOfKeyInBktAtAddr(k, newbkt[q]) = ValOfKeyInBktAtAddr(k, newbkt[q])'
            <6> USE <5>0
            <6>1. pc[q] \in {"I4", "U4", "R4"} => KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, bucket[q])'
              BY Zenon DEF KeyInBktAtAddr
            <6>2. KeyInBktAtAddr(k, newbkt[q]) = KeyInBktAtAddr(k, newbkt[q])'
              BY Zenon DEF KeyInBktAtAddr
            <6>3. pc[q] \in {"I4", "U4", "R4"} => ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])'
              <7> SUFFICES ASSUME pc[q] \in {"I4", "U4", "R4"}
                           PROVE  ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])'
                OBVIOUS
              <7> DEFINE bkt_arr == MemLocs'[bucket'[q]]
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
              <7>1. ValOfKeyInBktAtAddr(k, bucket[q])' = bkt_arr[idx].val
                BY Zenon DEF ValOfKeyInBktAtAddr
              <7>2. bkt_arr = MemLocs[bucket[q]]
                BY Zenon
              <7>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
                BY Zenon
              <7> QED
                BY <7>1, <7>2, <7>3, Isa DEF ValOfKeyInBktAtAddr
            <6>4. ValOfKeyInBktAtAddr(k, newbkt[q]) = ValOfKeyInBktAtAddr(k, newbkt[q])'
              <7> DEFINE bkt_arr == MemLocs'[newbkt'[q]]
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
              <7>1. ValOfKeyInBktAtAddr(k, newbkt[q])' = bkt_arr[idx].val
                BY Zenon DEF ValOfKeyInBktAtAddr
              <7>2. bkt_arr = MemLocs[newbkt[q]]
                BY Zenon
              <7>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
                BY Zenon
              <7> QED
                BY <7>1, <7>2, <7>3, Isa DEF ValOfKeyInBktAtAddr
            <6> QED
              BY <6>1, <6>2, <6>3, <6>4
          <5>1. CASE pc'[q] = "I4"
            <6> USE <5>1
            <6> SUFFICES /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                         /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                         /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                   /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                      (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
              OBVIOUS
            <6>1. pc[q] = "I4" /\ arg[q].key \in KeyDomain
              BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
            <6>2. /\ KeyInBktAtAddr(arg[q].key, newbkt[q])
                  /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q]) = arg[q].val
                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                            /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                               (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
              BY <6>1, Zenon DEF NewBktOK
            <6> QED
              BY <5>0, <6>1, <6>2, ZenonT(30)
          <5>2. CASE pc'[q] = "U4"
            <6> USE <5>2
            <6> SUFFICES /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                         /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                         /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                   /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                      (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
              OBVIOUS
            <6>1. pc[q] = "U4" /\ arg[q].key \in KeyDomain
              BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
            <6>2. /\ KeyInBktAtAddr(arg[q].key, newbkt[q])
                  /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q]) = arg[q].val
                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                            /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                               (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
              BY <6>1, Zenon DEF NewBktOK
            <6> QED
              BY <5>0, <6>1, <6>2, ZenonT(30)
          <5>3. CASE pc'[q] = "R4"
            <6> USE <5>3
            <6> SUFFICES /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])'
                         /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                   /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                      (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
              OBVIOUS
            <6>1. pc[q] = "R4" /\ arg[q].key \in KeyDomain
              BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
            <6>2. /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])
                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                            /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                               (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
              BY <6>1, Zenon DEF NewBktOK
            <6> QED
              BY <5>0, <6>1, <6>2, ZenonT(30)
          <5> QED
            BY <5>1, <5>2, <5>3
        <4> QED
          BY <4>1, <4>10, <4>11, <4>12, <4>13, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, <4>14, <4>15 DEF Inv
      <3>2. CASE Line = F2(p)
        <4> USE <3>2 DEF F2
        <4>1. PTypeOK'
          BY NextPTypeOK
        <4>2. (pc \in [ProcSet -> LineIDs])'
          BY Isa DEF LineIDs
        <4>3. (A \in [1..N -> AllocAddrs \union {NULL}])'
          OBVIOUS
        <4>4. (MemLocs \in [Addrs -> Seq([key: KeyDomain, val: ValDomain])])'
          OBVIOUS
        <4>5. (AllocAddrs \in SUBSET Addrs)'
          OBVIOUS
        <4>6. (bucket \in [ProcSet -> AllocAddrs \union {NULL}])'
          OBVIOUS
        <4>7. (newbkt \in [ProcSet -> AllocAddrs \union {NULL}])'
          OBVIOUS
        <4>8. (r \in [ProcSet -> ValDomain \union {NULL}])'
          <5>1. CASE bucket[p] # NULL /\ KeyInBktAtAddr(arg[p].key, bucket[p])
            <6>1. r' = [r EXCEPT ![p] = ValOfKeyInBktAtAddr(arg[p].key, bucket[p])]
              BY <5>1, Zenon
            <6>2. ValOfKeyInBktAtAddr(arg[p].key, bucket[p]) = MemLocs[bucket[p]][CHOOSE index \in 1..Len(MemLocs[bucket[p]]) : MemLocs[bucket[p]][index].key = arg[p].key].val
              BY Zenon DEF ValOfKeyInBktAtAddr
            <6>3. \E index \in 1..Len(MemLocs[bucket[p]]) : MemLocs[bucket[p]][index].key = arg[p].key
              BY <5>1, Zenon DEF KeyInBktAtAddr
            <6>4. PICK index \in 1..Len(MemLocs[bucket[p]]) : /\ MemLocs[bucket[p]][index].key = arg[p].key
                                                              /\ ValOfKeyInBktAtAddr(arg[p].key, bucket[p]) = MemLocs[bucket[p]][index].val
              BY <6>2, <6>3, Zenon
            <6>5. MemLocs[bucket[p]] \in Seq([key: KeyDomain, val: ValDomain])
              BY <5>1
            <6>6. MemLocs[bucket[p]][index] \in [key: KeyDomain, val: ValDomain]
              BY <6>4, <6>5, ElementOfSeq, Zenon
            <6>7. MemLocs[bucket[p]][index].val \in ValDomain
              BY <6>6
            <6> QED
              BY <6>1, <6>4, <6>7, Zenon
          <5>2. CASE bucket[p] = NULL \/ ~KeyInBktAtAddr(arg[p].key, bucket[p])
            BY <5>2, Zenon DEF KeyInBktAtAddr
          <5> QED
            BY <5>1, <5>2
        <4>9. (arg \in [ProcSet -> ArgDomain])'
          OBVIOUS
        <4>10. (ret \in [ProcSet -> RetDomain])'
          OBVIOUS
        <4>11. (\A p_1 \in ProcSet : (pc[p_1] # RemainderID) => arg[p_1] \in ArgsOf(LineIDtoOp(pc[p_1])))'
          <5> SUFFICES arg[p] \in ArgsOf(LineIDtoOp(pc'[p]))
            BY Zenon
          <5> QED
            BY RemDef, ZenonT(30) DEF LineIDtoOp, ArgsOf
        <4>12. AddrsOK'
          <5> SUFFICES ASSUME NEW p_1 \in ProcSet',
                              (pc[p_1] \in {"I4", "U4", "R4"})'
                       PROVE  (/\ \A q \in ProcSet : (p_1 # q => /\ newbkt[p_1] # bucket[q]
                                                                 /\ newbkt[p_1] # newbkt[q])
                               /\ \A idx \in 1..N  : (A[idx] # newbkt[p_1])
                               /\ newbkt[p_1] # bucket[p_1]
                               /\ newbkt[p_1] \in AllocAddrs)'
            BY DEF AddrsOK
          <5>1. (\A q \in ProcSet : (p_1 # q => /\ newbkt[p_1] # bucket[q]
                                                /\ newbkt[p_1] # newbkt[q]))'
            BY DEF AddrsOK
          <5>2. (\A idx \in 1..N  : (A[idx] # newbkt[p_1]))'
            BY DEF AddrsOK
          <5>3. (newbkt[p_1] # bucket[p_1])'
            BY DEF AddrsOK
          <5>4. (newbkt[p_1] \in AllocAddrs)'
            BY DEF AddrsOK
          <5>5. QED
            BY <5>1, <5>2, <5>3, <5>4
        <4>13. BktOK'
          <5> SUFFICES ASSUME NEW q \in ProcSet
                       PROVE  (/\ pc'[q] \in {"I3", "I4"} => (/\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                                                              /\ r'[q] = NULL)
                               /\ pc'[q] \in {"U3", "U4"} => (IF KeyInBktAtAddr(arg[q].key, bucket[q])'
                                                                  THEN (/\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                                                                        /\ r'[q] # NULL)
                                                                  ELSE r'[q] = NULL)
                               /\ pc'[q] \in {"R3", "R4"} => (/\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                                                              /\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                                                              /\ r'[q] # NULL))
            BY DEF BktOK
          <5>1. CASE pc'[q] \in {"I3", "I4"}
            <6> USE <5>1
            <6> SUFFICES ~KeyInBktAtAddr(arg[q].key, bucket[q])' /\ r'[q] = NULL
              OBVIOUS
            <6>1. ~KeyInBktAtAddr(arg[q].key, bucket[q]) /\ r[q] = NULL
              BY Zenon DEF BktOK
            <6> QED
              BY <6>1, Zenon DEF KeyInBktAtAddr
          <5>2. CASE pc'[q] \in {"U3", "U4"}
            <6> USE <5>2
            <6> SUFFICES IF KeyInBktAtAddr(arg[q].key, bucket[q])'
                            THEN (/\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                                  /\ r'[q] # NULL)
                            ELSE r'[q] = NULL
              OBVIOUS
            <6>1. IF KeyInBktAtAddr(arg[q].key, bucket[q])
                     THEN (/\ r[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                           /\ r[q] # NULL)
                     ELSE r[q] = NULL
              BY Zenon DEF BktOK
            <6>2. KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
              BY Zenon DEF KeyInBktAtAddr
            <6>3. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs'[bucket'[q]][CHOOSE index \in 1..Len(MemLocs'[bucket'[q]]) :
                                   MemLocs'[bucket'[q]][index].key = arg'[q].key].val
              BY DEF ValOfKeyInBktAtAddr
            <6>4. MemLocs = MemLocs' /\ arg = arg' /\ bucket[q] = bucket'[q]
              BY Zenon
            <6>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs[bucket'[q]][CHOOSE index \in 1..Len(MemLocs[bucket'[q]]) :
                                  MemLocs[bucket'[q]][index].key = arg[q].key].val
              BY Zenon, <6>3, <6>4
            <6>6. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs[bucket[q]][CHOOSE index \in 1..Len(MemLocs[bucket[q]]) :
                                 MemLocs[bucket[q]][index].key = arg[q].key].val
              BY <6>4, <6>5
            <6>7. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
              BY <6>6, Zenon DEF ValOfKeyInBktAtAddr
            <6> QED
              BY <6>1, <6>2, <6>7, Zenon
          <5>3. CASE pc'[q] \in {"R3", "R4"}
            <6> USE <5>3
            <6> SUFFICES /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                         /\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                         /\ r'[q] # NULL
              OBVIOUS
            <6>1. /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                  /\ r[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                  /\ r[q] # NULL
              BY Zenon DEF BktOK
            <6>2. KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
              BY Zenon DEF KeyInBktAtAddr
            <6>3. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs'[bucket'[q]][CHOOSE index \in 1..Len(MemLocs'[bucket'[q]]) :
                                   MemLocs'[bucket'[q]][index].key = arg'[q].key].val
              BY DEF ValOfKeyInBktAtAddr
            <6>4. MemLocs = MemLocs' /\ arg = arg' /\ bucket[q] = bucket'[q]
              BY Zenon
            <6>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs[bucket'[q]][CHOOSE index \in 1..Len(MemLocs[bucket'[q]]) :
                                  MemLocs[bucket'[q]][index].key = arg[q].key].val
              BY Zenon, <6>3, <6>4
            <6>6. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs[bucket[q]][CHOOSE index \in 1..Len(MemLocs[bucket[q]]) :
                                 MemLocs[bucket[q]][index].key = arg[q].key].val
              BY <6>4, <6>5
            <6>7. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
              BY <6>6, Zenon DEF ValOfKeyInBktAtAddr
            <6> QED
              BY <6>1, <6>2, <6>7, Zenon
          <5> QED
            BY <5>1, <5>2, <5>3
        <4>14. Uniq'
          <5> SUFFICES ASSUME NEW addr \in AllocAddrs', 
                              NEW bucket_arr, bucket_arr = MemLocs'[addr],
                              NEW j1 \in 1..Len(bucket_arr),
                              NEW j2 \in 1..Len(bucket_arr),
                              bucket_arr[j1].key = bucket_arr[j2].key
                       PROVE  j1 = j2
            BY Zenon DEF Uniq
          <5> QED
            BY Zenon DEF Uniq
        <4>15. NewBktOK'
          <5> SUFFICES ASSUME NEW q \in ProcSet
                       PROVE  /\ pc'[q] = "I4" => /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                                  /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                                                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                            /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                               (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
                              /\ pc'[q] = "U4" => /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                                  /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                                                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                            /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                               (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
                              /\ pc'[q] = "R4" => /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                            /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                               (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
            BY ZenonT(60) DEF NewBktOK
          <5>0. ASSUME NEW k \in KeyDomain
                PROVE  /\ pc[q] \in {"I4", "U4", "R4"} => KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, bucket[q])'
                       /\ KeyInBktAtAddr(k, newbkt[q]) = KeyInBktAtAddr(k, newbkt[q])'
                       /\ pc[q] \in {"I4", "U4", "R4"} => ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])'
                       /\ ValOfKeyInBktAtAddr(k, newbkt[q]) = ValOfKeyInBktAtAddr(k, newbkt[q])'
            <6> USE <5>0
            <6>1. pc[q] \in {"I4", "U4", "R4"} => KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, bucket[q])'
              BY Zenon DEF KeyInBktAtAddr
            <6>2. KeyInBktAtAddr(k, newbkt[q]) = KeyInBktAtAddr(k, newbkt[q])'
              BY Zenon DEF KeyInBktAtAddr
            <6>3. pc[q] \in {"I4", "U4", "R4"} => ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])'
              <7> SUFFICES ASSUME pc[q] \in {"I4", "U4", "R4"}
                           PROVE  ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])'
                OBVIOUS
              <7> DEFINE bkt_arr == MemLocs'[bucket'[q]]
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
              <7>1. ValOfKeyInBktAtAddr(k, bucket[q])' = bkt_arr[idx].val
                BY Zenon DEF ValOfKeyInBktAtAddr
              <7>2. bkt_arr = MemLocs[bucket[q]]
                BY Zenon
              <7>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
                BY Zenon
              <7> QED
                BY <7>1, <7>2, <7>3, Isa DEF ValOfKeyInBktAtAddr
            <6>4. ValOfKeyInBktAtAddr(k, newbkt[q]) = ValOfKeyInBktAtAddr(k, newbkt[q])'
              <7> DEFINE bkt_arr == MemLocs'[newbkt'[q]]
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
              <7>1. ValOfKeyInBktAtAddr(k, newbkt[q])' = bkt_arr[idx].val
                BY Zenon DEF ValOfKeyInBktAtAddr
              <7>2. bkt_arr = MemLocs[newbkt[q]]
                BY Zenon
              <7>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
                BY Zenon
              <7> QED
                BY <7>1, <7>2, <7>3, Isa DEF ValOfKeyInBktAtAddr
            <6> QED
              BY <6>1, <6>2, <6>3, <6>4
          <5>1. CASE pc'[q] = "I4"
            <6> USE <5>1
            <6> SUFFICES /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                         /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                         /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                   /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                      (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
              OBVIOUS
            <6>1. pc[q] = "I4" /\ arg[q].key \in KeyDomain
              BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
            <6>2. /\ KeyInBktAtAddr(arg[q].key, newbkt[q])
                  /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q]) = arg[q].val
                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                            /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                               (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
              BY <6>1, Zenon DEF NewBktOK
            <6> QED
              BY <5>0, <6>1, <6>2, ZenonT(30)
          <5>2. CASE pc'[q] = "U4"
            <6> USE <5>2
            <6> SUFFICES /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                         /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                         /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                   /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                      (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
              OBVIOUS
            <6>1. pc[q] = "U4" /\ arg[q].key \in KeyDomain
              BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
            <6>2. /\ KeyInBktAtAddr(arg[q].key, newbkt[q])
                  /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q]) = arg[q].val
                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                            /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                               (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
              BY <6>1, Zenon DEF NewBktOK
            <6> QED
              BY <5>0, <6>1, <6>2, ZenonT(30)
          <5>3. CASE pc'[q] = "R4"
            <6> USE <5>3
            <6> SUFFICES /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])'
                         /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                   /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                      (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
              OBVIOUS
            <6>1. pc[q] = "R4" /\ arg[q].key \in KeyDomain
              BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
            <6>2. /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])
                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                            /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                               (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
              BY <6>1, Zenon DEF NewBktOK
            <6> QED
              BY <5>0, <6>1, <6>2, ZenonT(30)
          <5> QED
            BY <5>1, <5>2, <5>3
        <4> QED
          BY <4>1, <4>10, <4>11, <4>12, <4>13, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, <4>14, <4>15 DEF Inv
      <3>3. CASE Line = I1(p)
        <4> USE <3>3 DEF I1
        <4>1. PTypeOK'
          BY NextPTypeOK
        <4>2. (pc \in [ProcSet -> LineIDs])'
          BY Isa DEF LineIDs
        <4>3. (A \in [1..N -> AllocAddrs \union {NULL}])'
          OBVIOUS
        <4>4. (MemLocs \in [Addrs -> Seq([key: KeyDomain, val: ValDomain])])'
          OBVIOUS
        <4>5. (AllocAddrs \in SUBSET Addrs)'
          OBVIOUS
        <4>6. (bucket \in [ProcSet -> AllocAddrs \union {NULL}])'
          <5>1. arg[p].key \in KeyDomain
            BY RemDef, Zenon DEF LineIDtoOp, ArgsOf
          <5> QED
            BY <5>1, HashDef, Zenon
        <4>7. (newbkt \in [ProcSet -> AllocAddrs \union {NULL}])'
          OBVIOUS
        <4>8. (r \in [ProcSet -> ValDomain \union {NULL}])'
          OBVIOUS
        <4>9. (arg \in [ProcSet -> ArgDomain])'
          OBVIOUS
        <4>10. (ret \in [ProcSet -> RetDomain])'
          OBVIOUS
        <4>11. (\A p_1 \in ProcSet : (pc[p_1] # RemainderID) => arg[p_1] \in ArgsOf(LineIDtoOp(pc[p_1])))'
          <5> SUFFICES arg[p] \in ArgsOf(LineIDtoOp(pc'[p]))
            BY Zenon
          <5> QED
            BY RemDef, ZenonT(30) DEF LineIDtoOp, ArgsOf
        <4>12. AddrsOK'
          <5> SUFFICES ASSUME NEW p_1 \in ProcSet',
                              (pc[p_1] \in {"I4", "U4", "R4"})'
                       PROVE  (/\ \A q \in ProcSet : (p_1 # q => /\ newbkt[p_1] # bucket[q]
                                                                 /\ newbkt[p_1] # newbkt[q])
                               /\ \A idx \in 1..N  : (A[idx] # newbkt[p_1])
                               /\ newbkt[p_1] # bucket[p_1]
                               /\ newbkt[p_1] \in AllocAddrs)'
            BY DEF AddrsOK
          <5>1. (\A q \in ProcSet : (p_1 # q => /\ newbkt[p_1] # bucket[q]
                                                /\ newbkt[p_1] # newbkt[q]))'
            <6> SUFFICES ASSUME NEW q \in ProcSet,
                                p_1 # q
                         PROVE  newbkt[p_1] # bucket'[q]
              BY ZenonT(30) DEF AddrsOK
            <6>1. CASE p = q
              <7>1. arg[p] \in [key: KeyDomain, val: ValDomain]
                BY RemDef, Zenon DEF ArgsOf, LineIDtoOp
              <7>2. Hash[arg[p].key] \in 1..N
                BY <7>1, HashDef
              <7>3. A[Hash[arg[p].key]] # newbkt[p_1]
                BY <7>2, Zenon DEF AddrsOK
              <7>4. bucket'[q] # newbkt[p_1]
                BY <6>1, <7>3, Zenon
              <7> QED
                BY <7>4
            <6>2. CASE p # q
              BY <6>2, Zenon DEF AddrsOK
            <6> QED
              BY <6>1, <6>2
          <5>2. (\A idx \in 1..N  : (A[idx] # newbkt[p_1]))'
            BY DEF AddrsOK
          <5>3. (newbkt[p_1] # bucket[p_1])'
            BY DEF AddrsOK
          <5>4. (newbkt[p_1] \in AllocAddrs)'
            BY DEF AddrsOK
          <5>5. QED
            BY <5>1, <5>2, <5>3, <5>4
        <4>13. BktOK'
          <5> SUFFICES ASSUME NEW q \in ProcSet
                       PROVE  (/\ pc'[q] \in {"I3", "I4"} => (/\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                                                              /\ r'[q] = NULL)
                               /\ pc'[q] \in {"U3", "U4"} => (IF KeyInBktAtAddr(arg[q].key, bucket[q])'
                                                                  THEN (/\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                                                                        /\ r'[q] # NULL)
                                                                  ELSE r'[q] = NULL)
                               /\ pc'[q] \in {"R3", "R4"} => (/\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                                                              /\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                                                              /\ r'[q] # NULL))
            BY DEF BktOK
          <5>1. CASE pc'[q] \in {"I3", "I4"}
            <6> USE <5>1
            <6> SUFFICES ~KeyInBktAtAddr(arg[q].key, bucket[q])' /\ r'[q] = NULL
              OBVIOUS
            <6>1. ~KeyInBktAtAddr(arg[q].key, bucket[q]) /\ r[q] = NULL
              BY Zenon DEF BktOK
            <6> QED
              BY <6>1, Zenon DEF KeyInBktAtAddr
          <5>2. CASE pc'[q] \in {"U3", "U4"}
            <6> USE <5>2
            <6> SUFFICES IF KeyInBktAtAddr(arg[q].key, bucket[q])'
                            THEN (/\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                                  /\ r'[q] # NULL)
                            ELSE r'[q] = NULL
              OBVIOUS
            <6>1. IF KeyInBktAtAddr(arg[q].key, bucket[q])
                     THEN (/\ r[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                           /\ r[q] # NULL)
                     ELSE r[q] = NULL
              BY Zenon DEF BktOK
            <6>2. KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
              BY Zenon DEF KeyInBktAtAddr
            <6>3. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs'[bucket'[q]][CHOOSE index \in 1..Len(MemLocs'[bucket'[q]]) :
                                   MemLocs'[bucket'[q]][index].key = arg'[q].key].val
              BY DEF ValOfKeyInBktAtAddr
            <6>4. MemLocs = MemLocs' /\ arg = arg' /\ bucket[q] = bucket'[q]
              BY Zenon
            <6>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs[bucket'[q]][CHOOSE index \in 1..Len(MemLocs[bucket'[q]]) :
                                  MemLocs[bucket'[q]][index].key = arg[q].key].val
              BY Zenon, <6>3, <6>4
            <6>6. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs[bucket[q]][CHOOSE index \in 1..Len(MemLocs[bucket[q]]) :
                                 MemLocs[bucket[q]][index].key = arg[q].key].val
              BY <6>4, <6>5
            <6>7. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
              BY <6>6, Zenon DEF ValOfKeyInBktAtAddr
            <6> QED
              BY <6>1, <6>2, <6>7, Zenon
          <5>3. CASE pc'[q] \in {"R3", "R4"}
            <6> USE <5>3
            <6> SUFFICES /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                         /\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                         /\ r'[q] # NULL
              OBVIOUS
            <6>1. /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                  /\ r[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                  /\ r[q] # NULL
              BY Zenon DEF BktOK
            <6>2. KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
              BY Zenon DEF KeyInBktAtAddr
            <6>3. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs'[bucket'[q]][CHOOSE index \in 1..Len(MemLocs'[bucket'[q]]) :
                                   MemLocs'[bucket'[q]][index].key = arg'[q].key].val
              BY DEF ValOfKeyInBktAtAddr
            <6>4. MemLocs = MemLocs' /\ arg = arg' /\ bucket[q] = bucket'[q]
              BY Zenon
            <6>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs[bucket'[q]][CHOOSE index \in 1..Len(MemLocs[bucket'[q]]) :
                                  MemLocs[bucket'[q]][index].key = arg[q].key].val
              BY Zenon, <6>3, <6>4
            <6>6. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs[bucket[q]][CHOOSE index \in 1..Len(MemLocs[bucket[q]]) :
                                 MemLocs[bucket[q]][index].key = arg[q].key].val
              BY <6>4, <6>5
            <6>7. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
              BY <6>6, Zenon DEF ValOfKeyInBktAtAddr
            <6> QED
              BY <6>1, <6>2, <6>7, Zenon
          <5> QED
            BY <5>1, <5>2, <5>3
        <4>14. Uniq'
          <5> SUFFICES ASSUME NEW addr \in AllocAddrs', 
                              NEW bucket_arr, bucket_arr = MemLocs'[addr],
                              NEW j1 \in 1..Len(bucket_arr),
                              NEW j2 \in 1..Len(bucket_arr),
                              bucket_arr[j1].key = bucket_arr[j2].key
                       PROVE  j1 = j2
            BY Zenon DEF Uniq
          <5> QED
            BY Zenon DEF Uniq
        <4>15. NewBktOK'
          <5> SUFFICES ASSUME NEW q \in ProcSet
                       PROVE  /\ pc'[q] = "I4" => /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                                  /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                                                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                            /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                               (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
                              /\ pc'[q] = "U4" => /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                                  /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                                                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                            /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                               (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
                              /\ pc'[q] = "R4" => /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                            /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                               (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
            BY ZenonT(60) DEF NewBktOK
          <5>0. ASSUME NEW k \in KeyDomain
                PROVE  /\ pc[q] \in {"I4", "U4", "R4"} => KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, bucket[q])'
                       /\ KeyInBktAtAddr(k, newbkt[q]) = KeyInBktAtAddr(k, newbkt[q])'
                       /\ pc[q] \in {"I4", "U4", "R4"} => ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])'
                       /\ ValOfKeyInBktAtAddr(k, newbkt[q]) = ValOfKeyInBktAtAddr(k, newbkt[q])'
            <6> USE <5>0
            <6>1. pc[q] \in {"I4", "U4", "R4"} => KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, bucket[q])'
              BY Zenon DEF KeyInBktAtAddr
            <6>2. KeyInBktAtAddr(k, newbkt[q]) = KeyInBktAtAddr(k, newbkt[q])'
              BY Zenon DEF KeyInBktAtAddr
            <6>3. pc[q] \in {"I4", "U4", "R4"} => ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])'
              <7> SUFFICES ASSUME pc[q] \in {"I4", "U4", "R4"}
                           PROVE  ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])'
                OBVIOUS
              <7> DEFINE bkt_arr == MemLocs'[bucket'[q]]
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
              <7>1. ValOfKeyInBktAtAddr(k, bucket[q])' = bkt_arr[idx].val
                BY Zenon DEF ValOfKeyInBktAtAddr
              <7>2. bkt_arr = MemLocs[bucket[q]]
                BY Zenon
              <7>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
                BY Zenon
              <7> QED
                BY <7>1, <7>2, <7>3, Isa DEF ValOfKeyInBktAtAddr
            <6>4. ValOfKeyInBktAtAddr(k, newbkt[q]) = ValOfKeyInBktAtAddr(k, newbkt[q])'
              <7> DEFINE bkt_arr == MemLocs'[newbkt'[q]]
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
              <7>1. ValOfKeyInBktAtAddr(k, newbkt[q])' = bkt_arr[idx].val
                BY Zenon DEF ValOfKeyInBktAtAddr
              <7>2. bkt_arr = MemLocs[newbkt[q]]
                BY Zenon
              <7>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
                BY Zenon
              <7> QED
                BY <7>1, <7>2, <7>3, Isa DEF ValOfKeyInBktAtAddr
            <6> QED
              BY <6>1, <6>2, <6>3, <6>4
          <5>1. CASE pc'[q] = "I4"
            <6> USE <5>1
            <6> SUFFICES /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                         /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                         /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                   /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                      (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
              OBVIOUS
            <6>1. pc[q] = "I4" /\ arg[q].key \in KeyDomain
              BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
            <6>2. /\ KeyInBktAtAddr(arg[q].key, newbkt[q])
                  /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q]) = arg[q].val
                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                            /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                               (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
              BY <6>1, Zenon DEF NewBktOK
            <6> QED
              BY <5>0, <6>1, <6>2, ZenonT(30)
          <5>2. CASE pc'[q] = "U4"
            <6> USE <5>2
            <6> SUFFICES /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                         /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                         /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                   /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                      (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
              OBVIOUS
            <6>1. pc[q] = "U4" /\ arg[q].key \in KeyDomain
              BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
            <6>2. /\ KeyInBktAtAddr(arg[q].key, newbkt[q])
                  /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q]) = arg[q].val
                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                            /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                               (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
              BY <6>1, Zenon DEF NewBktOK
            <6> QED
              BY <5>0, <6>1, <6>2, ZenonT(30)
          <5>3. CASE pc'[q] = "R4"
            <6> USE <5>3
            <6> SUFFICES /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])'
                         /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                   /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                      (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
              OBVIOUS
            <6>1. pc[q] = "R4" /\ arg[q].key \in KeyDomain
              BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
            <6>2. /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])
                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                            /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                               (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
              BY <6>1, Zenon DEF NewBktOK
            <6> QED
              BY <5>0, <6>1, <6>2, ZenonT(30)
          <5> QED
            BY <5>1, <5>2, <5>3
        <4> QED
          BY <4>1, <4>10, <4>11, <4>12, <4>13, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, <4>14, <4>15 DEF Inv
      <3>4. CASE Line = I2(p)
        <4> USE <3>4 DEF I2
        <4>1. PTypeOK'
          BY NextPTypeOK
        <4>2. (pc \in [ProcSet -> LineIDs])'
          BY Isa DEF LineIDs
        <4>3. (A \in [1..N -> AllocAddrs \union {NULL}])'
          OBVIOUS
        <4>4. (MemLocs \in [Addrs -> Seq([key: KeyDomain, val: ValDomain])])'
          OBVIOUS
        <4>5. (AllocAddrs \in SUBSET Addrs)'
          OBVIOUS
        <4>6. (bucket \in [ProcSet -> AllocAddrs \union {NULL}])'
          OBVIOUS
        <4>7. (newbkt \in [ProcSet -> AllocAddrs \union {NULL}])'
          OBVIOUS
        <4>8. (r \in [ProcSet -> ValDomain \union {NULL}])'
          <5>1. CASE bucket[p] # NULL /\ KeyInBktAtAddr(arg[p].key, bucket[p])
            <6>1. r' = [r EXCEPT ![p] = ValOfKeyInBktAtAddr(arg[p].key, bucket[p])]
              BY <5>1, Zenon
            <6>2. ValOfKeyInBktAtAddr(arg[p].key, bucket[p]) = MemLocs[bucket[p]][CHOOSE index \in 1..Len(MemLocs[bucket[p]]) : MemLocs[bucket[p]][index].key = arg[p].key].val
              BY Zenon DEF ValOfKeyInBktAtAddr
            <6>3. \E index \in 1..Len(MemLocs[bucket[p]]) : MemLocs[bucket[p]][index].key = arg[p].key
              BY <5>1, Zenon DEF KeyInBktAtAddr
            <6>4. PICK index \in 1..Len(MemLocs[bucket[p]]) : /\ MemLocs[bucket[p]][index].key = arg[p].key
                                                              /\ ValOfKeyInBktAtAddr(arg[p].key, bucket[p]) = MemLocs[bucket[p]][index].val
              BY <6>2, <6>3, Zenon
            <6>5. MemLocs[bucket[p]] \in Seq([key: KeyDomain, val: ValDomain])
              BY <5>1
            <6>6. MemLocs[bucket[p]][index] \in [key: KeyDomain, val: ValDomain]
              BY <6>4, <6>5, ElementOfSeq, Zenon
            <6>7. MemLocs[bucket[p]][index].val \in ValDomain
              BY <6>6
            <6> QED
              BY <6>1, <6>4, <6>7, Zenon
          <5>2. CASE bucket[p] = NULL \/ ~KeyInBktAtAddr(arg[p].key, bucket[p])
            BY <5>2, Zenon DEF KeyInBktAtAddr
          <5> QED
            BY <5>1, <5>2
        <4>9. (arg \in [ProcSet -> ArgDomain])'
          OBVIOUS
        <4>10. (ret \in [ProcSet -> RetDomain])'
          OBVIOUS
        <4>11. (\A p_1 \in ProcSet : (pc[p_1] # RemainderID) => arg[p_1] \in ArgsOf(LineIDtoOp(pc[p_1])))'
          <5> SUFFICES arg[p] \in ArgsOf(LineIDtoOp(pc'[p]))
            BY Zenon
          <5> QED
            BY RemDef, ZenonT(30) DEF LineIDtoOp, ArgsOf
        <4>12. AddrsOK'
          <5> SUFFICES ASSUME NEW p_1 \in ProcSet',
                              (pc[p_1] \in {"I4", "U4", "R4"})'
                       PROVE  (/\ \A q \in ProcSet : (p_1 # q => /\ newbkt[p_1] # bucket[q]
                                                                 /\ newbkt[p_1] # newbkt[q])
                               /\ \A idx \in 1..N  : (A[idx] # newbkt[p_1])
                               /\ newbkt[p_1] # bucket[p_1]
                               /\ newbkt[p_1] \in AllocAddrs)'
            BY DEF AddrsOK
          <5>1. (\A q \in ProcSet : (p_1 # q => /\ newbkt[p_1] # bucket[q]
                                                /\ newbkt[p_1] # newbkt[q]))'
            BY DEF AddrsOK
          <5>2. (\A idx \in 1..N  : (A[idx] # newbkt[p_1]))'
            BY DEF AddrsOK
          <5>3. (newbkt[p_1] # bucket[p_1])'
            BY DEF AddrsOK
          <5>4. (newbkt[p_1] \in AllocAddrs)'
            BY DEF AddrsOK
          <5>5. QED
            BY <5>1, <5>2, <5>3, <5>4
        <4>13. BktOK'
          <5> SUFFICES ASSUME NEW q \in ProcSet
                       PROVE  (/\ pc'[q] \in {"I3", "I4"} => (/\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                                                              /\ r'[q] = NULL)
                               /\ pc'[q] \in {"U3", "U4"} => (IF KeyInBktAtAddr(arg[q].key, bucket[q])'
                                                                  THEN (/\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                                                                        /\ r'[q] # NULL)
                                                                  ELSE r'[q] = NULL)
                               /\ pc'[q] \in {"R3", "R4"} => (/\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                                                              /\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                                                              /\ r'[q] # NULL))
            BY DEF BktOK
          <5>1. CASE pc'[q] \in {"I3", "I4"}
            <6> USE <5>1
            <6>1. CASE p = q
              <7>1. ~KeyInBktAtAddr(arg[q].key, bucket[q]) /\ r'[q] = NULL
                BY <6>1, Zenon
              <7> QED 
                BY <7>1, Zenon DEF KeyInBktAtAddr
            <6> SUFFICES ASSUME p # q
                         PROVE  ~KeyInBktAtAddr(arg[q].key, bucket[q])' /\ r'[q] = NULL
              BY <6>1
            <6>2. ~KeyInBktAtAddr(arg[q].key, bucket[q]) /\ r[q] = NULL
              BY Zenon DEF BktOK
            <6> QED
              BY <6>2, Zenon DEF KeyInBktAtAddr
          <5>2. CASE pc'[q] \in {"U3", "U4"}
            <6> USE <5>2
            <6> SUFFICES IF KeyInBktAtAddr(arg[q].key, bucket[q])'
                            THEN (/\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                                  /\ r'[q] # NULL)
                            ELSE r'[q] = NULL
              OBVIOUS
            <6>1. IF KeyInBktAtAddr(arg[q].key, bucket[q])
                     THEN (/\ r[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                           /\ r[q] # NULL)
                     ELSE r[q] = NULL
              BY Zenon DEF BktOK
            <6>2. KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
              BY Zenon DEF KeyInBktAtAddr
            <6>3. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs'[bucket'[q]][CHOOSE index \in 1..Len(MemLocs'[bucket'[q]]) :
                                   MemLocs'[bucket'[q]][index].key = arg'[q].key].val
              BY DEF ValOfKeyInBktAtAddr
            <6>4. MemLocs = MemLocs' /\ arg = arg' /\ bucket[q] = bucket'[q]
              BY Zenon
            <6>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs[bucket'[q]][CHOOSE index \in 1..Len(MemLocs[bucket'[q]]) :
                                  MemLocs[bucket'[q]][index].key = arg[q].key].val
              BY Zenon, <6>3, <6>4
            <6>6. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs[bucket[q]][CHOOSE index \in 1..Len(MemLocs[bucket[q]]) :
                                 MemLocs[bucket[q]][index].key = arg[q].key].val
              BY <6>4, <6>5
            <6>7. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
              BY <6>6, Zenon DEF ValOfKeyInBktAtAddr
            <6> QED
              BY <6>1, <6>2, <6>7, Zenon
          <5>3. CASE pc'[q] \in {"R3", "R4"}
            <6> USE <5>3
            <6> SUFFICES /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                         /\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                         /\ r'[q] # NULL
              OBVIOUS
            <6>1. /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                  /\ r[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                  /\ r[q] # NULL
              BY Zenon DEF BktOK
            <6>2. KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
              BY Zenon DEF KeyInBktAtAddr
            <6>3. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs'[bucket'[q]][CHOOSE index \in 1..Len(MemLocs'[bucket'[q]]) :
                                   MemLocs'[bucket'[q]][index].key = arg'[q].key].val
              BY DEF ValOfKeyInBktAtAddr
            <6>4. MemLocs = MemLocs' /\ arg = arg' /\ bucket[q] = bucket'[q]
              BY Zenon
            <6>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs[bucket'[q]][CHOOSE index \in 1..Len(MemLocs[bucket'[q]]) :
                                  MemLocs[bucket'[q]][index].key = arg[q].key].val
              BY Zenon, <6>3, <6>4
            <6>6. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs[bucket[q]][CHOOSE index \in 1..Len(MemLocs[bucket[q]]) :
                                 MemLocs[bucket[q]][index].key = arg[q].key].val
              BY <6>4, <6>5
            <6>7. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
              BY <6>6, Zenon DEF ValOfKeyInBktAtAddr
            <6> QED
              BY <6>1, <6>2, <6>7, Zenon
          <5> QED
            BY <5>1, <5>2, <5>3
        <4>14. Uniq'
          <5> SUFFICES ASSUME NEW addr \in AllocAddrs', 
                              NEW bucket_arr, bucket_arr = MemLocs'[addr],
                              NEW j1 \in 1..Len(bucket_arr),
                              NEW j2 \in 1..Len(bucket_arr),
                              bucket_arr[j1].key = bucket_arr[j2].key
                       PROVE  j1 = j2
            BY Zenon DEF Uniq
          <5> QED
            BY Zenon DEF Uniq
        <4>15. NewBktOK'
          <5> SUFFICES ASSUME NEW q \in ProcSet
                       PROVE  /\ pc'[q] = "I4" => /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                                  /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                                                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                            /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                               (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
                              /\ pc'[q] = "U4" => /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                                  /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                                                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                            /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                               (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
                              /\ pc'[q] = "R4" => /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                            /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                               (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
            BY ZenonT(60) DEF NewBktOK
          <5>0. ASSUME NEW k \in KeyDomain
                PROVE  /\ pc[q] \in {"I4", "U4", "R4"} => KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, bucket[q])'
                       /\ KeyInBktAtAddr(k, newbkt[q]) = KeyInBktAtAddr(k, newbkt[q])'
                       /\ pc[q] \in {"I4", "U4", "R4"} => ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])'
                       /\ ValOfKeyInBktAtAddr(k, newbkt[q]) = ValOfKeyInBktAtAddr(k, newbkt[q])'
            <6> USE <5>0
            <6>1. pc[q] \in {"I4", "U4", "R4"} => KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, bucket[q])'
              BY Zenon DEF KeyInBktAtAddr
            <6>2. KeyInBktAtAddr(k, newbkt[q]) = KeyInBktAtAddr(k, newbkt[q])'
              BY Zenon DEF KeyInBktAtAddr
            <6>3. pc[q] \in {"I4", "U4", "R4"} => ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])'
              <7> SUFFICES ASSUME pc[q] \in {"I4", "U4", "R4"}
                           PROVE  ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])'
                OBVIOUS
              <7> DEFINE bkt_arr == MemLocs'[bucket'[q]]
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
              <7>1. ValOfKeyInBktAtAddr(k, bucket[q])' = bkt_arr[idx].val
                BY Zenon DEF ValOfKeyInBktAtAddr
              <7>2. bkt_arr = MemLocs[bucket[q]]
                BY Zenon
              <7>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
                BY Zenon
              <7> QED
                BY <7>1, <7>2, <7>3, Isa DEF ValOfKeyInBktAtAddr
            <6>4. ValOfKeyInBktAtAddr(k, newbkt[q]) = ValOfKeyInBktAtAddr(k, newbkt[q])'
              <7> DEFINE bkt_arr == MemLocs'[newbkt'[q]]
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
              <7>1. ValOfKeyInBktAtAddr(k, newbkt[q])' = bkt_arr[idx].val
                BY Zenon DEF ValOfKeyInBktAtAddr
              <7>2. bkt_arr = MemLocs[newbkt[q]]
                BY Zenon
              <7>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
                BY Zenon
              <7> QED
                BY <7>1, <7>2, <7>3, Isa DEF ValOfKeyInBktAtAddr
            <6> QED
              BY <6>1, <6>2, <6>3, <6>4
          <5>1. CASE pc'[q] = "I4"
            <6> USE <5>1
            <6> SUFFICES /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                         /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                         /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                   /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                      (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
              OBVIOUS
            <6>1. pc[q] = "I4" /\ arg[q].key \in KeyDomain
              BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
            <6>2. /\ KeyInBktAtAddr(arg[q].key, newbkt[q])
                  /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q]) = arg[q].val
                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                            /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                               (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
              BY <6>1, Zenon DEF NewBktOK
            <6> QED
              BY <5>0, <6>1, <6>2, ZenonT(30)
          <5>2. CASE pc'[q] = "U4"
            <6> USE <5>2
            <6> SUFFICES /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                         /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                         /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                   /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                      (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
              OBVIOUS
            <6>1. pc[q] = "U4" /\ arg[q].key \in KeyDomain
              BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
            <6>2. /\ KeyInBktAtAddr(arg[q].key, newbkt[q])
                  /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q]) = arg[q].val
                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                            /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                               (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
              BY <6>1, Zenon DEF NewBktOK
            <6> QED
              BY <5>0, <6>1, <6>2, ZenonT(30)
          <5>3. CASE pc'[q] = "R4"
            <6> USE <5>3
            <6> SUFFICES /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])'
                         /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                   /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                      (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
              OBVIOUS
            <6>1. pc[q] = "R4" /\ arg[q].key \in KeyDomain
              BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
            <6>2. /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])
                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                            /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                               (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
              BY <6>1, Zenon DEF NewBktOK
            <6> QED
              BY <5>0, <6>1, <6>2, ZenonT(30)
          <5> QED
            BY <5>1, <5>2, <5>3
        <4> QED
          BY <4>1, <4>10, <4>11, <4>12, <4>13, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, <4>14, <4>15 DEF Inv
      <3>5. CASE Line = I3(p)
        <4> USE <3>5 DEF I3
        <4>1. PTypeOK'
          BY NextPTypeOK
        <4>2. (pc \in [ProcSet -> LineIDs])'
          BY Isa DEF LineIDs
        <4>3. (A \in [1..N -> AllocAddrs \union {NULL}])'
          OBVIOUS
        <4>4. (MemLocs \in [Addrs -> Seq([key: KeyDomain, val: ValDomain])])'
          <5>1. CASE bucket[p] = NULL
            <6> USE <5>1
            <6>1. PICK addr \in Addrs : MemLocs' = [MemLocs EXCEPT ![addr] = <<arg[p]>>]
              BY Zenon
            <6>2. MemLocs'[addr] \in Seq([key: KeyDomain, val: ValDomain])
              <7> SUFFICES arg[p] \in [key: KeyDomain, val: ValDomain]
                BY <6>1 DEF Seq
              <7> QED
                BY RemDef, Zenon DEF LineIDtoOp, ArgsOf
            <6> QED
              BY <6>1, <6>2
          <5>2. CASE bucket[p] # NULL
            <6> USE <5>2
            <6>1. PICK addr \in Addrs : MemLocs' = [MemLocs EXCEPT ![addr] = Append(MemLocs[bucket[p]], arg[p])]
              BY Zenon
            <6> SUFFICES Append(MemLocs[bucket[p]], arg[p]) \in Seq([key: KeyDomain, val: ValDomain])
              BY <6>1, Zenon
            <6> SUFFICES /\ MemLocs[bucket[p]] \in Seq([key: KeyDomain, val: ValDomain])
                         /\ arg[p] \in [key: KeyDomain, val: ValDomain]
              BY AppendProperties, Zenon
            <6>2. MemLocs[bucket[p]] \in Seq([key: KeyDomain, val: ValDomain])
              OBVIOUS
            <6>3. arg[p] \in [key: KeyDomain, val: ValDomain]
              BY RemDef, Zenon DEF LineIDtoOp, ArgsOf
            <6> QED
              BY <6>2, <6>3
          <5> QED
            BY <5>1, <5>2
        <4>5. (AllocAddrs \in SUBSET Addrs)'
          OBVIOUS
        <4>6. (bucket \in [ProcSet -> AllocAddrs \union {NULL}])'
          OBVIOUS
        <4>7. (newbkt \in [ProcSet -> AllocAddrs \union {NULL}])'
          OBVIOUS
        <4>8. (r \in [ProcSet -> ValDomain \union {NULL}])'
          OBVIOUS
        <4>9. (arg \in [ProcSet -> ArgDomain])'
          OBVIOUS
        <4>10. (ret \in [ProcSet -> RetDomain])'
          OBVIOUS
        <4>11. (\A p_1 \in ProcSet : (pc[p_1] # RemainderID) => arg[p_1] \in ArgsOf(LineIDtoOp(pc[p_1])))'
          <5> SUFFICES arg[p] \in ArgsOf(LineIDtoOp(pc'[p]))
            BY Zenon
          <5> QED
            BY RemDef, ZenonT(30) DEF LineIDtoOp, ArgsOf
        <4>12. AddrsOK'
          <5> SUFFICES ASSUME NEW p_1 \in ProcSet,
                              pc'[p_1] \in {"I4", "U4", "R4"}
                       PROVE  /\ \A q \in ProcSet : (p_1 # q => /\ newbkt'[p_1] # bucket'[q]
                                                                /\ newbkt'[p_1] # newbkt'[q])
                              /\ \A idx \in 1..N  : (A'[idx] # newbkt'[p_1])
                              /\ newbkt'[p_1] # bucket'[p_1]
                              /\ newbkt'[p_1] \in AllocAddrs'
            BY Zenon DEF AddrsOK
          <5>0. PICK addr \in Addrs : /\ addr \notin AllocAddrs
                                      /\ AllocAddrs' = AllocAddrs \cup {addr}
                                      /\ newbkt' = [newbkt EXCEPT ![p] = addr]
            BY Zenon
          <5>1. CASE p_1 = p
            <6>1. newbkt'[p_1] \notin AllocAddrs /\ newbkt'[p_1] # NULL
              BY <5>0, <5>1, NULLDef
            <6>2. \A q \in ProcSet : (p_1 # q => /\ newbkt'[p_1] # bucket'[q]
                                                 /\ newbkt'[p_1] # newbkt'[q])
              <7> SUFFICES ASSUME NEW q \in ProcSet,
                                  p_1 # q
                           PROVE  /\ newbkt'[p_1] # bucket'[q]
                                  /\ newbkt'[p_1] # newbkt'[q]
                OBVIOUS
              <7>1. bucket[q] \in AllocAddrs \/ bucket[q] = NULL
                OBVIOUS
              <7>2. bucket'[q] \in AllocAddrs \/ bucket'[q] = NULL
                BY <7>1, Zenon
              <7>3. newbkt[q] \in AllocAddrs \/ newbkt[q] = NULL
                OBVIOUS
              <7>4. newbkt'[q] \in AllocAddrs \/ newbkt'[q] = NULL
                BY <5>1, <7>3, Zenon
              <7>5. newbkt'[p_1] # bucket'[q]
                BY <5>1, <6>1, <7>2 DEF AddrsOK
              <7>6. newbkt'[p_1] # newbkt'[q]
                BY <5>1, <6>1, <7>4 DEF AddrsOK
              <7>7. QED
                BY <7>5, <7>6
            <6>3. \A idx \in 1..N  : (A'[idx] # newbkt'[p_1])
              <7> SUFFICES ASSUME NEW idx \in 1..N
                           PROVE  A'[idx] # newbkt'[p_1]
                OBVIOUS
              <7>1. A'[idx] \in AllocAddrs \/ A'[idx] = NULL
                BY <4>3, Zenon
              <7> QED
                BY <6>1, <7>1
            <6>4. newbkt'[p_1] # bucket'[p_1]
              <7>1. bucket'[p_1] \in AllocAddrs \/ bucket'[p_1] = NULL
                BY Zenon
              <7> QED
                BY <6>1, <7>1
            <6>5. newbkt'[p_1] \in AllocAddrs'
              BY <5>1 DEF AddrsOK
            <6>6. QED
              BY <6>2, <6>3, <6>4, <6>5
          <5>2. CASE p_1 # p
            <6>1. \A q \in ProcSet : (p_1 # q => /\ newbkt'[p_1] # bucket'[q]
                                                 /\ newbkt'[p_1] # newbkt'[q])
              <7> SUFFICES ASSUME NEW q \in ProcSet,
                                  p_1 # q
                           PROVE  /\ newbkt'[p_1] # bucket'[q]
                                  /\ newbkt'[p_1] # newbkt'[q]
                BY <5>2 DEF AddrsOK
              <7>1. newbkt'[p_1] # bucket'[q]
                BY <5>2 DEF AddrsOK
              <7>2. newbkt'[p_1] # newbkt'[q]
                <8>1. CASE q = p
                  <9>1. newbkt'[q] \notin AllocAddrs
                    BY <8>1, Zenon
                  <9>2. newbkt'[p_1] \in AllocAddrs
                    BY <5>2, Zenon DEF AddrsOK
                  <9> QED  
                    BY <9>1, <9>2
                <8>2. CASE q # p
                  BY <5>2, <8>2 DEF AddrsOK
                <8> QED
                  BY <8>1, <8>2
              <7>3. QED
                BY <7>1, <7>2
            <6>2. \A idx \in 1..N  : (A'[idx] # newbkt'[p_1])
              BY <5>2 DEF AddrsOK
            <6>3. newbkt'[p_1] # bucket'[p_1]
              BY <5>2 DEF AddrsOK
            <6>4. newbkt'[p_1] \in AllocAddrs'
              BY <5>2 DEF AddrsOK
            <6>5. QED
              BY <6>1, <6>2, <6>3, <6>4
          <5> QED
            BY <5>1, <5>2
        <4>13. BktOK'
          <5> SUFFICES ASSUME NEW q \in ProcSet
                       PROVE  (/\ pc'[q] \in {"I3", "I4"} => (/\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                                                              /\ r'[q] = NULL)
                               /\ pc'[q] \in {"U3", "U4"} => (IF KeyInBktAtAddr(arg[q].key, bucket[q])'
                                                                  THEN (/\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                                                                        /\ r'[q] # NULL)
                                                                  ELSE r'[q] = NULL)
                               /\ pc'[q] \in {"R3", "R4"} => (/\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                                                              /\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                                                              /\ r'[q] # NULL))
            BY DEF BktOK
          <5>0. PICK addr \in Addrs : /\ addr \notin AllocAddrs
                                      /\ AllocAddrs' = AllocAddrs \cup {addr}
                                      /\ newbkt' = [newbkt EXCEPT ![p] = addr]
                                      /\ \A a \in Addrs : a # addr => MemLocs[a] = MemLocs'[a]
            BY Zenon
          <5>1. CASE pc'[q] \in {"I3", "I4"}
            <6>1. KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
              <7>1. CASE bucket[q] = NULL
                <8> USE <7>1
                <8>1. KeyInBktAtAddr(arg[q].key, bucket[q]) = FALSE
                  BY DEF KeyInBktAtAddr
                <8>2. bucket'[q] = NULL
                  BY Zenon
                <8>3. KeyInBktAtAddr(arg[q].key, bucket[q])' = FALSE
                  BY <8>2 DEF KeyInBktAtAddr
                <8> QED
                  BY <8>1, <8>3, Zenon
              <7>2. CASE bucket[q] # NULL
                <8> USE <7>2
                <8>1. KeyInBktAtAddr(arg[q].key, bucket[q]) = \E index \in 1..Len(MemLocs[bucket[q]]) : MemLocs[bucket[q]][index].key = arg[q].key
                  BY Zenon DEF KeyInBktAtAddr
                <8>2. bucket'[q] = bucket[q] /\ bucket[q] \in AllocAddrs
                  BY Zenon
                <8>3. MemLocs'[bucket[q]] = MemLocs[bucket[q]] /\ arg' = arg
                  BY <8>2, Zenon
                <8>4. KeyInBktAtAddr(arg[q].key, bucket[q])' = \E index \in 1..Len(MemLocs'[bucket'[q]]) : MemLocs'[bucket'[q]][index].key = arg'[q].key
                  BY Zenon DEF KeyInBktAtAddr
                <8>5. KeyInBktAtAddr(arg[q].key, bucket[q])' = \E index \in 1..Len(MemLocs[bucket[q]]) : MemLocs[bucket[q]][index].key = arg[q].key
                  BY <8>2, <8>3, <8>4
                <8> QED
                  BY <8>1, <8>5
              <7> QED
                BY <7>1, <7>2
            <6>2. CASE p = q
              BY <6>2, <6>1, Zenon DEF BktOK
            <6> USE <5>1
            <6> SUFFICES ASSUME p # q
                         PROVE  ~KeyInBktAtAddr(arg[q].key, bucket[q])' /\ r'[q] = NULL
              BY <6>2
            <6>3. ~KeyInBktAtAddr(arg[q].key, bucket[q]) /\ r[q] = NULL
              BY Zenon DEF BktOK
            <6> QED
              BY <6>3, <6>1, Zenon DEF KeyInBktAtAddr
          <5>2. CASE pc'[q] \in {"U3", "U4"}
            <6> USE <5>2
            <6> SUFFICES IF KeyInBktAtAddr(arg[q].key, bucket[q])'
                            THEN (/\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                                  /\ r'[q] # NULL)
                            ELSE r'[q] = NULL
              OBVIOUS
            <6>1. IF KeyInBktAtAddr(arg[q].key, bucket[q])
                     THEN (/\ r[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                           /\ r[q] # NULL)
                     ELSE r[q] = NULL
              BY Zenon DEF BktOK
            <6>2. KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
              <7>1. CASE bucket[q] = NULL
                <8> USE <7>1
                <8>1. KeyInBktAtAddr(arg[q].key, bucket[q]) = FALSE
                  BY DEF KeyInBktAtAddr
                <8>2. bucket'[q] = NULL
                  BY Zenon
                <8>3. KeyInBktAtAddr(arg[q].key, bucket[q])' = FALSE
                  BY <8>2 DEF KeyInBktAtAddr
                <8> QED
                  BY <8>1, <8>3, Zenon
              <7>2. CASE bucket[q] # NULL
                <8> USE <7>2
                <8>1. KeyInBktAtAddr(arg[q].key, bucket[q]) = \E index \in 1..Len(MemLocs[bucket[q]]) : MemLocs[bucket[q]][index].key = arg[q].key
                  BY Zenon DEF KeyInBktAtAddr
                <8>2. bucket'[q] = bucket[q] /\ bucket[q] \in AllocAddrs
                  BY Zenon
                <8>3. MemLocs'[bucket[q]] = MemLocs[bucket[q]] /\ arg' = arg
                  BY <8>2, Zenon
                <8>4. KeyInBktAtAddr(arg[q].key, bucket[q])' = \E index \in 1..Len(MemLocs'[bucket'[q]]) : MemLocs'[bucket'[q]][index].key = arg'[q].key
                  BY Zenon DEF KeyInBktAtAddr
                <8>5. KeyInBktAtAddr(arg[q].key, bucket[q])' = \E index \in 1..Len(MemLocs[bucket[q]]) : MemLocs[bucket[q]][index].key = arg[q].key
                  BY <8>2, <8>3, <8>4
                <8> QED
                  BY <8>1, <8>5
              <7> QED
                BY <7>1, <7>2
            <6>3. CASE KeyInBktAtAddr(arg[q].key, bucket[q])
              <7>1. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
                MemLocs'[bucket'[q]][CHOOSE index \in 1..Len(MemLocs'[bucket'[q]]) :
                                     MemLocs'[bucket'[q]][index].key = arg'[q].key].val
                BY DEF ValOfKeyInBktAtAddr
              <7>2. bucket'[q] = bucket[q] /\ bucket[q] \in AllocAddrs
                BY Zenon, <6>3 DEF KeyInBktAtAddr
              <7>3. MemLocs'[bucket'[q]] = MemLocs[bucket[q]]
                BY <5>0, <7>2, Zenon
              <7>4. arg' = arg
                BY Zenon
              <7>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
                MemLocs[bucket[q]][CHOOSE index \in 1..Len(MemLocs[bucket[q]]) :
                                    MemLocs[bucket[q]][index].key = arg[q].key].val
                BY <7>1, <7>3, <7>4
              <7>6. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                BY <7>5, Zenon DEF ValOfKeyInBktAtAddr
              <7>7. r'[q] = r[q]
                BY Zenon
              <7> QED
                BY <6>1, <6>2, <6>3, <7>6, <7>7
            <6>4. CASE ~KeyInBktAtAddr(arg[q].key, bucket[q])
              BY <6>1, <6>2, <6>4, Zenon
            <6> QED
              BY <6>3, <6>4
          <5>3. CASE pc'[q] \in {"R3", "R4"}
            <6> USE <5>3
            <6> SUFFICES /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                         /\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                         /\ r'[q] # NULL
              OBVIOUS
            <6>1. /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                  /\ r[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                  /\ r[q] # NULL
              BY Zenon DEF BktOK
            <6>2. MemLocs[bucket[q]] = MemLocs'[bucket'[q]]
              <7>1. bucket[q] = bucket'[q]
                BY Zenon
              <7>2. bucket[q] \in AllocAddrs
                BY Zenon, <6>1 DEF KeyInBktAtAddr
              <7>3. bucket[q] # addr
                BY <5>0, <7>2
              <7>4. MemLocs'[bucket[q]] = MemLocs[bucket[q]]
                BY <5>0, <7>2, <7>3, Zenon
              <7> QED
                BY <7>1, <7>4
            <6>3. KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
              BY <6>2, Zenon DEF KeyInBktAtAddr
            <6>4. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs'[bucket'[q]][CHOOSE index \in 1..Len(MemLocs'[bucket'[q]]) :
                                   MemLocs'[bucket'[q]][index].key = arg'[q].key].val
              BY DEF ValOfKeyInBktAtAddr
            <6>5. arg = arg'
              BY Zenon
            <6>6. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs[bucket[q]][CHOOSE index \in 1..Len(MemLocs[bucket[q]]) :
                                   MemLocs[bucket[q]][index].key = arg'[q].key].val
              BY <6>2, <6>4
            <6>7. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs[bucket[q]][CHOOSE index \in 1..Len(MemLocs[bucket[q]]) :
                                  MemLocs[bucket[q]][index].key = arg[q].key].val
              BY Zenon, <6>6, <6>5
            <6>8. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
              BY <6>7, Zenon DEF ValOfKeyInBktAtAddr
            <6> QED
              BY <6>1, <6>3, <6>8, Zenon
          <5> QED
            BY <5>1, <5>2, <5>3
        <4>14. Uniq'
          <5> SUFFICES ASSUME NEW a \in AllocAddrs', 
                              NEW bucket_arr, bucket_arr = MemLocs'[a],
                              NEW j1 \in 1..Len(bucket_arr),
                              NEW j2 \in 1..Len(bucket_arr),
                              bucket_arr[j1].key = bucket_arr[j2].key
                       PROVE  j1 = j2
            BY Zenon DEF Uniq
          <5>1. PICK addr \in Addrs : /\ addr \notin AllocAddrs
                                      /\ AllocAddrs' = AllocAddrs \cup {addr}
                                      /\ IF bucket[p] = NULL
                                            THEN MemLocs' = [MemLocs EXCEPT ![addr] = <<arg[p]>>]
                                            ELSE MemLocs' = [MemLocs EXCEPT ![addr] = Append(MemLocs[bucket[p]], arg[p])]
            BY Zenon
          <5>2. \A ad \in Addrs : ad # addr => MemLocs'[ad] = MemLocs[ad]
            BY <5>1, Zenon
          <5>3. CASE a # addr
            BY <5>1, <5>2, <5>3, Zenon DEF Uniq
          <5> SUFFICES ASSUME a = addr
                       PROVE  j1 = j2
            BY <5>3
          <5>4. CASE bucket[p] = NULL
            <6>1. Len(bucket_arr) = 1
              BY <5>1, <5>4
            <6> QED
              BY <6>1
          <5>5. CASE bucket[p] # NULL
            <6>1. bucket_arr = Append(MemLocs[bucket[p]], arg[p])
              BY <5>1, <5>5, Zenon
            <6>2. MemLocs[bucket[p]] \in Seq([key: KeyDomain, val: ValDomain])
              BY <5>5, Zenon
            <6>3. arg[p] \in [key: KeyDomain, val: ValDomain]
              BY RemDef, Zenon DEF LineIDtoOp, ArgsOf
            <6>A. Len(bucket_arr) = Len(MemLocs[bucket[p]])+1
              BY <6>1, <6>2, <6>3, AppendProperties
            <6>4. \A index \in 1..Len(MemLocs[bucket[p]]) : Append(MemLocs[bucket[p]], arg[p])[index] = MemLocs[bucket[p]][index]
              BY <6>2, <6>3, AppendProperties
            <6>5. \A index \in 1..Len(MemLocs[bucket[p]]) : bucket_arr[index] = MemLocs[bucket[p]][index]
              BY <6>1, <6>4, Zenon
            <6>6. CASE j1 = Len(bucket_arr)
              <7>1. bucket_arr[j1] = arg[p]
                BY <6>1, <6>2, <6>3, <6>6, AppendProperties
              <7>2. \A index \in 1..Len(MemLocs[bucket[p]]) : MemLocs[bucket[p]][index].key # arg[p].key
                BY Zenon, <5>5 DEF KeyInBktAtAddr, BktOK
              <7>3. \A index \in 1..Len(MemLocs[bucket[p]]) : bucket_arr[index].key # arg[p].key
                BY <6>5, <7>2, Zenon
              <7>4. j2 \notin 1..Len(MemLocs[bucket[p]])
                BY <7>1, <7>3
              <7>5. j2 = Len(bucket_arr)
                BY <6>A, <7>4
              <7> QED
                BY <6>6, <7>5
            <6>7. CASE j2 = Len(bucket_arr)
              <7>1. bucket_arr[j2] = arg[p]
                BY <6>1, <6>2, <6>3, <6>7, AppendProperties
              <7>2. \A index \in 1..Len(MemLocs[bucket[p]]) : MemLocs[bucket[p]][index].key # arg[p].key
                BY Zenon, <5>5 DEF KeyInBktAtAddr, BktOK
              <7>3. \A index \in 1..Len(MemLocs[bucket[p]]) : bucket_arr[index].key # arg[p].key
                BY <6>5, <7>2, Zenon
              <7>4. j1 \notin 1..Len(MemLocs[bucket[p]])
                BY <7>1, <7>3
              <7>5. j1 = Len(bucket_arr)
                BY <6>A, <7>4
              <7> QED
                BY <6>6, <7>5
            <6>8. CASE j1 # Len(bucket_arr) /\ j2 # Len(bucket_arr)
              <7>1. j1 \in 1..Len(MemLocs[bucket[p]]) /\ j2 \in 1..Len(MemLocs[bucket[p]])
                BY <6>A, <6>8
              <7>2. bucket[p] \in AllocAddrs
                BY <5>5
              <7> QED
                BY <6>5, <7>1, <7>2 DEF Uniq
            <6> QED
              BY <6>6, <6>7, <6>8
          <5> QED
            BY <5>4, <5>5
        <4>15. NewBktOK'
          <5> SUFFICES ASSUME NEW q \in ProcSet
                       PROVE  /\ pc'[q] = "I4" => /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                                  /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                                                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                            /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                               (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
                              /\ pc'[q] = "U4" => /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                                  /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                                                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                            /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                               (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
                              /\ pc'[q] = "R4" => /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                            /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                               (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
            BY ZenonT(60) DEF NewBktOK
          <5> PICK addr \in Addrs : /\ addr \notin AllocAddrs
                                    /\ AllocAddrs' = AllocAddrs \cup {addr}
                                    /\ newbkt' = [newbkt EXCEPT ![p] = addr]
                                    /\ IF bucket[p] = NULL
                                          THEN MemLocs' = [MemLocs EXCEPT ![addr] = <<arg[p]>>]
                                          ELSE MemLocs' = [MemLocs EXCEPT ![addr] = Append(MemLocs[bucket[p]], arg[p])]
            BY Zenon
          <5>A. \A a \in Addrs : a # addr => MemLocs'[a] = MemLocs[a]
            BY ZenonT(30)
          <5>B. ASSUME NEW k \in KeyDomain, q # p, pc[q] \in {"I4", "U4", "R4"}
                PROVE  /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, bucket[q])'
                       /\ KeyInBktAtAddr(k, newbkt[q]) = KeyInBktAtAddr(k, newbkt[q])'
                       /\ KeyInBktAtAddr(k, bucket[q]) => (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])')
                       /\ KeyInBktAtAddr(k, newbkt[q]) => (ValOfKeyInBktAtAddr(k, newbkt[q]) = ValOfKeyInBktAtAddr(k, newbkt[q])')
            <6> USE <5>B
            <6>1. bucket[q] = bucket'[q] /\ newbkt'[q] = newbkt[q] /\ newbkt[q] \in AllocAddrs
              BY NULLDef, Zenon DEF AddrsOK
            <6>2. MemLocs[newbkt[q]] = MemLocs'[newbkt'[q]]
              BY <5>A, <6>1, Zenon
            <6>3. KeyInBktAtAddr(k, newbkt[q]) = KeyInBktAtAddr(k, newbkt[q])'  
              BY Zenon, <6>1, <6>2 DEF KeyInBktAtAddr
            <6>4. ValOfKeyInBktAtAddr(k, newbkt[q]) = ValOfKeyInBktAtAddr(k, newbkt[q])'
              <7> DEFINE bkt_arr == MemLocs'[newbkt'[q]]
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
              <7>1. ValOfKeyInBktAtAddr(k, newbkt[q])' = bkt_arr[idx].val
                BY Zenon DEF ValOfKeyInBktAtAddr
              <7>2. bkt_arr = MemLocs[newbkt[q]]
                BY Zenon, <6>2
              <7>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
                BY Zenon
              <7> QED
                BY <7>1, <7>2, <7>3, Isa DEF ValOfKeyInBktAtAddr
            <6>5. CASE bucket[q] = NULL
              BY <6>1, <6>3, <6>4, <6>5, Zenon DEF KeyInBktAtAddr
            <6> SUFFICES ASSUME bucket[q] \in AllocAddrs
                         PROVE  /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, bucket[q])'
                                /\ KeyInBktAtAddr(k, bucket[q]) => (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])')
              BY NULLDef, <6>5, <6>3, <6>4, Zenon
            <6>6. MemLocs[bucket[q]] = MemLocs'[bucket'[q]]
              BY <5>A, <6>1, Zenon
            <6>7. KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, bucket[q])'  
              BY Zenon, <6>1, <6>6 DEF KeyInBktAtAddr
            <6> SUFFICES ASSUME KeyInBktAtAddr(k, bucket[q])
                         PROVE  ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])'
              BY <6>7, Zenon
            <6>8. ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])'
              <7> DEFINE bkt_arr == MemLocs'[bucket'[q]]
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
              <7>1. ValOfKeyInBktAtAddr(k, bucket[q])' = bkt_arr[idx].val
                BY Zenon DEF ValOfKeyInBktAtAddr
              <7>2. bkt_arr = MemLocs[bucket[q]]
                BY Zenon, <6>6
              <7>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
                BY Zenon
              <7> QED
                BY <7>1, <7>2, <7>3, Isa DEF ValOfKeyInBktAtAddr
            <6> QED
              BY <6>8
          <5>1. CASE pc'[q] = "I4"
            <6> USE <5>1
            <6> SUFFICES /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                         /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                         /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                   /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                      (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
              OBVIOUS
            <6>1. CASE q = p
              <7> USE <6>1
              <7>1. CASE bucket[p] = NULL
                <8> USE <7>1
                <8> DEFINE bkt_arr == MemLocs'[newbkt'[q]]
                <8>1. newbkt'[q] = addr /\ bkt_arr = <<arg[q]>> /\ arg = arg'
                  BY Zenon
                <8>2. KeyInBktAtAddr(arg[q].key, newbkt[q])'
                  <9> SUFFICES newbkt'[q] # NULL /\ \E index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg'[q].key
                    BY Zenon DEF KeyInBktAtAddr
                  <9> SUFFICES newbkt'[q] # NULL /\ \E index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
                    BY <8>1 
                  <9>1. newbkt'[q] # NULL
                    BY <8>1, NULLDef, Zenon
                  <9>2. Len(bkt_arr) = 1
                    BY <8>1
                  <9>3. 1 \in 1..Len(bkt_arr)
                    BY <9>2
                  <9>4. bkt_arr[1].key = arg[q].key
                    BY <8>1
                  <9> QED
                    BY <9>1, <9>3, <9>4
                <8>3. ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                  <9> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
                  <9>1. ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = bkt_arr[idx].val
                    BY <8>1, Zenon DEF ValOfKeyInBktAtAddr
                  <9>2. Len(bkt_arr) = 1
                    BY <8>1
                  <9>3. \E index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
                    BY <8>1, <8>2, Zenon DEF KeyInBktAtAddr
                  <9>4. idx = 1
                    BY <9>2, <9>3
                  <9>5. bkt_arr[idx].val = arg[q].val
                    BY <8>1, <9>4, Isa
                  <9> QED
                    BY <9>1, <9>5
                <8>4. ASSUME NEW k \in KeyDomain, k # arg[q].key
                      PROVE  /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])' 
                             /\ KeyInBktAtAddr(k, bucket[q])' =>
                                (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
                  <9> USE <8>4
                  <9>1. KeyInBktAtAddr(k, bucket[q])' = FALSE
                    BY Zenon DEF KeyInBktAtAddr
                  <9>2. KeyInBktAtAddr(k, newbkt[q])' = FALSE
                    <10>1. Len(bkt_arr) = 1
                      BY <8>1
                    <10>2. \A index \in 1..Len(bkt_arr) : index = 1
                      BY <10>1
                    <10>3. \A index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
                      BY <10>2
                    <10> QED
                      BY <10>3, Zenon DEF KeyInBktAtAddr 
                  <9> QED
                    BY <9>1, <9>2, Zenon
                <8> QED
                  BY <8>2, <8>3, <8>4
              <7>2. CASE bucket[p] # NULL
                <8> USE <7>2
                <8> DEFINE bkt_arr == MemLocs'[newbkt'[q]]
                <8>1. newbkt'[q] = addr /\ bkt_arr = Append(MemLocs[bucket[q]], arg[q]) /\ arg = arg'
                  BY Zenon
                <8>2. KeyInBktAtAddr(arg[q].key, newbkt[q])'
                  <9> SUFFICES newbkt'[q] # NULL /\ \E index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg'[q].key
                    BY Zenon DEF KeyInBktAtAddr
                  <9> SUFFICES newbkt'[q] # NULL /\ \E index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
                    BY <8>1 
                  <9>1. newbkt'[q] # NULL
                    BY <8>1, NULLDef, Zenon
                  <9>2. MemLocs[bucket[q]] \in Seq([key: KeyDomain, val: ValDomain])
                    BY Zenon
                  <9>3. arg[q] \in [key: KeyDomain, val: ValDomain]
                    BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
                  <9>4. bkt_arr[Len(bkt_arr)] = arg[q]
                    BY <8>1, <9>2, <9>3, AppendProperties, Isa
                  <9>5. Len(bkt_arr) \in 1..Len(bkt_arr)
                    BY <9>2, <9>3, AppendProperties, LenProperties
                  <9> QED
                    BY <9>1, <9>4, <9>5
                <8>3. ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                  <9> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
                  <9>1. ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = bkt_arr[idx].val
                    BY Zenon, <8>1 DEF ValOfKeyInBktAtAddr
                  <9> PICK index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
                    BY Zenon, <8>1, <8>2 DEF KeyInBktAtAddr
                  <9> idx = index
                    OBVIOUS
                  <9>2. MemLocs[bucket[q]] \in Seq([key: KeyDomain, val: ValDomain])
                    BY Zenon
                  <9>3. arg[q] \in [key: KeyDomain, val: ValDomain]
                    BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
                  <9>4. bkt_arr[Len(bkt_arr)] = arg[q]
                    BY <8>1, <9>2, <9>3, AppendProperties, Isa
                  <9>5. Len(MemLocs[bucket[q]]) \in Nat /\ Len(bkt_arr) \in 1..Len(bkt_arr) /\ Len(bkt_arr) = Len(MemLocs[bucket[q]])+1
                    BY <9>2, <9>3, AppendProperties, LenProperties
                  <9>6. \A ind \in 1..Len(MemLocs[bucket[q]]) : MemLocs[bucket[q]][ind].key # arg[q].key
                    BY Zenon DEF BktOK, KeyInBktAtAddr
                  <9>7. index = Len(bkt_arr)
                    BY <9>5, <9>6, Z3T(90)
                  <9>8. bkt_arr[index] = arg[q]
                    BY <9>4, <9>7, Zenon
                  <9> QED
                    BY <9>1, <9>8, Zenon
                <8>4. ASSUME NEW k \in KeyDomain, k # arg[q].key
                      PROVE  /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])' 
                             /\ KeyInBktAtAddr(k, bucket[q])' =>
                                (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
                  <9> USE <8>4
                  <9>1. CASE KeyInBktAtAddr(k, bucket[q])' = TRUE
                    <10> USE <9>1
                    <10> SUFFICES /\ KeyInBktAtAddr(k, newbkt[q])'
                                  /\ ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])'
                      BY Zenon 
                    <10>1. bucket[q] \in AllocAddrs
                      BY Zenon
                    <10>2. bucket[q] # addr /\ bucket[q] = bucket'[q]
                      BY <10>1, Zenon
                    <10>3. MemLocs'[bucket'[q]] = MemLocs[bucket[q]]
                      BY Zenon, <5>A, <10>2
                    <10>4. \E index \in 1..Len(MemLocs[bucket[q]]) : MemLocs[bucket[q]][index].key = k
                      BY Zenon, <10>3 DEF KeyInBktAtAddr
                    <10>5. MemLocs[bucket[q]] \in Seq([key: KeyDomain, val: ValDomain])
                      BY Zenon
                    <10>6. arg[q] \in [key: KeyDomain, val: ValDomain]
                      BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
                    <10>7. /\ \A index \in 1..Len(MemLocs[bucket[q]]) : bkt_arr[index] = MemLocs[bucket[q]][index]
                           /\ Len(MemLocs[bucket[q]]) \in Nat
                           /\ Len(bkt_arr) = Len(MemLocs[bucket[q]])+1
                           /\ bkt_arr[Len(bkt_arr)] = arg[q]
                      BY <10>5, <10>6, AppendProperties, LenProperties
                    <10>8. \E index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
                      BY <10>4, <10>7
                    <10>9. newbkt'[q] # NULL
                      BY NULLDef
                    <10>10. KeyInBktAtAddr(k, newbkt[q])'
                      BY <8>1, <10>8, <10>9, Zenon DEF KeyInBktAtAddr
                    <10> DEFINE idx == CHOOSE index \in 1..Len(MemLocs'[bucket'[q]]) : MemLocs'[bucket'[q]][index].key = k
                    <10>11. ValOfKeyInBktAtAddr(k, bucket[q])' = MemLocs'[bucket'[q]][idx].val
                       BY Zenon, <10>3 DEF ValOfKeyInBktAtAddr
                    <10> PICK index \in 1..Len(MemLocs'[bucket'[q]]) : MemLocs'[bucket'[q]][index].key = k
                      BY Zenon DEF KeyInBktAtAddr
                    <10> idx = index
                      OBVIOUS
                    <10> index \in 1..Len(MemLocs[bucket[q]]) /\ MemLocs[bucket[q]][index].key = k
                      BY <10>3
                    <10>12. ValOfKeyInBktAtAddr(k, bucket[q])' = MemLocs[bucket[q]][index].val
                      BY <10>3, <10>11, Zenon
                    <10>13. ValOfKeyInBktAtAddr(k, bucket[q])' = bkt_arr[index].val
                      BY <10>12, <10>7, Zenon
                    <10>14. bkt_arr[Len(bkt_arr)].key # k
                      BY <10>7
                    <10>15. \A ind \in 1..Len(MemLocs[bucket[q]]) : MemLocs[bucket[q]][ind].key = MemLocs[bucket[q]][index].key => ind = index
                      BY Zenon, <10>1 DEF Uniq
                    <10>16. \A ind \in 1..Len(MemLocs[bucket[q]]) : ind # index => MemLocs[bucket[q]][ind].key # k
                      BY <10>15, Zenon
                    <10>17. \A ind \in 1..Len(bkt_arr) : ind # index => bkt_arr[ind].key # k
                      BY <10>16, <10>14, <10>7, Z3T(30)
                    <10>18. \E ind \in 1..Len(bkt_arr) : bkt_arr[ind].key = k
                      BY <10>7
                    <10>19. ValOfKeyInBktAtAddr(k, newbkt[q])' = bkt_arr[index].val
                      BY <8>1, <10>17, <10>18, Zenon DEF ValOfKeyInBktAtAddr
                    <10> QED
                      BY <10>10, <10>13, <10>19, Zenon
                  <9>2. CASE KeyInBktAtAddr(k, bucket[q])' = FALSE
                    <10> USE <9>2
                    <10> SUFFICES KeyInBktAtAddr(k, newbkt[q])' = FALSE
                      BY Zenon
                    <10>1. bucket[q] \in AllocAddrs
                      BY Zenon
                    <10>2. bucket[q] # addr /\ bucket[q] = bucket'[q]
                      BY <10>1, Zenon
                    <10>3. MemLocs'[bucket'[q]] = MemLocs[bucket[q]]
                      BY Zenon, <5>A, <10>2
                    <10>4. \A index \in 1..Len(MemLocs[bucket[q]]) : MemLocs[bucket[q]][index].key # k
                      BY Zenon, <10>3 DEF KeyInBktAtAddr
                    <10>5. MemLocs[bucket[q]] \in Seq([key: KeyDomain, val: ValDomain])
                      BY Zenon
                    <10>6. arg[q] \in [key: KeyDomain, val: ValDomain]
                      BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
                    <10>7. bkt_arr[Len(bkt_arr)].key # k
                      BY <8>1, <10>5, <10>6, AppendProperties, Isa
                    <10>8. /\ \A index \in 1..Len(MemLocs[bucket[q]]) : bkt_arr[index] = MemLocs[bucket[q]][index]
                           /\ Len(MemLocs[bucket[q]]) \in Nat
                           /\ Len(bkt_arr) = Len(MemLocs[bucket[q]])+1
                      BY <10>5, <10>6, AppendProperties, LenProperties
                    <10> QED
                      BY <10>4, <10>7, <10>8 DEF KeyInBktAtAddr
                  <9> QED
                    BY <9>1, <9>2, Zenon DEF KeyInBktAtAddr
                <8> QED
                  BY <8>2, <8>3, <8>4
              <7> QED
                BY <7>1, <7>2
            <6>2. CASE q # p
              <7> USE <6>2
              <7>1. /\ KeyInBktAtAddr(arg[q].key, newbkt[q])
                    /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q]) = arg[q].val
                    /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                              /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                                 (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
                BY Zenon DEF NewBktOK
              <7>2. arg[q].key \in KeyDomain
                BY RemDef, Zenon DEF ArgsOf, LineIDtoOp
              <7> QED
                BY <5>B, <7>1, <7>2, ZenonT(30)
            <6> QED
              BY <6>1, <6>2
          <5>2. CASE pc'[q] = "U4"
            <6> USE <5>2
            <6>1. /\ KeyInBktAtAddr(arg[q].key, newbkt[q])
                  /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q]) = arg[q].val
                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                            /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                               (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
              BY Zenon DEF NewBktOK
            <6>2. arg[q].key \in KeyDomain
              BY RemDef, Zenon DEF ArgsOf, LineIDtoOp
            <6> QED
              BY <5>B, <6>1, <6>2, ZenonT(30)
          <5>3. CASE pc'[q] = "R4"
            <6> USE <5>3
            <6>1. /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])
                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                            /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                               (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
              BY Zenon DEF NewBktOK
            <6>2. arg[q].key \in KeyDomain
              BY RemDef, Zenon DEF ArgsOf, LineIDtoOp
            <6> QED
              BY <5>B, <6>1, <6>2, ZenonT(30)
          <5> QED
            BY <5>1, <5>2, <5>3
        <4> QED
          BY <4>1, <4>10, <4>11, <4>12, <4>13, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, <4>14, <4>15 DEF Inv
      <3>6. CASE Line = I4(p)
        <4> USE <3>6 DEF I4
        <4>1. PTypeOK'
          BY NextPTypeOK
        <4>2. (pc \in [ProcSet -> LineIDs])'
          BY Isa DEF LineIDs
        <4>3. (A \in [1..N -> AllocAddrs \union {NULL}])'
          <5>1. CASE A[Hash[arg[p].key]] = bucket[p]
            <6> SUFFICES newbkt[p] \in AllocAddrs \union {NULL}
              BY <5>1, Isa
            <6> QED
              OBVIOUS
          <5>2. CASE A[Hash[arg[p].key]] # bucket[p] 
            BY <5>2
          <5> QED
            BY <5>1, <5>2
        <4>4. (MemLocs \in [Addrs -> Seq([key: KeyDomain, val: ValDomain])])'
          OBVIOUS
        <4>5. (AllocAddrs \in SUBSET Addrs)'
          OBVIOUS
        <4>6. (bucket \in [ProcSet -> AllocAddrs \union {NULL}])'
          OBVIOUS
        <4>7. (newbkt \in [ProcSet -> AllocAddrs \union {NULL}])'
          OBVIOUS
        <4>8. (r \in [ProcSet -> ValDomain \union {NULL}])'
          OBVIOUS
        <4>9. (arg \in [ProcSet -> ArgDomain])'
          OBVIOUS
        <4>10. (ret \in [ProcSet -> RetDomain])'
          OBVIOUS
        <4>11. (\A p_1 \in ProcSet : (pc[p_1] # RemainderID) => arg[p_1] \in ArgsOf(LineIDtoOp(pc[p_1])))'
          <5> SUFFICES arg[p] \in ArgsOf(LineIDtoOp(pc'[p]))
            BY Zenon
          <5> QED
            BY RemDef, ZenonT(30) DEF LineIDtoOp, ArgsOf
        <4>12. AddrsOK'
          <5> SUFFICES ASSUME NEW p_1 \in ProcSet',
                              (pc[p_1] \in {"I4", "U4", "R4"})'
                       PROVE  (/\ \A q \in ProcSet : (p_1 # q => /\ newbkt[p_1] # bucket[q]
                                                                 /\ newbkt[p_1] # newbkt[q])
                               /\ \A idx \in 1..N  : (A[idx] # newbkt[p_1])
                               /\ newbkt[p_1] # bucket[p_1]
                               /\ newbkt[p_1] \in AllocAddrs)'
            BY DEF AddrsOK
          <5>1. (\A q \in ProcSet : (p_1 # q => /\ newbkt[p_1] # bucket[q]
                                                /\ newbkt[p_1] # newbkt[q]))'
            BY DEF AddrsOK
          <5>2. (\A idx \in 1..N  : (A[idx] # newbkt[p_1]))'
            BY DEF AddrsOK
          <5>3. (newbkt[p_1] # bucket[p_1])'
            BY DEF AddrsOK
          <5>4. (newbkt[p_1] \in AllocAddrs)'
            BY DEF AddrsOK
          <5>5. QED
            BY <5>1, <5>2, <5>3, <5>4
        <4>13. BktOK'
          <5> SUFFICES ASSUME NEW q \in ProcSet
                       PROVE  (/\ pc'[q] \in {"I3", "I4"} => (/\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                                                              /\ r'[q] = NULL)
                               /\ pc'[q] \in {"U3", "U4"} => (IF KeyInBktAtAddr(arg[q].key, bucket[q])'
                                                                  THEN (/\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                                                                        /\ r'[q] # NULL)
                                                                  ELSE r'[q] = NULL)
                               /\ pc'[q] \in {"R3", "R4"} => (/\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                                                              /\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                                                              /\ r'[q] # NULL))
            BY DEF BktOK
          <5>1. CASE pc'[q] \in {"I3", "I4"}
            <6> USE <5>1
            <6> SUFFICES ~KeyInBktAtAddr(arg[q].key, bucket[q])' /\ r'[q] = NULL
              OBVIOUS
            <6>1. ~KeyInBktAtAddr(arg[q].key, bucket[q]) /\ r[q] = NULL
              BY Zenon DEF BktOK
            <6> QED
              BY <6>1, Zenon DEF KeyInBktAtAddr
          <5>2. CASE pc'[q] \in {"U3", "U4"}
            <6> USE <5>2
            <6> SUFFICES IF KeyInBktAtAddr(arg[q].key, bucket[q])'
                            THEN (/\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                                  /\ r'[q] # NULL)
                            ELSE r'[q] = NULL
              OBVIOUS
            <6>1. IF KeyInBktAtAddr(arg[q].key, bucket[q])
                     THEN (/\ r[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                           /\ r[q] # NULL)
                     ELSE r[q] = NULL
              BY Zenon DEF BktOK
            <6>2. KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
              BY Zenon DEF KeyInBktAtAddr
            <6>3. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs'[bucket'[q]][CHOOSE index \in 1..Len(MemLocs'[bucket'[q]]) :
                                   MemLocs'[bucket'[q]][index].key = arg'[q].key].val
              BY DEF ValOfKeyInBktAtAddr
            <6>4. MemLocs = MemLocs' /\ arg = arg' /\ bucket[q] = bucket'[q]
              BY Zenon
            <6>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs[bucket'[q]][CHOOSE index \in 1..Len(MemLocs[bucket'[q]]) :
                                  MemLocs[bucket'[q]][index].key = arg[q].key].val
              BY Zenon, <6>3, <6>4
            <6>6. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs[bucket[q]][CHOOSE index \in 1..Len(MemLocs[bucket[q]]) :
                                 MemLocs[bucket[q]][index].key = arg[q].key].val
              BY <6>4, <6>5
            <6>7. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
              BY <6>6, Zenon DEF ValOfKeyInBktAtAddr
            <6> QED
              BY <6>1, <6>2, <6>7, Zenon
          <5>3. CASE pc'[q] \in {"R3", "R4"}
            <6> USE <5>3
            <6> SUFFICES /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                         /\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                         /\ r'[q] # NULL
              OBVIOUS
            <6>1. /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                  /\ r[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                  /\ r[q] # NULL
              BY Zenon DEF BktOK
            <6>2. KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
              BY Zenon DEF KeyInBktAtAddr
            <6>3. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs'[bucket'[q]][CHOOSE index \in 1..Len(MemLocs'[bucket'[q]]) :
                                   MemLocs'[bucket'[q]][index].key = arg'[q].key].val
              BY DEF ValOfKeyInBktAtAddr
            <6>4. MemLocs = MemLocs' /\ arg = arg' /\ bucket[q] = bucket'[q]
              BY Zenon
            <6>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs[bucket'[q]][CHOOSE index \in 1..Len(MemLocs[bucket'[q]]) :
                                  MemLocs[bucket'[q]][index].key = arg[q].key].val
              BY Zenon, <6>3, <6>4
            <6>6. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs[bucket[q]][CHOOSE index \in 1..Len(MemLocs[bucket[q]]) :
                                 MemLocs[bucket[q]][index].key = arg[q].key].val
              BY <6>4, <6>5
            <6>7. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
              BY <6>6, Zenon DEF ValOfKeyInBktAtAddr
            <6> QED
              BY <6>1, <6>2, <6>7, Zenon
          <5> QED
            BY <5>1, <5>2, <5>3
        <4>14. Uniq'
          <5> SUFFICES ASSUME NEW addr \in AllocAddrs', 
                              NEW bucket_arr, bucket_arr = MemLocs'[addr],
                              NEW j1 \in 1..Len(bucket_arr),
                              NEW j2 \in 1..Len(bucket_arr),
                              bucket_arr[j1].key = bucket_arr[j2].key
                       PROVE  j1 = j2
            BY Zenon DEF Uniq
          <5> QED
            BY Zenon DEF Uniq
        <4>15. NewBktOK'
          <5> SUFFICES ASSUME NEW q \in ProcSet
                       PROVE  /\ pc'[q] = "I4" => /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                                  /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                                                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                            /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                               (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
                              /\ pc'[q] = "U4" => /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                                  /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                                                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                            /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                               (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
                              /\ pc'[q] = "R4" => /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                            /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                               (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
            BY ZenonT(60) DEF NewBktOK
          <5>0. ASSUME NEW k \in KeyDomain
                PROVE  /\ pc[q] \in {"I4", "U4", "R4"} => KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, bucket[q])'
                       /\ KeyInBktAtAddr(k, newbkt[q]) = KeyInBktAtAddr(k, newbkt[q])'
                       /\ pc[q] \in {"I4", "U4", "R4"} => ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])'
                       /\ ValOfKeyInBktAtAddr(k, newbkt[q]) = ValOfKeyInBktAtAddr(k, newbkt[q])'
            <6> USE <5>0
            <6>1. pc[q] \in {"I4", "U4", "R4"} => KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, bucket[q])'
              BY Zenon DEF KeyInBktAtAddr
            <6>2. KeyInBktAtAddr(k, newbkt[q]) = KeyInBktAtAddr(k, newbkt[q])'
              BY Zenon DEF KeyInBktAtAddr
            <6>3. pc[q] \in {"I4", "U4", "R4"} => ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])'
              <7> SUFFICES ASSUME pc[q] \in {"I4", "U4", "R4"}
                           PROVE  ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])'
                OBVIOUS
              <7> DEFINE bkt_arr == MemLocs'[bucket'[q]]
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
              <7>1. ValOfKeyInBktAtAddr(k, bucket[q])' = bkt_arr[idx].val
                BY Zenon DEF ValOfKeyInBktAtAddr
              <7>2. bkt_arr = MemLocs[bucket[q]]
                BY Zenon
              <7>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
                BY Zenon
              <7> QED
                BY <7>1, <7>2, <7>3, Isa DEF ValOfKeyInBktAtAddr
            <6>4. ValOfKeyInBktAtAddr(k, newbkt[q]) = ValOfKeyInBktAtAddr(k, newbkt[q])'
              <7> DEFINE bkt_arr == MemLocs'[newbkt'[q]]
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
              <7>1. ValOfKeyInBktAtAddr(k, newbkt[q])' = bkt_arr[idx].val
                BY Zenon DEF ValOfKeyInBktAtAddr
              <7>2. bkt_arr = MemLocs[newbkt[q]]
                BY Zenon
              <7>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
                BY Zenon
              <7> QED
                BY <7>1, <7>2, <7>3, Isa DEF ValOfKeyInBktAtAddr
            <6> QED
              BY <6>1, <6>2, <6>3, <6>4
          <5>1. CASE pc'[q] = "I4"
            <6> USE <5>1
            <6> SUFFICES /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                         /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                         /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                   /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                      (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
              OBVIOUS
            <6>1. pc[q] = "I4" /\ arg[q].key \in KeyDomain
              BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
            <6>2. /\ KeyInBktAtAddr(arg[q].key, newbkt[q])
                  /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q]) = arg[q].val
                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                            /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                               (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
              BY <6>1, Zenon DEF NewBktOK
            <6> QED
              BY <5>0, <6>1, <6>2, ZenonT(30)
          <5>2. CASE pc'[q] = "U4"
            <6> USE <5>2
            <6> SUFFICES /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                         /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                         /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                   /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                      (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
              OBVIOUS
            <6>1. pc[q] = "U4" /\ arg[q].key \in KeyDomain
              BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
            <6>2. /\ KeyInBktAtAddr(arg[q].key, newbkt[q])
                  /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q]) = arg[q].val
                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                            /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                               (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
              BY <6>1, Zenon DEF NewBktOK
            <6> QED
              BY <5>0, <6>1, <6>2, ZenonT(30)
          <5>3. CASE pc'[q] = "R4"
            <6> USE <5>3
            <6> SUFFICES /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])'
                         /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                   /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                      (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
              OBVIOUS
            <6>1. pc[q] = "R4" /\ arg[q].key \in KeyDomain
              BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
            <6>2. /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])
                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                            /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                               (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
              BY <6>1, Zenon DEF NewBktOK
            <6> QED
              BY <5>0, <6>1, <6>2, ZenonT(30)
          <5> QED
            BY <5>1, <5>2, <5>3
        <4> QED
          BY <4>1, <4>10, <4>11, <4>12, <4>13, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, <4>14, <4>15 DEF Inv
      <3>7. CASE Line = U1(p)
        <4> USE <3>7 DEF U1
        <4>1. PTypeOK'
          BY NextPTypeOK
        <4>2. (pc \in [ProcSet -> LineIDs])'
          BY Isa DEF LineIDs
        <4>3. (A \in [1..N -> AllocAddrs \union {NULL}])'
          OBVIOUS
        <4>4. (MemLocs \in [Addrs -> Seq([key: KeyDomain, val: ValDomain])])'
          OBVIOUS
        <4>5. (AllocAddrs \in SUBSET Addrs)'
          OBVIOUS
        <4>6. (bucket \in [ProcSet -> AllocAddrs \union {NULL}])'
          <5>1. arg[p].key \in KeyDomain
            BY RemDef, Zenon DEF LineIDtoOp, ArgsOf
          <5> QED
            BY <5>1, HashDef, Zenon
        <4>7. (newbkt \in [ProcSet -> AllocAddrs \union {NULL}])'
          OBVIOUS
        <4>8. (r \in [ProcSet -> ValDomain \union {NULL}])'
          OBVIOUS
        <4>9. (arg \in [ProcSet -> ArgDomain])'
          OBVIOUS
        <4>10. (ret \in [ProcSet -> RetDomain])'
          OBVIOUS
        <4>11. (\A p_1 \in ProcSet : (pc[p_1] # RemainderID) => arg[p_1] \in ArgsOf(LineIDtoOp(pc[p_1])))'
          <5> SUFFICES arg[p] \in ArgsOf(LineIDtoOp(pc'[p]))
            BY Zenon
          <5> QED
            BY RemDef, ZenonT(30) DEF LineIDtoOp, ArgsOf
        <4>12. AddrsOK'
          <5> SUFFICES ASSUME NEW p_1 \in ProcSet',
                              (pc[p_1] \in {"I4", "U4", "R4"})'
                       PROVE  (/\ \A q \in ProcSet : (p_1 # q => /\ newbkt[p_1] # bucket[q]
                                                                 /\ newbkt[p_1] # newbkt[q])
                               /\ \A idx \in 1..N  : (A[idx] # newbkt[p_1])
                               /\ newbkt[p_1] # bucket[p_1]
                               /\ newbkt[p_1] \in AllocAddrs)'
            BY DEF AddrsOK
          <5>1. (\A q \in ProcSet : (p_1 # q => /\ newbkt[p_1] # bucket[q]
                                                /\ newbkt[p_1] # newbkt[q]))'
            <6> SUFFICES ASSUME NEW q \in ProcSet,
                                p_1 # q
                         PROVE  newbkt[p_1] # bucket'[q]
              BY ZenonT(30) DEF AddrsOK
            <6>1. CASE p = q
              <7>1. arg[p] \in [key: KeyDomain, val: ValDomain]
                BY RemDef, Zenon DEF ArgsOf, LineIDtoOp
              <7>2. Hash[arg[p].key] \in 1..N
                BY <7>1, HashDef
              <7>3. A[Hash[arg[p].key]] # newbkt[p_1]
                BY <7>2, Zenon DEF AddrsOK
              <7>4. bucket'[q] # newbkt[p_1]
                BY <6>1, <7>3, Zenon
              <7> QED
                BY <7>4
            <6>2. CASE p # q
              BY <6>2, Zenon DEF AddrsOK
            <6> QED
              BY <6>1, <6>2
          <5>2. (\A idx \in 1..N  : (A[idx] # newbkt[p_1]))'
            BY DEF AddrsOK
          <5>3. (newbkt[p_1] # bucket[p_1])'
            BY DEF AddrsOK
          <5>4. (newbkt[p_1] \in AllocAddrs)'
            BY DEF AddrsOK
          <5>5. QED
            BY <5>1, <5>2, <5>3, <5>4
        <4>13. BktOK'
          <5> SUFFICES ASSUME NEW q \in ProcSet
                       PROVE  (/\ pc'[q] \in {"I3", "I4"} => (/\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                                                              /\ r'[q] = NULL)
                               /\ pc'[q] \in {"U3", "U4"} => (IF KeyInBktAtAddr(arg[q].key, bucket[q])'
                                                                  THEN (/\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                                                                        /\ r'[q] # NULL)
                                                                  ELSE r'[q] = NULL)
                               /\ pc'[q] \in {"R3", "R4"} => (/\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                                                              /\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                                                              /\ r'[q] # NULL))
            BY DEF BktOK
          <5>1. CASE pc'[q] \in {"I3", "I4"}
            <6> USE <5>1
            <6> SUFFICES ~KeyInBktAtAddr(arg[q].key, bucket[q])' /\ r'[q] = NULL
              OBVIOUS
            <6>1. ~KeyInBktAtAddr(arg[q].key, bucket[q]) /\ r[q] = NULL
              BY Zenon DEF BktOK
            <6> QED
              BY <6>1, Zenon DEF KeyInBktAtAddr
          <5>2. CASE pc'[q] \in {"U3", "U4"}
            <6> USE <5>2
            <6> SUFFICES IF KeyInBktAtAddr(arg[q].key, bucket[q])'
                            THEN (/\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                                  /\ r'[q] # NULL)
                            ELSE r'[q] = NULL
              OBVIOUS
            <6>1. IF KeyInBktAtAddr(arg[q].key, bucket[q])
                     THEN (/\ r[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                           /\ r[q] # NULL)
                     ELSE r[q] = NULL
              BY Zenon DEF BktOK
            <6>2. KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
              BY Zenon DEF KeyInBktAtAddr
            <6>3. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs'[bucket'[q]][CHOOSE index \in 1..Len(MemLocs'[bucket'[q]]) :
                                   MemLocs'[bucket'[q]][index].key = arg'[q].key].val
              BY DEF ValOfKeyInBktAtAddr
            <6>4. MemLocs = MemLocs' /\ arg = arg' /\ bucket[q] = bucket'[q]
              BY Zenon
            <6>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs[bucket'[q]][CHOOSE index \in 1..Len(MemLocs[bucket'[q]]) :
                                  MemLocs[bucket'[q]][index].key = arg[q].key].val
              BY Zenon, <6>3, <6>4
            <6>6. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs[bucket[q]][CHOOSE index \in 1..Len(MemLocs[bucket[q]]) :
                                 MemLocs[bucket[q]][index].key = arg[q].key].val
              BY <6>4, <6>5
            <6>7. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
              BY <6>6, Zenon DEF ValOfKeyInBktAtAddr
            <6> QED
              BY <6>1, <6>2, <6>7, Zenon
          <5>3. CASE pc'[q] \in {"R3", "R4"}
            <6> USE <5>3
            <6> SUFFICES /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                         /\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                         /\ r'[q] # NULL
              OBVIOUS
            <6>1. /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                  /\ r[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                  /\ r[q] # NULL
              BY Zenon DEF BktOK
            <6>2. KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
              BY Zenon DEF KeyInBktAtAddr
            <6>3. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs'[bucket'[q]][CHOOSE index \in 1..Len(MemLocs'[bucket'[q]]) :
                                   MemLocs'[bucket'[q]][index].key = arg'[q].key].val
              BY DEF ValOfKeyInBktAtAddr
            <6>4. MemLocs = MemLocs' /\ arg = arg' /\ bucket[q] = bucket'[q]
              BY Zenon
            <6>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs[bucket'[q]][CHOOSE index \in 1..Len(MemLocs[bucket'[q]]) :
                                  MemLocs[bucket'[q]][index].key = arg[q].key].val
              BY Zenon, <6>3, <6>4
            <6>6. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs[bucket[q]][CHOOSE index \in 1..Len(MemLocs[bucket[q]]) :
                                 MemLocs[bucket[q]][index].key = arg[q].key].val
              BY <6>4, <6>5
            <6>7. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
              BY <6>6, Zenon DEF ValOfKeyInBktAtAddr
            <6> QED
              BY <6>1, <6>2, <6>7, Zenon
          <5> QED
            BY <5>1, <5>2, <5>3
        <4>14. Uniq'
          <5> SUFFICES ASSUME NEW addr \in AllocAddrs', 
                              NEW bucket_arr, bucket_arr = MemLocs'[addr],
                              NEW j1 \in 1..Len(bucket_arr),
                              NEW j2 \in 1..Len(bucket_arr),
                              bucket_arr[j1].key = bucket_arr[j2].key
                       PROVE  j1 = j2
            BY Zenon DEF Uniq
          <5> QED
            BY Zenon DEF Uniq
        <4>15. NewBktOK'
          <5> SUFFICES ASSUME NEW q \in ProcSet
                       PROVE  /\ pc'[q] = "I4" => /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                                  /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                                                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                            /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                               (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
                              /\ pc'[q] = "U4" => /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                                  /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                                                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                            /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                               (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
                              /\ pc'[q] = "R4" => /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                            /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                               (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
            BY ZenonT(60) DEF NewBktOK
          <5>0. ASSUME NEW k \in KeyDomain
                PROVE  /\ pc[q] \in {"I4", "U4", "R4"} => KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, bucket[q])'
                       /\ KeyInBktAtAddr(k, newbkt[q]) = KeyInBktAtAddr(k, newbkt[q])'
                       /\ pc[q] \in {"I4", "U4", "R4"} => ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])'
                       /\ ValOfKeyInBktAtAddr(k, newbkt[q]) = ValOfKeyInBktAtAddr(k, newbkt[q])'
            <6> USE <5>0
            <6>1. pc[q] \in {"I4", "U4", "R4"} => KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, bucket[q])'
              BY Zenon DEF KeyInBktAtAddr
            <6>2. KeyInBktAtAddr(k, newbkt[q]) = KeyInBktAtAddr(k, newbkt[q])'
              BY Zenon DEF KeyInBktAtAddr
            <6>3. pc[q] \in {"I4", "U4", "R4"} => ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])'
              <7> SUFFICES ASSUME pc[q] \in {"I4", "U4", "R4"}
                           PROVE  ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])'
                OBVIOUS
              <7> DEFINE bkt_arr == MemLocs'[bucket'[q]]
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
              <7>1. ValOfKeyInBktAtAddr(k, bucket[q])' = bkt_arr[idx].val
                BY Zenon DEF ValOfKeyInBktAtAddr
              <7>2. bkt_arr = MemLocs[bucket[q]]
                BY Zenon
              <7>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
                BY Zenon
              <7> QED
                BY <7>1, <7>2, <7>3, Isa DEF ValOfKeyInBktAtAddr
            <6>4. ValOfKeyInBktAtAddr(k, newbkt[q]) = ValOfKeyInBktAtAddr(k, newbkt[q])'
              <7> DEFINE bkt_arr == MemLocs'[newbkt'[q]]
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
              <7>1. ValOfKeyInBktAtAddr(k, newbkt[q])' = bkt_arr[idx].val
                BY Zenon DEF ValOfKeyInBktAtAddr
              <7>2. bkt_arr = MemLocs[newbkt[q]]
                BY Zenon
              <7>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
                BY Zenon
              <7> QED
                BY <7>1, <7>2, <7>3, Isa DEF ValOfKeyInBktAtAddr
            <6> QED
              BY <6>1, <6>2, <6>3, <6>4
          <5>1. CASE pc'[q] = "I4"
            <6> USE <5>1
            <6> SUFFICES /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                         /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                         /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                   /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                      (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
              OBVIOUS
            <6>1. pc[q] = "I4" /\ arg[q].key \in KeyDomain
              BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
            <6>2. /\ KeyInBktAtAddr(arg[q].key, newbkt[q])
                  /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q]) = arg[q].val
                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                            /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                               (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
              BY <6>1, Zenon DEF NewBktOK
            <6> QED
              BY <5>0, <6>1, <6>2, ZenonT(30)
          <5>2. CASE pc'[q] = "U4"
            <6> USE <5>2
            <6> SUFFICES /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                         /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                         /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                   /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                      (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
              OBVIOUS
            <6>1. pc[q] = "U4" /\ arg[q].key \in KeyDomain
              BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
            <6>2. /\ KeyInBktAtAddr(arg[q].key, newbkt[q])
                  /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q]) = arg[q].val
                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                            /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                               (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
              BY <6>1, Zenon DEF NewBktOK
            <6> QED
              BY <5>0, <6>1, <6>2, ZenonT(30)
          <5>3. CASE pc'[q] = "R4"
            <6> USE <5>3
            <6> SUFFICES /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])'
                         /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                   /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                      (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
              OBVIOUS
            <6>1. pc[q] = "R4" /\ arg[q].key \in KeyDomain
              BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
            <6>2. /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])
                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                            /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                               (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
              BY <6>1, Zenon DEF NewBktOK
            <6> QED
              BY <5>0, <6>1, <6>2, ZenonT(30)
          <5> QED
            BY <5>1, <5>2, <5>3
        <4> QED
          BY <4>1, <4>10, <4>11, <4>12, <4>13, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, <4>14, <4>15 DEF Inv
      <3>8. CASE Line = U2(p)
        <4> USE <3>8 DEF U2
        <4>1. PTypeOK'
          BY NextPTypeOK
        <4>2. (pc \in [ProcSet -> LineIDs])'
          BY Isa DEF LineIDs
        <4>3. (A \in [1..N -> AllocAddrs \union {NULL}])'
          OBVIOUS
        <4>4. (MemLocs \in [Addrs -> Seq([key: KeyDomain, val: ValDomain])])'
          OBVIOUS
        <4>5. (AllocAddrs \in SUBSET Addrs)'
          OBVIOUS
        <4>6. (bucket \in [ProcSet -> AllocAddrs \union {NULL}])'
          OBVIOUS
        <4>7. (newbkt \in [ProcSet -> AllocAddrs \union {NULL}])'
          OBVIOUS
        <4>8. (r \in [ProcSet -> ValDomain \union {NULL}])'
          <5>1. CASE bucket[p] # NULL /\ KeyInBktAtAddr(arg[p].key, bucket[p])
            <6>1. r' = [r EXCEPT ![p] = ValOfKeyInBktAtAddr(arg[p].key, bucket[p])]
              BY <5>1, Zenon
            <6>2. ValOfKeyInBktAtAddr(arg[p].key, bucket[p]) = MemLocs[bucket[p]][CHOOSE index \in 1..Len(MemLocs[bucket[p]]) : MemLocs[bucket[p]][index].key = arg[p].key].val
              BY Zenon DEF ValOfKeyInBktAtAddr
            <6>3. \E index \in 1..Len(MemLocs[bucket[p]]) : MemLocs[bucket[p]][index].key = arg[p].key
              BY <5>1, Zenon DEF KeyInBktAtAddr
            <6>4. PICK index \in 1..Len(MemLocs[bucket[p]]) : /\ MemLocs[bucket[p]][index].key = arg[p].key
                                                              /\ ValOfKeyInBktAtAddr(arg[p].key, bucket[p]) = MemLocs[bucket[p]][index].val
              BY <6>2, <6>3, Zenon
            <6>5. MemLocs[bucket[p]] \in Seq([key: KeyDomain, val: ValDomain])
              BY <5>1
            <6>6. MemLocs[bucket[p]][index] \in [key: KeyDomain, val: ValDomain]
              BY <6>4, <6>5, ElementOfSeq, Zenon
            <6>7. MemLocs[bucket[p]][index].val \in ValDomain
              BY <6>6
            <6> QED
              BY <6>1, <6>4, <6>7, Zenon
          <5>2. CASE bucket[p] = NULL \/ ~KeyInBktAtAddr(arg[p].key, bucket[p])
            BY <5>2, Zenon DEF KeyInBktAtAddr
          <5> QED
            BY <5>1, <5>2
        <4>9. (arg \in [ProcSet -> ArgDomain])'
          OBVIOUS
        <4>10. (ret \in [ProcSet -> RetDomain])'
          OBVIOUS
        <4>11. (\A p_1 \in ProcSet : (pc[p_1] # RemainderID) => arg[p_1] \in ArgsOf(LineIDtoOp(pc[p_1])))'
          <5> SUFFICES arg[p] \in ArgsOf(LineIDtoOp(pc'[p]))
            BY Zenon
          <5> QED
            BY RemDef, ZenonT(30) DEF LineIDtoOp, ArgsOf
        <4>12. AddrsOK'
          <5> SUFFICES ASSUME NEW p_1 \in ProcSet',
                              (pc[p_1] \in {"I4", "U4", "R4"})'
                       PROVE  (/\ \A q \in ProcSet : (p_1 # q => /\ newbkt[p_1] # bucket[q]
                                                                 /\ newbkt[p_1] # newbkt[q])
                               /\ \A idx \in 1..N  : (A[idx] # newbkt[p_1])
                               /\ newbkt[p_1] # bucket[p_1]
                               /\ newbkt[p_1] \in AllocAddrs)'
            BY DEF AddrsOK
          <5>1. (\A q \in ProcSet : (p_1 # q => /\ newbkt[p_1] # bucket[q]
                                                /\ newbkt[p_1] # newbkt[q]))'
            BY DEF AddrsOK
          <5>2. (\A idx \in 1..N  : (A[idx] # newbkt[p_1]))'
            BY DEF AddrsOK
          <5>3. (newbkt[p_1] # bucket[p_1])'
            BY DEF AddrsOK
          <5>4. (newbkt[p_1] \in AllocAddrs)'
            BY DEF AddrsOK
          <5>5. QED
            BY <5>1, <5>2, <5>3, <5>4
        <4>13. BktOK'
          <5> SUFFICES ASSUME NEW q \in ProcSet
                       PROVE  (/\ pc'[q] \in {"I3", "I4"} => (/\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                                                              /\ r'[q] = NULL)
                               /\ pc'[q] \in {"U3", "U4"} => (IF KeyInBktAtAddr(arg[q].key, bucket[q])'
                                                                  THEN (/\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                                                                        /\ r'[q] # NULL)
                                                                  ELSE r'[q] = NULL)
                               /\ pc'[q] \in {"R3", "R4"} => (/\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                                                              /\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                                                              /\ r'[q] # NULL))
            BY DEF BktOK
          <5>1. CASE pc'[q] \in {"I3", "I4"}
            <6> USE <5>1
            <6> SUFFICES ~KeyInBktAtAddr(arg[q].key, bucket[q])' /\ r'[q] = NULL
              OBVIOUS
            <6>1. ~KeyInBktAtAddr(arg[q].key, bucket[q]) /\ r[q] = NULL
              BY Zenon DEF BktOK
            <6> QED
              BY <6>1, Zenon DEF KeyInBktAtAddr
          <5>2. CASE pc'[q] \in {"U3", "U4"}
            <6> USE <5>2
            <6> SUFFICES IF KeyInBktAtAddr(arg[q].key, bucket[q])'
                            THEN (/\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                                  /\ r'[q] # NULL)
                            ELSE r'[q] = NULL
              OBVIOUS
            <6>1. CASE p = q
              <7> USE <6>1
              <7>1. CASE KeyInBktAtAddr(arg[p].key, bucket[p])
                <8>1. KeyInBktAtAddr(arg[p].key, bucket[p])'
                  BY <7>1, Zenon DEF KeyInBktAtAddr
                <8>2. r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                  BY <7>1, Zenon
                <8>3. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
                  MemLocs'[bucket'[q]][CHOOSE index \in 1..Len(MemLocs'[bucket'[q]]) :
                                       MemLocs'[bucket'[q]][index].key = arg'[q].key].val
                  BY DEF ValOfKeyInBktAtAddr
                <8>4. MemLocs = MemLocs' /\ arg = arg' /\ bucket[q] = bucket'[q]
                  BY Zenon
                <8>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
                  MemLocs[bucket'[q]][CHOOSE index \in 1..Len(MemLocs[bucket'[q]]) :
                                      MemLocs[bucket'[q]][index].key = arg[q].key].val
                  BY Zenon, <8>3, <8>4
                <8>6. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
                  MemLocs[bucket[q]][CHOOSE index \in 1..Len(MemLocs[bucket[q]]) :
                                     MemLocs[bucket[q]][index].key = arg[q].key].val
                  BY <8>4, <8>5
                <8>7. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                  BY <8>6, Zenon DEF ValOfKeyInBktAtAddr
                <8>8. \E index \in 1..Len(MemLocs[bucket[p]]) : MemLocs[bucket[p]][index].key = arg[p].key
                  BY <7>1, Zenon DEF KeyInBktAtAddr
                <8>9. ValOfKeyInBktAtAddr(arg[p].key, bucket[p]) = MemLocs[bucket[p]][CHOOSE index \in 1..Len(MemLocs[bucket[p]]) : MemLocs[bucket[p]][index].key = arg[p].key].val
                  BY Zenon DEF ValOfKeyInBktAtAddr
                <8>10. PICK index \in 1..Len(MemLocs[bucket[p]]) : /\ MemLocs[bucket[p]][index].key = arg[p].key
                                                                   /\ ValOfKeyInBktAtAddr(arg[p].key, bucket[p]) = MemLocs[bucket[p]][index].val
                  BY <8>8, <8>9, Zenon
                <8>11. MemLocs[bucket[p]] \in Seq([key: KeyDomain, val: ValDomain])
                  BY <7>1, Zenon DEF KeyInBktAtAddr
                <8>12. MemLocs[bucket[p]][index] \in [key: KeyDomain, val: ValDomain]
                  BY <8>10, <8>11, ElementOfSeq, Zenon
                <8>13. MemLocs[bucket[p]][index].val \in ValDomain
                  BY <8>12
                <8> QED 
                  BY <8>1, <8>2, <8>7, <8>10, <8>13, NULLDef, Zenon
              <7>2. CASE ~KeyInBktAtAddr(arg[p].key, bucket[p])
                <8>1. ~KeyInBktAtAddr(arg[p].key, bucket[p])'
                  BY <7>2, Zenon DEF KeyInBktAtAddr
                <8>2. r'[q] = NULL
                  BY <7>2, Zenon
                <8> QED
                  BY <8>1, <8>2  
              <7> QED
                BY <7>1, <7>2
            <6> SUFFICES ASSUME p # q
                         PROVE  IF KeyInBktAtAddr(arg[q].key, bucket[q])'
                                THEN (/\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                                      /\ r'[q] # NULL)
                                ELSE r'[q] = NULL
              BY <6>1
            <6>2. IF KeyInBktAtAddr(arg[q].key, bucket[q])
                     THEN (/\ r[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                           /\ r[q] # NULL)
                     ELSE r[q] = NULL
              BY Zenon DEF BktOK
            <6>3. KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
              BY Zenon DEF KeyInBktAtAddr
            <6>4. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs'[bucket'[q]][CHOOSE index \in 1..Len(MemLocs'[bucket'[q]]) :
                                   MemLocs'[bucket'[q]][index].key = arg'[q].key].val
              BY DEF ValOfKeyInBktAtAddr
            <6>5. MemLocs = MemLocs' /\ arg = arg' /\ bucket[q] = bucket'[q]
              BY Zenon
            <6>6. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs[bucket'[q]][CHOOSE index \in 1..Len(MemLocs[bucket'[q]]) :
                                  MemLocs[bucket'[q]][index].key = arg[q].key].val
              BY Zenon, <6>4, <6>5
            <6>7. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs[bucket[q]][CHOOSE index \in 1..Len(MemLocs[bucket[q]]) :
                                 MemLocs[bucket[q]][index].key = arg[q].key].val
              BY <6>5, <6>6
            <6>8. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
              BY <6>7, Zenon DEF ValOfKeyInBktAtAddr
            <6> QED
              BY <6>2, <6>3, <6>8, Zenon
          <5>3. CASE pc'[q] \in {"R3", "R4"}
            <6> USE <5>3
            <6> SUFFICES /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                         /\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                         /\ r'[q] # NULL
              OBVIOUS
            <6>1. /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                  /\ r[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                  /\ r[q] # NULL
              BY Zenon DEF BktOK
            <6>2. KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
              BY Zenon DEF KeyInBktAtAddr
            <6>3. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs'[bucket'[q]][CHOOSE index \in 1..Len(MemLocs'[bucket'[q]]) :
                                   MemLocs'[bucket'[q]][index].key = arg'[q].key].val
              BY DEF ValOfKeyInBktAtAddr
            <6>4. MemLocs = MemLocs' /\ arg = arg' /\ bucket[q] = bucket'[q]
              BY Zenon
            <6>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs[bucket'[q]][CHOOSE index \in 1..Len(MemLocs[bucket'[q]]) :
                                  MemLocs[bucket'[q]][index].key = arg[q].key].val
              BY Zenon, <6>3, <6>4
            <6>6. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs[bucket[q]][CHOOSE index \in 1..Len(MemLocs[bucket[q]]) :
                                 MemLocs[bucket[q]][index].key = arg[q].key].val
              BY <6>4, <6>5
            <6>7. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
              BY <6>6, Zenon DEF ValOfKeyInBktAtAddr
            <6> QED
              BY <6>1, <6>2, <6>7, Zenon
          <5> QED
            BY <5>1, <5>2, <5>3
        <4>14. Uniq'
          <5> SUFFICES ASSUME NEW addr \in AllocAddrs', 
                              NEW bucket_arr, bucket_arr = MemLocs'[addr],
                              NEW j1 \in 1..Len(bucket_arr),
                              NEW j2 \in 1..Len(bucket_arr),
                              bucket_arr[j1].key = bucket_arr[j2].key
                       PROVE  j1 = j2
            BY Zenon DEF Uniq
          <5> QED
            BY Zenon DEF Uniq
        <4>15. NewBktOK'
          <5> SUFFICES ASSUME NEW q \in ProcSet
                       PROVE  /\ pc'[q] = "I4" => /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                                  /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                                                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                            /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                               (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
                              /\ pc'[q] = "U4" => /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                                  /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                                                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                            /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                               (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
                              /\ pc'[q] = "R4" => /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                            /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                               (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
            BY ZenonT(60) DEF NewBktOK
          <5>0. ASSUME NEW k \in KeyDomain
                PROVE  /\ pc[q] \in {"I4", "U4", "R4"} => KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, bucket[q])'
                       /\ KeyInBktAtAddr(k, newbkt[q]) = KeyInBktAtAddr(k, newbkt[q])'
                       /\ pc[q] \in {"I4", "U4", "R4"} => ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])'
                       /\ ValOfKeyInBktAtAddr(k, newbkt[q]) = ValOfKeyInBktAtAddr(k, newbkt[q])'
            <6> USE <5>0
            <6>1. pc[q] \in {"I4", "U4", "R4"} => KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, bucket[q])'
              BY Zenon DEF KeyInBktAtAddr
            <6>2. KeyInBktAtAddr(k, newbkt[q]) = KeyInBktAtAddr(k, newbkt[q])'
              BY Zenon DEF KeyInBktAtAddr
            <6>3. pc[q] \in {"I4", "U4", "R4"} => ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])'
              <7> SUFFICES ASSUME pc[q] \in {"I4", "U4", "R4"}
                           PROVE  ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])'
                OBVIOUS
              <7> DEFINE bkt_arr == MemLocs'[bucket'[q]]
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
              <7>1. ValOfKeyInBktAtAddr(k, bucket[q])' = bkt_arr[idx].val
                BY Zenon DEF ValOfKeyInBktAtAddr
              <7>2. bkt_arr = MemLocs[bucket[q]]
                BY Zenon
              <7>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
                BY Zenon
              <7> QED
                BY <7>1, <7>2, <7>3, Isa DEF ValOfKeyInBktAtAddr
            <6>4. ValOfKeyInBktAtAddr(k, newbkt[q]) = ValOfKeyInBktAtAddr(k, newbkt[q])'
              <7> DEFINE bkt_arr == MemLocs'[newbkt'[q]]
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
              <7>1. ValOfKeyInBktAtAddr(k, newbkt[q])' = bkt_arr[idx].val
                BY Zenon DEF ValOfKeyInBktAtAddr
              <7>2. bkt_arr = MemLocs[newbkt[q]]
                BY Zenon
              <7>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
                BY Zenon
              <7> QED
                BY <7>1, <7>2, <7>3, Isa DEF ValOfKeyInBktAtAddr
            <6> QED
              BY <6>1, <6>2, <6>3, <6>4
          <5>1. CASE pc'[q] = "I4"
            <6> USE <5>1
            <6> SUFFICES /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                         /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                         /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                   /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                      (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
              OBVIOUS
            <6>1. pc[q] = "I4" /\ arg[q].key \in KeyDomain
              BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
            <6>2. /\ KeyInBktAtAddr(arg[q].key, newbkt[q])
                  /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q]) = arg[q].val
                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                            /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                               (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
              BY <6>1, Zenon DEF NewBktOK
            <6> QED
              BY <5>0, <6>1, <6>2, ZenonT(30)
          <5>2. CASE pc'[q] = "U4"
            <6> USE <5>2
            <6> SUFFICES /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                         /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                         /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                   /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                      (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
              OBVIOUS
            <6>1. pc[q] = "U4" /\ arg[q].key \in KeyDomain
              BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
            <6>2. /\ KeyInBktAtAddr(arg[q].key, newbkt[q])
                  /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q]) = arg[q].val
                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                            /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                               (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
              BY <6>1, Zenon DEF NewBktOK
            <6> QED
              BY <5>0, <6>1, <6>2, ZenonT(30)
          <5>3. CASE pc'[q] = "R4"
            <6> USE <5>3
            <6> SUFFICES /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])'
                         /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                   /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                      (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
              OBVIOUS
            <6>1. pc[q] = "R4" /\ arg[q].key \in KeyDomain
              BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
            <6>2. /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])
                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                            /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                               (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
              BY <6>1, Zenon DEF NewBktOK
            <6> QED
              BY <5>0, <6>1, <6>2, ZenonT(30)
          <5> QED
            BY <5>1, <5>2, <5>3
        <4> QED
          BY <4>1, <4>10, <4>11, <4>12, <4>13, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, <4>14, <4>15 DEF Inv
      <3>9. CASE Line = U3(p)
        <4> USE <3>9 DEF U3
        <4>1. PTypeOK'
          BY NextPTypeOK
        <4>2. (pc \in [ProcSet -> LineIDs])'
          BY Isa DEF LineIDs
        <4>3. (A \in [1..N -> AllocAddrs \union {NULL}])'
          OBVIOUS
        <4>4. (MemLocs \in [Addrs -> Seq([key: KeyDomain, val: ValDomain])])'
          <5>0. PICK addr \in Addrs : 
            /\ addr \notin AllocAddrs
            /\ AllocAddrs' = AllocAddrs \cup {addr}
            /\ newbkt' = [newbkt EXCEPT ![p] = addr]
            /\ IF bucket[p] = NULL
                  THEN MemLocs' = [MemLocs EXCEPT ![addr] = <<arg[p]>>]
               ELSE
                  IF r[p] = NULL
                  THEN MemLocs' = [MemLocs EXCEPT ![addr] = Append(MemLocs[bucket[p]], arg[p])]
                  ELSE LET idx == IdxInBktAtAddr(arg[p].key, bucket[p]) IN
                       MemLocs' = [MemLocs EXCEPT ![addr] = [MemLocs[bucket[p]] EXCEPT ![idx] = arg[p]]]
            BY Zenon
          <5>1. CASE bucket[p] = NULL
            <6> USE <5>1
            <6>1. MemLocs' = [MemLocs EXCEPT ![addr] = <<arg[p]>>]
              BY <5>0, Zenon
            <6>2. MemLocs'[addr] \in Seq([key: KeyDomain, val: ValDomain])
              <7> SUFFICES arg[p] \in [key: KeyDomain, val: ValDomain]
                BY <6>1 DEF Seq
              <7> QED
                BY RemDef, Zenon DEF LineIDtoOp, ArgsOf
            <6> QED
              BY <6>1, <6>2
          <5>2. CASE bucket[p] # NULL /\ r[p] = NULL
            <6> USE <5>2
            <6>1. MemLocs' = [MemLocs EXCEPT ![addr] = Append(MemLocs[bucket[p]], arg[p])]
              BY <5>0, Zenon
            <6> SUFFICES Append(MemLocs[bucket[p]], arg[p]) \in Seq([key: KeyDomain, val: ValDomain])
              BY <6>1, Zenon
            <6> SUFFICES /\ MemLocs[bucket[p]] \in Seq([key: KeyDomain, val: ValDomain])
                         /\ arg[p] \in [key: KeyDomain, val: ValDomain]
              BY AppendProperties, Zenon
            <6>2. MemLocs[bucket[p]] \in Seq([key: KeyDomain, val: ValDomain])
              BY Zenon
            <6>3. arg[p] \in [key: KeyDomain, val: ValDomain]
              BY RemDef, Zenon DEF LineIDtoOp, ArgsOf
            <6> QED
              BY <6>2, <6>3
          <5>3. CASE bucket[p] # NULL /\ r[p] # NULL         
            <6> USE <5>3
            <6> DEFINE idx == IdxInBktAtAddr(arg[p].key, bucket[p])
            <6>1. MemLocs' = [MemLocs EXCEPT ![addr] = [MemLocs[bucket[p]] EXCEPT ![idx] = arg[p]]]
              BY <5>0, Zenon
            <6> SUFFICES [MemLocs[bucket[p]] EXCEPT ![idx] = arg[p]] \in Seq([key: KeyDomain, val: ValDomain])
              BY Zenon
            <6> SUFFICES /\ idx \in 1..Len(MemLocs[bucket[p]])
                         /\ MemLocs[bucket[p]] \in Seq([key: KeyDomain, val: ValDomain])
                         /\ arg[p] \in [key: KeyDomain, val: ValDomain]
              BY ExceptSeq, Zenon
            <6>2. arg[p] \in [key: KeyDomain, val: ValDomain]
              BY RemDef, Zenon DEF LineIDtoOp, ArgsOf, U3
            <6>3. MemLocs[bucket[p]] \in Seq([key: KeyDomain, val: ValDomain])
              BY <5>3, Zenon DEF U3
            <6> HIDE DEF U3
            <6>4. idx = CHOOSE index \in 1..Len(MemLocs[bucket[p]]) : MemLocs[bucket[p]][index].key = arg[p].key
              BY DEF IdxInBktAtAddr
            <6>5. \E index \in 1..Len(MemLocs[bucket[p]]) : MemLocs[bucket[p]][index].key = arg[p].key
              <7>1. KeyInBktAtAddr(arg[p].key, bucket[p])
                BY Zenon DEF BktOK, U3
              <7> QED
                BY <7>1 DEF KeyInBktAtAddr
            <6> QED
              BY <6>2, <6>3, <6>4, <6>5, Zenon
          <5> QED
            BY <5>1, <5>2, <5>3
        <4>5. (AllocAddrs \in SUBSET Addrs)'
          OBVIOUS
        <4>6. (bucket \in [ProcSet -> AllocAddrs \union {NULL}])'
          OBVIOUS
        <4>7. (newbkt \in [ProcSet -> AllocAddrs \union {NULL}])'
          OBVIOUS
        <4>8. (r \in [ProcSet -> ValDomain \union {NULL}])'
          OBVIOUS
        <4>9. (arg \in [ProcSet -> ArgDomain])'
          OBVIOUS
        <4>10. (ret \in [ProcSet -> RetDomain])'
          OBVIOUS
        <4>11. (\A p_1 \in ProcSet : (pc[p_1] # RemainderID) => arg[p_1] \in ArgsOf(LineIDtoOp(pc[p_1])))'
          <5> SUFFICES arg[p] \in ArgsOf(LineIDtoOp(pc'[p]))
            BY Zenon
          <5> QED
            BY RemDef, ZenonT(30) DEF LineIDtoOp, ArgsOf
        <4>12. AddrsOK'
          <5> SUFFICES ASSUME NEW p_1 \in ProcSet,
                              pc'[p_1] \in {"I4", "U4", "R4"}
                       PROVE  /\ \A q \in ProcSet : (p_1 # q => /\ newbkt'[p_1] # bucket'[q]
                                                                /\ newbkt'[p_1] # newbkt'[q])
                              /\ \A idx \in 1..N  : (A'[idx] # newbkt'[p_1])
                              /\ newbkt'[p_1] # bucket'[p_1]
                              /\ newbkt'[p_1] \in AllocAddrs'
            BY Zenon DEF AddrsOK
          <5>0. PICK addr \in Addrs : /\ addr \notin AllocAddrs
                                      /\ AllocAddrs' = AllocAddrs \cup {addr}
                                      /\ newbkt' = [newbkt EXCEPT ![p] = addr]
            BY Zenon
          <5> HIDE DEF U3
          <5>1. CASE p_1 = p
            <6>1. newbkt'[p_1] \notin AllocAddrs /\ newbkt'[p_1] # NULL
              BY <5>0, <5>1, NULLDef
            <6>2. \A q \in ProcSet : (p_1 # q => /\ newbkt'[p_1] # bucket'[q]
                                                 /\ newbkt'[p_1] # newbkt'[q])
              <7> SUFFICES ASSUME NEW q \in ProcSet,
                                  p_1 # q
                           PROVE  /\ newbkt'[p_1] # bucket'[q]
                                  /\ newbkt'[p_1] # newbkt'[q]
                OBVIOUS
              <7>1. bucket[q] \in AllocAddrs \/ bucket[q] = NULL
                OBVIOUS
              <7>2. bucket'[q] \in AllocAddrs \/ bucket'[q] = NULL
                BY <7>1, Zenon DEF U3
              <7>3. newbkt[q] \in AllocAddrs \/ newbkt[q] = NULL
                OBVIOUS
              <7>4. newbkt'[q] \in AllocAddrs \/ newbkt'[q] = NULL
                BY <5>1, <7>3, Zenon DEF U3
              <7>5. newbkt'[p_1] # bucket'[q]
                BY <5>1, <6>1, <7>2 DEF AddrsOK
              <7>6. newbkt'[p_1] # newbkt'[q]
                BY <5>1, <6>1, <7>4 DEF AddrsOK
              <7>7. QED
                BY <7>5, <7>6
            <6>3. \A idx \in 1..N  : (A'[idx] # newbkt'[p_1])
              <7> SUFFICES ASSUME NEW idx \in 1..N
                           PROVE  A'[idx] # newbkt'[p_1]
                OBVIOUS
              <7>1. A'[idx] \in AllocAddrs \/ A'[idx] = NULL
                BY <4>3, Zenon DEF U3
              <7> QED
                BY <6>1, <7>1
            <6>4. newbkt'[p_1] # bucket'[p_1]
              <7>1. bucket'[p_1] \in AllocAddrs \/ bucket'[p_1] = NULL
                BY Zenon DEF U3
              <7> QED
                BY <6>1, <7>1
            <6>5. newbkt'[p_1] \in AllocAddrs'
              BY <5>1, Zenon DEF AddrsOK, U3
            <6>6. QED
              BY <6>2, <6>3, <6>4, <6>5
          <5>2. CASE p_1 # p
            <6>1. \A q \in ProcSet : (p_1 # q => /\ newbkt'[p_1] # bucket'[q]
                                                 /\ newbkt'[p_1] # newbkt'[q])
              <7> SUFFICES ASSUME NEW q \in ProcSet,
                                  p_1 # q
                           PROVE  /\ newbkt'[p_1] # bucket'[q]
                                  /\ newbkt'[p_1] # newbkt'[q]
                BY <5>2 DEF AddrsOK
              <7>1. newbkt'[p_1] # bucket'[q]
                BY <5>2, Zenon DEF AddrsOK, U3
              <7>2. newbkt'[p_1] # newbkt'[q]
                <8>1. CASE q = p
                  <9>1. newbkt'[q] \notin AllocAddrs
                    BY <8>1, Zenon DEF U3
                  <9>2. newbkt'[p_1] \in AllocAddrs
                    BY <5>2, Zenon DEF AddrsOK, U3
                  <9> QED  
                    BY <9>1, <9>2
                <8>2. CASE q # p
                  BY <5>2, <8>2, Zenon DEF AddrsOK, U3
                <8> QED
                  BY <8>1, <8>2
              <7>3. QED
                BY <7>1, <7>2
            <6>2. \A idx \in 1..N  : (A'[idx] # newbkt'[p_1])
              BY <5>2, Zenon DEF AddrsOK, U3
            <6>3. newbkt'[p_1] # bucket'[p_1]
              BY <5>2, Zenon DEF AddrsOK, U3
            <6>4. newbkt'[p_1] \in AllocAddrs'
              BY <5>2, Zenon DEF AddrsOK, U3
            <6>5. QED
              BY <6>1, <6>2, <6>3, <6>4
          <5> QED
            BY <5>1, <5>2
        <4>13. BktOK'
          <5> SUFFICES ASSUME NEW q \in ProcSet
                       PROVE  (/\ pc'[q] \in {"I3", "I4"} => (/\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                                                              /\ r'[q] = NULL)
                               /\ pc'[q] \in {"U3", "U4"} => (IF KeyInBktAtAddr(arg[q].key, bucket[q])'
                                                                  THEN (/\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                                                                        /\ r'[q] # NULL)
                                                                  ELSE r'[q] = NULL)
                               /\ pc'[q] \in {"R3", "R4"} => (/\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                                                              /\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                                                              /\ r'[q] # NULL))
            BY Zenon DEF BktOK
          <5>0. PICK addr \in Addrs : /\ addr \notin AllocAddrs
                                      /\ AllocAddrs' = AllocAddrs \cup {addr}
                                      /\ newbkt' = [newbkt EXCEPT ![p] = addr]
                                      /\ \A a \in Addrs : a # addr => MemLocs[a] = MemLocs'[a]
            BY Zenon
          <5> HIDE DEF U3
          <5>1. CASE pc'[q] \in {"I3", "I4"}
            <6>1. KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
              <7>1. CASE bucket[q] = NULL
                <8> USE <7>1
                <8>1. KeyInBktAtAddr(arg[q].key, bucket[q]) = FALSE
                  BY DEF KeyInBktAtAddr
                <8>2. bucket'[q] = NULL
                  BY Zenon DEF U3
                <8>3. KeyInBktAtAddr(arg[q].key, bucket[q])' = FALSE
                  BY <8>2 DEF KeyInBktAtAddr
                <8> QED
                  BY <8>1, <8>3, Zenon
              <7>2. CASE bucket[q] # NULL
                <8> USE <7>2
                <8>1. KeyInBktAtAddr(arg[q].key, bucket[q]) = \E index \in 1..Len(MemLocs[bucket[q]]) : MemLocs[bucket[q]][index].key = arg[q].key
                  BY Zenon DEF KeyInBktAtAddr, U3
                <8>2. bucket'[q] = bucket[q] /\ bucket[q] \in AllocAddrs
                  BY Zenon DEF U3
                <8>3. MemLocs'[bucket[q]] = MemLocs[bucket[q]] /\ arg' = arg
                  BY <8>2, Zenon DEF U3
                <8>4. KeyInBktAtAddr(arg[q].key, bucket[q])' = \E index \in 1..Len(MemLocs'[bucket'[q]]) : MemLocs'[bucket'[q]][index].key = arg'[q].key
                  BY Zenon DEF KeyInBktAtAddr, U3
                <8>5. KeyInBktAtAddr(arg[q].key, bucket[q])' = \E index \in 1..Len(MemLocs[bucket[q]]) : MemLocs[bucket[q]][index].key = arg[q].key
                  BY <8>2, <8>3, <8>4
                <8> QED
                  BY <8>1, <8>5
              <7> QED
                BY <7>1, <7>2
            <6> USE <5>1
            <6> SUFFICES ~KeyInBktAtAddr(arg[q].key, bucket[q])' /\ r'[q] = NULL
              OBVIOUS
            <6>3. ~KeyInBktAtAddr(arg[q].key, bucket[q]) /\ r[q] = NULL
              BY Zenon DEF BktOK, U3
            <6> QED
              BY <6>3, <6>1, Zenon DEF KeyInBktAtAddr, U3
          <5>2. CASE pc'[q] \in {"U3", "U4"}
            <6> USE <5>2
            <6> SUFFICES IF KeyInBktAtAddr(arg[q].key, bucket[q])'
                            THEN (/\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                                  /\ r'[q] # NULL)
                            ELSE r'[q] = NULL
              OBVIOUS
            <6>1. IF KeyInBktAtAddr(arg[q].key, bucket[q])
                     THEN (/\ r[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                           /\ r[q] # NULL)
                     ELSE r[q] = NULL
              BY Zenon DEF BktOK, U3
            <6>2. KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
              <7>1. CASE bucket[q] = NULL
                <8> USE <7>1
                <8>1. KeyInBktAtAddr(arg[q].key, bucket[q]) = FALSE
                  BY DEF KeyInBktAtAddr
                <8>2. bucket'[q] = NULL
                  BY Zenon DEF U3
                <8>3. KeyInBktAtAddr(arg[q].key, bucket[q])' = FALSE
                  BY <8>2 DEF KeyInBktAtAddr
                <8> QED
                  BY <8>1, <8>3, Zenon
              <7>2. CASE bucket[q] # NULL
                <8> USE <7>2
                <8>1. KeyInBktAtAddr(arg[q].key, bucket[q]) = \E index \in 1..Len(MemLocs[bucket[q]]) : MemLocs[bucket[q]][index].key = arg[q].key
                  BY Zenon DEF KeyInBktAtAddr
                <8>2. bucket'[q] = bucket[q] /\ bucket[q] \in AllocAddrs
                  BY Zenon DEF U3
                <8>3. MemLocs'[bucket[q]] = MemLocs[bucket[q]] /\ arg' = arg
                  BY <8>2, Zenon DEF U3
                <8>4. KeyInBktAtAddr(arg[q].key, bucket[q])' = \E index \in 1..Len(MemLocs'[bucket'[q]]) : MemLocs'[bucket'[q]][index].key = arg'[q].key
                  BY Zenon DEF KeyInBktAtAddr, U3
                <8>5. KeyInBktAtAddr(arg[q].key, bucket[q])' = \E index \in 1..Len(MemLocs[bucket[q]]) : MemLocs[bucket[q]][index].key = arg[q].key
                  BY <8>2, <8>3, <8>4
                <8> QED
                  BY <8>1, <8>5
              <7> QED
                BY <7>1, <7>2
            <6>3. CASE KeyInBktAtAddr(arg[q].key, bucket[q])
              <7>1. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
                MemLocs'[bucket'[q]][CHOOSE index \in 1..Len(MemLocs'[bucket'[q]]) :
                                     MemLocs'[bucket'[q]][index].key = arg'[q].key].val
                BY DEF ValOfKeyInBktAtAddr
              <7>2. bucket'[q] = bucket[q] /\ bucket[q] \in AllocAddrs
                BY Zenon, <6>3 DEF KeyInBktAtAddr, U3
              <7>3. MemLocs'[bucket'[q]] = MemLocs[bucket[q]]
                BY <5>0, <7>2, Zenon DEF U3
              <7>4. arg' = arg
                BY Zenon DEF U3
              <7>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
                MemLocs[bucket[q]][CHOOSE index \in 1..Len(MemLocs[bucket[q]]) :
                                    MemLocs[bucket[q]][index].key = arg[q].key].val
                BY <7>1, <7>3, <7>4
              <7>6. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                BY <7>5, Zenon DEF ValOfKeyInBktAtAddr
              <7>7. r'[q] = r[q]
                BY Zenon DEF U3
              <7> QED
                BY <6>1, <6>2, <6>3, <7>6, <7>7
            <6>4. CASE ~KeyInBktAtAddr(arg[q].key, bucket[q])
              BY <6>1, <6>2, <6>4, Zenon DEF U3
            <6> QED
              BY <6>3, <6>4
          <5>3. CASE pc'[q] \in {"R3", "R4"}
            <6> USE <5>3
            <6> SUFFICES /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                         /\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                         /\ r'[q] # NULL
              OBVIOUS
            <6>1. /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                  /\ r[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                  /\ r[q] # NULL
              BY Zenon DEF BktOK, U3
            <6>2. MemLocs[bucket[q]] = MemLocs'[bucket'[q]]
              <7>1. bucket[q] = bucket'[q]
                BY Zenon DEF U3
              <7>2. bucket[q] \in AllocAddrs
                BY Zenon, <6>1 DEF KeyInBktAtAddr
              <7>3. bucket[q] # addr
                BY <5>0, <7>2
              <7>4. MemLocs'[bucket[q]] = MemLocs[bucket[q]]
                BY <5>0, <7>2, <7>3, Zenon
              <7> QED
                BY <7>1, <7>4
            <6>3. KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
              BY <6>2, Zenon DEF KeyInBktAtAddr, U3
            <6>4. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs'[bucket'[q]][CHOOSE index \in 1..Len(MemLocs'[bucket'[q]]) :
                                   MemLocs'[bucket'[q]][index].key = arg'[q].key].val
              BY DEF ValOfKeyInBktAtAddr
            <6>5. arg = arg'
              BY Zenon DEF U3
            <6>6. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs[bucket[q]][CHOOSE index \in 1..Len(MemLocs[bucket[q]]) :
                                   MemLocs[bucket[q]][index].key = arg'[q].key].val
              BY <6>2, <6>4
            <6>7. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs[bucket[q]][CHOOSE index \in 1..Len(MemLocs[bucket[q]]) :
                                  MemLocs[bucket[q]][index].key = arg[q].key].val
              BY Zenon, <6>6, <6>5
            <6>8. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
              BY <6>7, Zenon DEF ValOfKeyInBktAtAddr
            <6> QED
              BY <6>1, <6>3, <6>8, Zenon DEF U3
          <5> QED
            BY <5>1, <5>2, <5>3
        <4>14. Uniq'
          <5> SUFFICES ASSUME NEW a \in AllocAddrs', 
                              NEW bucket_arr, bucket_arr = MemLocs'[a],
                              NEW j1 \in 1..Len(bucket_arr),
                              NEW j2 \in 1..Len(bucket_arr),
                              bucket_arr[j1].key = bucket_arr[j2].key
                       PROVE  j1 = j2
            BY Zenon DEF Uniq
          <5>1. PICK addr \in Addrs : /\ addr \notin AllocAddrs
                                      /\ AllocAddrs' = AllocAddrs \cup {addr}
                                      /\ CASE bucket[p] = NULL                -> MemLocs' = [MemLocs EXCEPT ![addr] = <<arg[p]>>]
                                           [] bucket[p] # NULL /\ r[p] = NULL -> MemLocs' = [MemLocs EXCEPT ![addr] = Append(MemLocs[bucket[p]], arg[p])]
                                           [] bucket[p] # NULL /\ r[p] # NULL -> LET idx == IdxInBktAtAddr(arg[p].key, bucket[p]) IN 
                                                                                 MemLocs' = [MemLocs EXCEPT ![addr] = [MemLocs[bucket[p]] EXCEPT ![idx] = arg[p]]]
            BY Zenon
          <5>2. \A ad \in Addrs : ad # addr => MemLocs'[ad] = MemLocs[ad]
            BY <5>1, Zenon
          <5>3. CASE a # addr
            BY <5>1, <5>2, <5>3, Zenon DEF Uniq
          <5> SUFFICES ASSUME a = addr
                       PROVE  j1 = j2
            BY <5>3, Zenon
          <5>4. CASE bucket[p] = NULL
            <6> HIDE DEF U3
            <6>1. Len(bucket_arr) = 1
              BY <5>1, <5>4
            <6> QED
              BY <6>1
          <5>5. CASE bucket[p] # NULL /\ r[p] = NULL
            <6> HIDE DEF U3
            <6>1. bucket_arr = Append(MemLocs[bucket[p]], arg[p])
              BY <5>1, <5>5, Zenon
            <6>2. MemLocs[bucket[p]] \in Seq([key: KeyDomain, val: ValDomain])
              BY <5>5, Zenon
            <6>3. arg[p] \in [key: KeyDomain, val: ValDomain]
              BY RemDef, Zenon DEF LineIDtoOp, ArgsOf, U3
            <6>4. Len(bucket_arr) = Len(MemLocs[bucket[p]])+1
              BY <6>1, <6>2, <6>3, AppendProperties
            <6>5. \A index \in 1..Len(MemLocs[bucket[p]]) : Append(MemLocs[bucket[p]], arg[p])[index] = MemLocs[bucket[p]][index]
              BY <6>2, <6>3, AppendProperties
            <6>6. \A index \in 1..Len(MemLocs[bucket[p]]) : bucket_arr[index] = MemLocs[bucket[p]][index]
              BY <6>1, <6>5, Zenon
            <6>7. CASE j1 = Len(bucket_arr)
              <7>1. bucket_arr[j1] = arg[p]
                BY <6>1, <6>2, <6>3, <6>7, AppendProperties
              <7>2. \A index \in 1..Len(MemLocs[bucket[p]]) : MemLocs[bucket[p]][index].key # arg[p].key
                BY Zenon, <5>5 DEF KeyInBktAtAddr, BktOK, U3
              <7>3. \A index \in 1..Len(MemLocs[bucket[p]]) : bucket_arr[index].key # arg[p].key
                BY <6>6, <7>2, Zenon
              <7>4. j2 \notin 1..Len(MemLocs[bucket[p]])
                BY <7>1, <7>3
              <7>5. j2 = Len(bucket_arr)
                BY <6>4, <7>4
              <7> QED
                BY <6>7, <7>5
            <6>8. CASE j2 = Len(bucket_arr)
              <7>1. bucket_arr[j2] = arg[p]
                BY <6>1, <6>2, <6>3, <6>8, AppendProperties
              <7>2. \A index \in 1..Len(MemLocs[bucket[p]]) : MemLocs[bucket[p]][index].key # arg[p].key
                BY Zenon, <5>5 DEF KeyInBktAtAddr, BktOK, U3
              <7>3. \A index \in 1..Len(MemLocs[bucket[p]]) : bucket_arr[index].key # arg[p].key
                BY <6>6, <7>2, Zenon
              <7>4. j1 \notin 1..Len(MemLocs[bucket[p]])
                BY <7>1, <7>3
              <7>5. j1 = Len(bucket_arr)
                BY <6>4, <7>4
              <7> QED
                BY <6>7, <7>5
            <6>9. CASE j1 # Len(bucket_arr) /\ j2 # Len(bucket_arr)
              <7>1. j1 \in 1..Len(MemLocs[bucket[p]]) /\ j2 \in 1..Len(MemLocs[bucket[p]])
                BY <6>4, <6>9
              <7>2. bucket[p] \in AllocAddrs
                BY <5>5
              <7> QED
                BY <6>6, <7>1, <7>2 DEF Uniq
            <6> QED
              BY <6>7, <6>8, <6>9
          <5>6. CASE bucket[p] # NULL /\ r[p] # NULL
            <6> HIDE DEF U3
            <6> DEFINE idx == IdxInBktAtAddr(arg[p].key, bucket[p])
            <6>1. bucket_arr = [MemLocs[bucket[p]] EXCEPT ![idx] = arg[p]]
              BY <5>1, <5>6, Zenon
            <6>2. MemLocs[bucket[p]] \in Seq([key: KeyDomain, val: ValDomain])
              BY <5>6, Zenon
            <6>3. arg[p] \in [key: KeyDomain, val: ValDomain]
              BY RemDef, Zenon DEF LineIDtoOp, ArgsOf, U3
            <6>4. Len(bucket_arr) = Len(MemLocs[bucket[p]])
              BY <6>1, <6>2, <6>3, ExceptSeq
            <6>5. \A index \in 1..Len(MemLocs[bucket[p]]) : /\ index # idx => bucket_arr[index] = MemLocs[bucket[p]][index]
                                                            /\ index = idx => bucket_arr[index] = arg[p]
              BY <6>1, <6>2, <6>3, ExceptSeq
            <6>6. idx = CHOOSE index \in 1..Len(MemLocs[bucket[p]]) : MemLocs[bucket[p]][index].key = arg[p].key
              BY DEF IdxInBktAtAddr
            <6>7. \E index \in 1..Len(MemLocs[bucket[p]]) : MemLocs[bucket[p]][index].key = arg[p].key
              <7>1. KeyInBktAtAddr(arg[p].key, bucket[p])
                BY <5>6, Zenon DEF BktOK, U3
              <7> QED
                BY <7>1 DEF KeyInBktAtAddr
            <6>8. CASE j1 = idx
              <7>1. bucket[p] \in AllocAddrs
                BY <5>6
              <7>2. MemLocs[bucket[p]][j1].key = arg[p].key
                BY <6>4, <6>6, <6>7, <6>8
              <7>3. bucket_arr[j1].key = arg[p].key
                BY <6>1, <6>8
              <7>4. MemLocs[bucket[p]][j1].key = bucket_arr[j1].key
                BY <7>2, <7>3
              <7> SUFFICES ASSUME j2 # idx PROVE FALSE
                BY <6>8
              <7>5. MemLocs[bucket[p]][j2].key = bucket_arr[j2].key
                BY <6>4, <6>5
              <7>6. MemLocs[bucket[p]][j1].key = MemLocs[bucket[p]][j2].key
                BY <7>4, <7>5
              <7>7. j1 = j2
                BY <6>4, <7>1, <7>6 DEF Uniq
              <7> QED
                BY <6>8, <7>7
            <6>9. CASE j2 = idx
              <7>1. bucket[p] \in AllocAddrs
                BY <5>6
              <7>2. MemLocs[bucket[p]][j2].key = arg[p].key
                BY <6>4, <6>6, <6>7, <6>9
              <7>3. bucket_arr[j2].key = arg[p].key
                BY <6>1, <6>9
              <7>4. MemLocs[bucket[p]][j2].key = bucket_arr[j2].key
                BY <7>2, <7>3
              <7> SUFFICES ASSUME j1 # idx PROVE FALSE
                BY <6>8
              <7>5. MemLocs[bucket[p]][j1].key = bucket_arr[j1].key
                BY <6>4, <6>5
              <7>6. MemLocs[bucket[p]][j2].key = MemLocs[bucket[p]][j1].key
                BY <7>4, <7>5
              <7>7. j1 = j2
                BY <6>4, <7>1, <7>6 DEF Uniq
              <7> QED
                BY <6>9, <7>7
            <6>10. CASE j1 # idx /\ j2 # idx
              <7>1. bucket[p] \in AllocAddrs
                BY <5>6
              <7>2. bucket_arr[j1] = MemLocs[bucket[p]][j1] /\ bucket_arr[j2] = MemLocs[bucket[p]][j2]
                BY <6>4, <6>5, <6>10
              <7>3. MemLocs[bucket[p]][j1].key = MemLocs[bucket[p]][j2].key
                BY <7>2
              <7> QED
                BY <6>4, <7>1, <7>3 DEF Uniq
            <6> QED
              BY <6>8, <6>9, <6>10
          <5> QED
            BY <5>4, <5>5, <5>6, Zenon
        <4>15. NewBktOK'
          <5> SUFFICES ASSUME NEW q \in ProcSet
                       PROVE  /\ pc'[q] = "I4" => /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                                  /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                                                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                            /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                               (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
                              /\ pc'[q] = "U4" => /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                                  /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                                                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                            /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                               (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
                              /\ pc'[q] = "R4" => /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                            /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                               (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
            BY ZenonT(60) DEF NewBktOK
          <5> PICK addr \in Addrs : /\ addr \notin AllocAddrs
                                    /\ AllocAddrs' = AllocAddrs \cup {addr}
                                    /\ newbkt' = [newbkt EXCEPT ![p] = addr]
                                    /\ CASE bucket[p] = NULL                -> MemLocs' = [MemLocs EXCEPT ![addr] = <<arg[p]>>]
                                         [] bucket[p] # NULL /\ r[p] = NULL -> MemLocs' = [MemLocs EXCEPT ![addr] = Append(MemLocs[bucket[p]], arg[p])]
                                         [] bucket[p] # NULL /\ r[p] # NULL -> LET idx == IdxInBktAtAddr(arg[p].key, bucket[p]) IN
                                                                               MemLocs' = [MemLocs EXCEPT ![addr] = [MemLocs[bucket[p]] EXCEPT ![idx] = arg[p]]]
            BY Zenon
          <5> /\ pc[p] = "U3"
              /\ pc' = [pc EXCEPT ![p] = "U4"]
              /\ UNCHANGED <<A, bucket, r, arg, ret>>
            BY Zenon
          <5> HIDE DEF U3
          <5>A. \A a \in Addrs : a # addr => MemLocs'[a] = MemLocs[a]
            BY ZenonT(30)
          <5>B. ASSUME NEW k \in KeyDomain, q # p, pc[q] \in {"I4", "U4", "R4"}
                PROVE  /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, bucket[q])'
                       /\ KeyInBktAtAddr(k, newbkt[q]) = KeyInBktAtAddr(k, newbkt[q])'
                       /\ KeyInBktAtAddr(k, bucket[q]) => (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])')
                       /\ KeyInBktAtAddr(k, newbkt[q]) => (ValOfKeyInBktAtAddr(k, newbkt[q]) = ValOfKeyInBktAtAddr(k, newbkt[q])')
            <6> USE <5>B
            <6>1. bucket[q] = bucket'[q] /\ newbkt'[q] = newbkt[q] /\ newbkt[q] \in AllocAddrs
              BY NULLDef, Zenon DEF AddrsOK
            <6>2. MemLocs[newbkt[q]] = MemLocs'[newbkt'[q]]
              BY <5>A, <6>1, Zenon
            <6>3. KeyInBktAtAddr(k, newbkt[q]) = KeyInBktAtAddr(k, newbkt[q])'  
              BY Zenon, <6>1, <6>2 DEF KeyInBktAtAddr
            <6>4. ValOfKeyInBktAtAddr(k, newbkt[q]) = ValOfKeyInBktAtAddr(k, newbkt[q])'
              <7> DEFINE bkt_arr == MemLocs'[newbkt'[q]]
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
              <7>1. ValOfKeyInBktAtAddr(k, newbkt[q])' = bkt_arr[idx].val
                BY Zenon DEF ValOfKeyInBktAtAddr
              <7>2. bkt_arr = MemLocs[newbkt[q]]
                BY Zenon, <6>2
              <7>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
                BY Zenon
              <7> QED
                BY <7>1, <7>2, <7>3, Isa DEF ValOfKeyInBktAtAddr
            <6>5. CASE bucket[q] = NULL
              BY <6>1, <6>3, <6>4, <6>5, Zenon DEF KeyInBktAtAddr
            <6> SUFFICES ASSUME bucket[q] \in AllocAddrs
                         PROVE  /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, bucket[q])'
                                /\ KeyInBktAtAddr(k, bucket[q]) => (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])')
              BY NULLDef, <6>5, <6>3, <6>4, Zenon
            <6>6. MemLocs[bucket[q]] = MemLocs'[bucket'[q]]
              BY <5>A, <6>1, Zenon
            <6>7. KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, bucket[q])'  
              BY Zenon, <6>1, <6>6 DEF KeyInBktAtAddr
            <6> SUFFICES ASSUME KeyInBktAtAddr(k, bucket[q])
                         PROVE  ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])'
              BY <6>7, Zenon
            <6>8. ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])'
              <7> DEFINE bkt_arr == MemLocs'[bucket'[q]]
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
              <7>1. ValOfKeyInBktAtAddr(k, bucket[q])' = bkt_arr[idx].val
                BY Zenon DEF ValOfKeyInBktAtAddr
              <7>2. bkt_arr = MemLocs[bucket[q]]
                BY Zenon, <6>6
              <7>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
                BY Zenon
              <7> QED
                BY <7>1, <7>2, <7>3, Isa DEF ValOfKeyInBktAtAddr
            <6> QED
              BY <6>8
          <5>1. CASE pc'[q] = "I4"
            <6> USE <5>1
            <6>1. /\ KeyInBktAtAddr(arg[q].key, newbkt[q])
                  /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q]) = arg[q].val
                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                            /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                               (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
              BY Zenon DEF NewBktOK
            <6>2. arg[q].key \in KeyDomain
              BY RemDef, Zenon DEF ArgsOf, LineIDtoOp
            <6> QED
              BY <5>B, <6>1, <6>2, ZenonT(30)
          <5>2. CASE pc'[q] = "U4"
            <6> USE <5>2
            <6> SUFFICES /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                         /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                         /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                   /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                      (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
              OBVIOUS
            <6>1. CASE q = p
              <7> USE <6>1
              <7>1. CASE bucket[p] = NULL
                <8> USE <7>1
                <8> DEFINE bkt_arr == MemLocs'[newbkt'[q]]
                <8>1. newbkt'[q] = addr /\ bkt_arr = <<arg[q]>> /\ arg = arg'
                  BY Zenon
                <8>2. KeyInBktAtAddr(arg[q].key, newbkt[q])'
                  <9> SUFFICES newbkt'[q] # NULL /\ \E index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg'[q].key
                    BY Zenon DEF KeyInBktAtAddr
                  <9> SUFFICES newbkt'[q] # NULL /\ \E index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
                    BY <8>1 
                  <9>1. newbkt'[q] # NULL
                    BY <8>1, NULLDef, Zenon
                  <9>2. Len(bkt_arr) = 1
                    BY <8>1
                  <9>3. 1 \in 1..Len(bkt_arr)
                    BY <9>2
                  <9>4. bkt_arr[1].key = arg[q].key
                    BY <8>1
                  <9> QED
                    BY <9>1, <9>3, <9>4
                <8>3. ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                  <9> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
                  <9>1. ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = bkt_arr[idx].val
                    BY <8>1, Zenon DEF ValOfKeyInBktAtAddr
                  <9>2. Len(bkt_arr) = 1
                    BY <8>1
                  <9>3. \E index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
                    BY <8>1, <8>2, Zenon DEF KeyInBktAtAddr
                  <9>4. idx = 1
                    BY <9>2, <9>3
                  <9> HIDE DEF bkt_arr, idx
                  <9>5. bkt_arr[idx].val = arg[q].val
                    BY <8>1, <9>4
                  <9> QED
                    BY <9>1, <9>5
                <8>4. ASSUME NEW k \in KeyDomain, k # arg[q].key
                      PROVE  /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])' 
                             /\ KeyInBktAtAddr(k, bucket[q])' =>
                                (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
                  <9> USE <8>4
                  <9>1. KeyInBktAtAddr(k, bucket[q])' = FALSE
                    BY Zenon DEF KeyInBktAtAddr
                  <9>2. KeyInBktAtAddr(k, newbkt[q])' = FALSE
                    <10>1. Len(bkt_arr) = 1
                      BY <8>1
                    <10>2. \A index \in 1..Len(bkt_arr) : index = 1
                      BY <10>1
                    <10>3. \A index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
                      BY <10>2
                    <10> QED
                      BY <10>3, Zenon DEF KeyInBktAtAddr 
                  <9> QED
                    BY <9>1, <9>2, Zenon
                <8> QED
                  BY <8>2, <8>3, <8>4
              <7>2. CASE bucket[p] # NULL /\ r[p] = NULL
                <8> USE <7>2
                <8> DEFINE bkt_arr == MemLocs'[newbkt'[q]]
                <8>1. newbkt'[q] = addr /\ bkt_arr = Append(MemLocs[bucket[q]], arg[q]) /\ arg = arg'
                  BY Zenon
                <8>2. KeyInBktAtAddr(arg[q].key, newbkt[q])'
                  <9> SUFFICES newbkt'[q] # NULL /\ \E index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg'[q].key
                    BY Zenon DEF KeyInBktAtAddr
                  <9> SUFFICES newbkt'[q] # NULL /\ \E index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
                    BY <8>1 
                  <9>1. newbkt'[q] # NULL
                    BY <8>1, NULLDef, Zenon
                  <9>2. MemLocs[bucket[q]] \in Seq([key: KeyDomain, val: ValDomain])
                    BY Zenon
                  <9>3. arg[q] \in [key: KeyDomain, val: ValDomain]
                    BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
                  <9> HIDE DEF bkt_arr
                  <9>4. bkt_arr[Len(bkt_arr)] = arg[q]
                    BY <8>1, <9>2, <9>3, AppendProperties
                  <9> USE DEF bkt_arr
                  <9>5. Len(bkt_arr) \in 1..Len(bkt_arr)
                    BY <9>2, <9>3, AppendProperties, LenProperties
                  <9> QED
                    BY <9>1, <9>4, <9>5
                <8>3. ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                  <9> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
                  <9>1. ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = bkt_arr[idx].val
                    BY Zenon, <8>1 DEF ValOfKeyInBktAtAddr
                  <9> PICK index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
                    BY Zenon, <8>1, <8>2 DEF KeyInBktAtAddr
                  <9> idx = index
                    OBVIOUS
                  <9>2. MemLocs[bucket[q]] \in Seq([key: KeyDomain, val: ValDomain])
                    BY Zenon
                  <9>3. arg[q] \in [key: KeyDomain, val: ValDomain]
                    BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
                  <9> HIDE DEF bkt_arr
                  <9>4. bkt_arr[Len(bkt_arr)] = arg[q]
                    BY <8>1, <9>2, <9>3, AppendProperties
                  <9> USE DEF bkt_arr
                  <9>5. Len(MemLocs[bucket[q]]) \in Nat /\ Len(bkt_arr) \in 1..Len(bkt_arr) /\ Len(bkt_arr) = Len(MemLocs[bucket[q]])+1
                    BY <9>2, <9>3, AppendProperties, LenProperties
                  <9>6. \A ind \in 1..Len(MemLocs[bucket[q]]) : MemLocs[bucket[q]][ind].key # arg[q].key
                    BY Zenon DEF BktOK, KeyInBktAtAddr
                  <9>7. index = Len(bkt_arr)
                    BY <9>5, <9>6, Z3T(90)
                  <9>8. bkt_arr[index] = arg[q]
                    BY <9>4, <9>7, Zenon
                  <9> QED
                    BY <9>1, <9>8, Zenon
                <8>4. ASSUME NEW k \in KeyDomain, k # arg[q].key
                      PROVE  /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])' 
                             /\ KeyInBktAtAddr(k, bucket[q])' =>
                                (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
                  <9> USE <8>4
                  <9>1. CASE KeyInBktAtAddr(k, bucket[q])' = TRUE
                    <10> USE <9>1
                    <10> SUFFICES /\ KeyInBktAtAddr(k, newbkt[q])'
                                  /\ ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])'
                      BY Zenon 
                    <10>1. bucket[q] \in AllocAddrs
                      BY Zenon
                    <10>2. bucket[q] # addr /\ bucket[q] = bucket'[q]
                      BY <10>1, Zenon
                    <10>3. MemLocs'[bucket'[q]] = MemLocs[bucket[q]]
                      BY Zenon, <5>A, <10>2
                    <10>4. \E index \in 1..Len(MemLocs[bucket[q]]) : MemLocs[bucket[q]][index].key = k
                      BY Zenon, <10>3 DEF KeyInBktAtAddr
                    <10>5. MemLocs[bucket[q]] \in Seq([key: KeyDomain, val: ValDomain])
                      BY Zenon
                    <10>6. arg[q] \in [key: KeyDomain, val: ValDomain]
                      BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
                    <10>7. /\ \A index \in 1..Len(MemLocs[bucket[q]]) : bkt_arr[index] = MemLocs[bucket[q]][index]
                           /\ Len(MemLocs[bucket[q]]) \in Nat
                           /\ Len(bkt_arr) = Len(MemLocs[bucket[q]])+1
                           /\ bkt_arr[Len(bkt_arr)] = arg[q]
                      BY <10>5, <10>6, AppendProperties, LenProperties
                    <10>8. \E index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
                      BY <10>4, <10>7
                    <10>9. newbkt'[q] # NULL
                      BY NULLDef
                    <10>10. KeyInBktAtAddr(k, newbkt[q])'
                      BY <8>1, <10>8, <10>9, Zenon DEF KeyInBktAtAddr
                    <10> DEFINE idx == CHOOSE index \in 1..Len(MemLocs'[bucket'[q]]) : MemLocs'[bucket'[q]][index].key = k
                    <10>11. ValOfKeyInBktAtAddr(k, bucket[q])' = MemLocs'[bucket'[q]][idx].val
                       BY Zenon, <10>3 DEF ValOfKeyInBktAtAddr
                    <10> PICK index \in 1..Len(MemLocs'[bucket'[q]]) : MemLocs'[bucket'[q]][index].key = k
                      BY Zenon DEF KeyInBktAtAddr
                    <10> idx = index
                      OBVIOUS
                    <10> index \in 1..Len(MemLocs[bucket[q]]) /\ MemLocs[bucket[q]][index].key = k
                      BY <10>3
                    <10>12. ValOfKeyInBktAtAddr(k, bucket[q])' = MemLocs[bucket[q]][index].val
                      BY <10>3, <10>11, Zenon
                    <10>13. ValOfKeyInBktAtAddr(k, bucket[q])' = bkt_arr[index].val
                      BY <10>12, <10>7, Zenon
                    <10>14. bkt_arr[Len(bkt_arr)].key # k
                      BY <10>7
                    <10>15. \A ind \in 1..Len(MemLocs[bucket[q]]) : MemLocs[bucket[q]][ind].key = MemLocs[bucket[q]][index].key => ind = index
                      BY Zenon, <10>1 DEF Uniq
                    <10>16. \A ind \in 1..Len(MemLocs[bucket[q]]) : ind # index => MemLocs[bucket[q]][ind].key # k
                      BY <10>15, Zenon
                    <10>17. \A ind \in 1..Len(bkt_arr) : ind # index => bkt_arr[ind].key # k
                      BY <10>16, <10>14, <10>7, Z3T(30)
                    <10>18. \E ind \in 1..Len(bkt_arr) : bkt_arr[ind].key = k
                      BY <10>7
                    <10>19. ValOfKeyInBktAtAddr(k, newbkt[q])' = bkt_arr[index].val
                      BY <8>1, <10>17, <10>18, Zenon DEF ValOfKeyInBktAtAddr
                    <10> QED
                      BY <10>10, <10>13, <10>19, Zenon
                  <9>2. CASE KeyInBktAtAddr(k, bucket[q])' = FALSE
                    <10> USE <9>2
                    <10> SUFFICES KeyInBktAtAddr(k, newbkt[q])' = FALSE
                      BY Zenon
                    <10>1. bucket[q] \in AllocAddrs
                      BY Zenon
                    <10>2. bucket[q] # addr /\ bucket[q] = bucket'[q]
                      BY <10>1, Zenon
                    <10>3. MemLocs'[bucket'[q]] = MemLocs[bucket[q]]
                      BY Zenon, <5>A, <10>2
                    <10>4. \A index \in 1..Len(MemLocs[bucket[q]]) : MemLocs[bucket[q]][index].key # k
                      BY Zenon, <10>3 DEF KeyInBktAtAddr
                    <10>5. MemLocs[bucket[q]] \in Seq([key: KeyDomain, val: ValDomain])
                      BY Zenon
                    <10>6. arg[q] \in [key: KeyDomain, val: ValDomain]
                      BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
                    <10> HIDE DEF bkt_arr
                    <10>7. bkt_arr[Len(bkt_arr)].key # k
                      BY <8>1, <10>5, <10>6, AppendProperties
                    <10> USE DEF bkt_arr
                    <10>8. /\ \A index \in 1..Len(MemLocs[bucket[q]]) : bkt_arr[index] = MemLocs[bucket[q]][index]
                           /\ Len(MemLocs[bucket[q]]) \in Nat
                           /\ Len(bkt_arr) = Len(MemLocs[bucket[q]])+1
                      BY <10>5, <10>6, AppendProperties, LenProperties
                    <10> QED
                      BY <10>4, <10>7, <10>8 DEF KeyInBktAtAddr
                  <9> QED
                    BY <9>1, <9>2, Zenon DEF KeyInBktAtAddr
                <8> QED
                  BY <8>2, <8>3, <8>4
              <7>3. CASE bucket[p] # NULL /\ r[p] # NULL
                <8> USE <7>3
                <8> DEFINE bkt_arr == MemLocs'[newbkt'[q]]
                <8> DEFINE idx == IdxInBktAtAddr(arg[p].key, bucket[p])
                <8> DEFINE old_arr == MemLocs[bucket[q]]
                <8> idx = CHOOSE index \in 1..Len(old_arr) : old_arr[index].key = arg[p].key
                  BY Zenon DEF IdxInBktAtAddr
                <8> /\ bucket[p] # NULL
                    /\ bucket[p] \in AllocAddrs
                    /\ \E index \in 1..Len(old_arr) : old_arr[index].key = arg[p].key
                  BY Zenon DEF BktOK, KeyInBktAtAddr
                <8> PICK index \in 1..Len(old_arr) : old_arr[index].key = arg[p].key
                  OBVIOUS
                <8> idx = index
                  OBVIOUS
                <8>1. \A ind \in 1..Len(old_arr) : old_arr[ind].key = old_arr[index].key => ind = index
                  BY DEF Uniq
                <8>2. \A ind \in 1..Len(old_arr) : ind # index => old_arr[ind].key # arg[p].key
                  BY <8>1
                <8>3. newbkt'[q] = addr /\ bkt_arr = [old_arr EXCEPT ![idx] = arg[p]] /\ arg = arg'
                  BY Zenon
                <8>4. \A ind \in 1..Len(bkt_arr) : ind # index => bkt_arr[ind].key # arg[p].key
                  BY <8>3, <8>2
                <8>5. idx \in 1..Len(bkt_arr) /\ bkt_arr[idx].key = arg[p].key
                  BY <8>3  
                <8>6. KeyInBktAtAddr(arg[q].key, newbkt[q])'
                  BY <8>3, <8>5, Zenon, NULLDef DEF KeyInBktAtAddr
                <8>7. ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                  <9>1. ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = bkt_arr[idx].val
                    BY <8>3, <8>5, <8>4, Zenon DEF ValOfKeyInBktAtAddr
                  <9>2. bkt_arr[idx].val = arg[q].val
                    BY <8>3
                  <9> QED
                    BY <8>5, <9>1, <9>2, Zenon
                <8>8. ASSUME NEW k \in KeyDomain, k # arg[q].key
                      PROVE  /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])' 
                             /\ KeyInBktAtAddr(k, bucket[q])' =>
                                (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
                  <9> USE <8>8
                  <9>1. CASE KeyInBktAtAddr(k, bucket[q]) = TRUE
                    <10> USE <9>1
                    <10>1. KeyInBktAtAddr(k, bucket[q])' = TRUE
                      BY Zenon DEF KeyInBktAtAddr
                    <10> PICK ind \in 1..Len(old_arr) : old_arr[ind].key = k
                      BY Zenon DEF KeyInBktAtAddr
                    <10>2. ind # idx
                      OBVIOUS
                    <10>3. bkt_arr[ind].key = k
                      BY <10>2 
                    <10>4. KeyInBktAtAddr(k, newbkt[q])' = TRUE
                      BY <8>3, <10>3, NULLDef DEF KeyInBktAtAddr
                    <10>5. ValOfKeyInBktAtAddr(k, bucket[q]) = old_arr[CHOOSE id \in 1..Len(old_arr) : old_arr[id].key = k].val
                      BY Zenon DEF ValOfKeyInBktAtAddr
                    <10>6. ind = CHOOSE id \in 1..Len(old_arr) : old_arr[id].key = k
                      OBVIOUS
                    <10>7. ValOfKeyInBktAtAddr(k, bucket[q]) = old_arr[ind].val
                      BY <10>6, <10>5
                    <10>8. old_arr = old_arr'
                      BY Zenon
                    <10>9. ValOfKeyInBktAtAddr(k, bucket[q])' = old_arr'[CHOOSE id \in 1..Len(old_arr') : old_arr'[id].key = k].val
                      BY Zenon DEF ValOfKeyInBktAtAddr
                    <10>10. ValOfKeyInBktAtAddr(k, bucket[q])' = old_arr[CHOOSE id \in 1..Len(old_arr) : old_arr[id].key = k].val
                      BY <10>8, <10>9
                    <10>11. ValOfKeyInBktAtAddr(k, bucket[q])' = old_arr[ind].val
                      BY <10>6, <10>10
                    <10>12. old_arr[ind] = bkt_arr[ind]
                      BY <10>2
                    <10>13. ValOfKeyInBktAtAddr(k, newbkt[q])' = bkt_arr[CHOOSE id \in 1..Len(bkt_arr) : bkt_arr[id].key = k].val
                      BY Zenon DEF ValOfKeyInBktAtAddr
                    <10>14. \E id \in 1..Len(bkt_arr) : bkt_arr[id].key = k
                      BY <10>3
                    <10>15. \A id \in 1..Len(bkt_arr) : bkt_arr[id].key = bkt_arr[ind].key => id = ind
                      BY <4>14 DEF Uniq
                    <10>16. \A id \in 1..Len(bkt_arr) : bkt_arr[id].key = k => id = ind
                      BY <10>3, <10>15
                    <10>17. ind = CHOOSE id \in 1..Len(bkt_arr) : bkt_arr[id].key = k
                      BY <10>14, <10>16
                    <10>18. ValOfKeyInBktAtAddr(k, newbkt[q])' = bkt_arr[ind].val
                      BY <10>13, <10>17, Zenon
                    <10>19. ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])'
                      BY <10>11, <10>12, <10>18
                    <10> QED
                      BY <10>1, <10>4, <10>19
                  <9>2. CASE KeyInBktAtAddr(k, bucket[q]) = FALSE
                    <10> USE <9>2
                    <10>1. KeyInBktAtAddr(k, bucket[q])' = FALSE
                      BY Zenon DEF KeyInBktAtAddr
                    <10>2. \A ind \in 1..Len(old_arr) : old_arr[ind].key # k
                      BY Zenon DEF KeyInBktAtAddr
                    <10>3. \A ind \in 1..Len(bkt_arr) : ind # idx => bkt_arr[ind].key = old_arr[ind].key
                      OBVIOUS
                    <10>4. bkt_arr[idx].key = old_arr[idx].key
                      BY <8>5, Zenon
                    <10>5. \A ind \in 1..Len(bkt_arr) : bkt_arr[ind].key = old_arr[ind].key
                      BY <10>3, <10>4, Zenon
                    <10>6. \A ind \in 1..Len(bkt_arr) : bkt_arr[ind].key # k
                      BY <10>5, <10>2
                    <10>7. KeyInBktAtAddr(k, newbkt[q])' = FALSE
                      BY <8>3, <10>6 DEF KeyInBktAtAddr
                    <10> QED
                      BY <10>1, <10>7, Zenon
                  <9> QED
                    BY <9>1, <9>2 DEF KeyInBktAtAddr
                <8> QED
                  BY <8>6, <8>7, <8>8
              <7> QED
                BY <7>1, <7>2, <7>3
            <6>2. CASE q # p
              <7> USE <6>2
              <7>1. /\ KeyInBktAtAddr(arg[q].key, newbkt[q])
                    /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q]) = arg[q].val
                    /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                              /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                                 (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
                BY Zenon DEF NewBktOK
              <7>2. arg[q].key \in KeyDomain
                BY RemDef, Zenon DEF ArgsOf, LineIDtoOp
              <7> QED
                BY <5>B, <7>1, <7>2, ZenonT(30)
            <6> QED
              BY <6>1, <6>2
          <5>3. CASE pc'[q] = "R4"
            <6> USE <5>3
            <6>1. /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])
                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                            /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                               (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
              BY Zenon DEF NewBktOK
            <6>2. arg[q].key \in KeyDomain
              BY RemDef, Zenon DEF ArgsOf, LineIDtoOp
            <6> QED
              BY <5>B, <6>1, <6>2, ZenonT(30)
          <5> QED
            BY <5>1, <5>2, <5>3
        <4> QED
          BY <4>1, <4>10, <4>11, <4>12, <4>13, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, <4>14, <4>15 DEF Inv
      <3>10. CASE Line = U4(p)
        <4> USE <3>10 DEF U4
        <4>1. PTypeOK'
          BY NextPTypeOK
        <4>2. (pc \in [ProcSet -> LineIDs])'
          BY Isa DEF LineIDs
        <4>3. (A \in [1..N -> AllocAddrs \union {NULL}])'
          <5>1. CASE A[Hash[arg[p].key]] = bucket[p]
            <6> SUFFICES newbkt[p] \in AllocAddrs \union {NULL}
              BY <5>1, Isa
            <6> QED
              OBVIOUS
          <5>2. CASE A[Hash[arg[p].key]] # bucket[p] 
            BY <5>2
          <5> QED
            BY <5>1, <5>2
        <4>4. (MemLocs \in [Addrs -> Seq([key: KeyDomain, val: ValDomain])])'
          OBVIOUS
        <4>5. (AllocAddrs \in SUBSET Addrs)'
          OBVIOUS
        <4>6. (bucket \in [ProcSet -> AllocAddrs \union {NULL}])'
          OBVIOUS
        <4>7. (newbkt \in [ProcSet -> AllocAddrs \union {NULL}])'
          OBVIOUS
        <4>8. (r \in [ProcSet -> ValDomain \union {NULL}])'
          OBVIOUS
        <4>9. (arg \in [ProcSet -> ArgDomain])'
          OBVIOUS
        <4>10. (ret \in [ProcSet -> RetDomain])'
          OBVIOUS
        <4>11. (\A p_1 \in ProcSet : (pc[p_1] # RemainderID) => arg[p_1] \in ArgsOf(LineIDtoOp(pc[p_1])))'
          <5> SUFFICES arg[p] \in ArgsOf(LineIDtoOp(pc'[p]))
            BY Zenon
          <5> QED
            BY RemDef, ZenonT(30) DEF LineIDtoOp, ArgsOf
        <4>12. AddrsOK'
          <5> SUFFICES ASSUME NEW p_1 \in ProcSet',
                              (pc[p_1] \in {"I4", "U4", "R4"})'
                       PROVE  (/\ \A q \in ProcSet : (p_1 # q => /\ newbkt[p_1] # bucket[q]
                                                                 /\ newbkt[p_1] # newbkt[q])
                               /\ \A idx \in 1..N  : (A[idx] # newbkt[p_1])
                               /\ newbkt[p_1] # bucket[p_1]
                               /\ newbkt[p_1] \in AllocAddrs)'
            BY DEF AddrsOK
          <5>1. (\A q \in ProcSet : (p_1 # q => /\ newbkt[p_1] # bucket[q]
                                                /\ newbkt[p_1] # newbkt[q]))'
            BY DEF AddrsOK
          <5>2. (\A idx \in 1..N  : (A[idx] # newbkt[p_1]))'
            BY DEF AddrsOK
          <5>3. (newbkt[p_1] # bucket[p_1])'
            BY DEF AddrsOK
          <5>4. (newbkt[p_1] \in AllocAddrs)'
            BY DEF AddrsOK
          <5>5. QED
            BY <5>1, <5>2, <5>3, <5>4
        <4>13. BktOK'
          <5> SUFFICES ASSUME NEW q \in ProcSet
                       PROVE  (/\ pc'[q] \in {"I3", "I4"} => (/\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                                                              /\ r'[q] = NULL)
                               /\ pc'[q] \in {"U3", "U4"} => (IF KeyInBktAtAddr(arg[q].key, bucket[q])'
                                                                  THEN (/\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                                                                        /\ r'[q] # NULL)
                                                                  ELSE r'[q] = NULL)
                               /\ pc'[q] \in {"R3", "R4"} => (/\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                                                              /\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                                                              /\ r'[q] # NULL))
            BY DEF BktOK
          <5>1. CASE pc'[q] \in {"I3", "I4"}
            <6> USE <5>1
            <6> SUFFICES ~KeyInBktAtAddr(arg[q].key, bucket[q])' /\ r'[q] = NULL
              OBVIOUS
            <6>1. ~KeyInBktAtAddr(arg[q].key, bucket[q]) /\ r[q] = NULL
              BY Zenon DEF BktOK
            <6> QED
              BY <6>1, Zenon DEF KeyInBktAtAddr
          <5>2. CASE pc'[q] \in {"U3", "U4"}
            <6> USE <5>2
            <6> SUFFICES IF KeyInBktAtAddr(arg[q].key, bucket[q])'
                            THEN (/\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                                  /\ r'[q] # NULL)
                            ELSE r'[q] = NULL
              OBVIOUS
            <6>1. IF KeyInBktAtAddr(arg[q].key, bucket[q])
                     THEN (/\ r[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                           /\ r[q] # NULL)
                     ELSE r[q] = NULL
              BY Zenon DEF BktOK
            <6>2. KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
              BY Zenon DEF KeyInBktAtAddr
            <6>3. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs'[bucket'[q]][CHOOSE index \in 1..Len(MemLocs'[bucket'[q]]) :
                                   MemLocs'[bucket'[q]][index].key = arg'[q].key].val
              BY DEF ValOfKeyInBktAtAddr
            <6>4. MemLocs = MemLocs' /\ arg = arg' /\ bucket[q] = bucket'[q]
              BY Zenon
            <6>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs[bucket'[q]][CHOOSE index \in 1..Len(MemLocs[bucket'[q]]) :
                                  MemLocs[bucket'[q]][index].key = arg[q].key].val
              BY Zenon, <6>3, <6>4
            <6>6. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs[bucket[q]][CHOOSE index \in 1..Len(MemLocs[bucket[q]]) :
                                 MemLocs[bucket[q]][index].key = arg[q].key].val
              BY <6>4, <6>5
            <6>7. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
              BY <6>6, Zenon DEF ValOfKeyInBktAtAddr
            <6> QED
              BY <6>1, <6>2, <6>7, Zenon
          <5>3. CASE pc'[q] \in {"R3", "R4"}
            <6> USE <5>3
            <6> SUFFICES /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                         /\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                         /\ r'[q] # NULL
              OBVIOUS
            <6>1. /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                  /\ r[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                  /\ r[q] # NULL
              BY Zenon DEF BktOK
            <6>2. KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
              BY Zenon DEF KeyInBktAtAddr
            <6>3. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs'[bucket'[q]][CHOOSE index \in 1..Len(MemLocs'[bucket'[q]]) :
                                   MemLocs'[bucket'[q]][index].key = arg'[q].key].val
              BY DEF ValOfKeyInBktAtAddr
            <6>4. MemLocs = MemLocs' /\ arg = arg' /\ bucket[q] = bucket'[q]
              BY Zenon
            <6>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs[bucket'[q]][CHOOSE index \in 1..Len(MemLocs[bucket'[q]]) :
                                  MemLocs[bucket'[q]][index].key = arg[q].key].val
              BY Zenon, <6>3, <6>4
            <6>6. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs[bucket[q]][CHOOSE index \in 1..Len(MemLocs[bucket[q]]) :
                                 MemLocs[bucket[q]][index].key = arg[q].key].val
              BY <6>4, <6>5
            <6>7. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
              BY <6>6, Zenon DEF ValOfKeyInBktAtAddr
            <6> QED
              BY <6>1, <6>2, <6>7, Zenon
          <5> QED
            BY <5>1, <5>2, <5>3
        <4>14. Uniq'
          <5> SUFFICES ASSUME NEW addr \in AllocAddrs', 
                              NEW bucket_arr, bucket_arr = MemLocs'[addr],
                              NEW j1 \in 1..Len(bucket_arr),
                              NEW j2 \in 1..Len(bucket_arr),
                              bucket_arr[j1].key = bucket_arr[j2].key
                       PROVE  j1 = j2
            BY Zenon DEF Uniq
          <5> QED
            BY Zenon DEF Uniq
        <4>15. NewBktOK'
          <5> SUFFICES ASSUME NEW q \in ProcSet
                       PROVE  /\ pc'[q] = "I4" => /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                                  /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                                                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                            /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                               (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
                              /\ pc'[q] = "U4" => /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                                  /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                                                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                            /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                               (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
                              /\ pc'[q] = "R4" => /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                            /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                               (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
            BY ZenonT(60) DEF NewBktOK
          <5>0. ASSUME NEW k \in KeyDomain
                PROVE  /\ pc[q] \in {"I4", "U4", "R4"} => KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, bucket[q])'
                       /\ KeyInBktAtAddr(k, newbkt[q]) = KeyInBktAtAddr(k, newbkt[q])'
                       /\ pc[q] \in {"I4", "U4", "R4"} => ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])'
                       /\ ValOfKeyInBktAtAddr(k, newbkt[q]) = ValOfKeyInBktAtAddr(k, newbkt[q])'
            <6> USE <5>0
            <6>1. pc[q] \in {"I4", "U4", "R4"} => KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, bucket[q])'
              BY Zenon DEF KeyInBktAtAddr
            <6>2. KeyInBktAtAddr(k, newbkt[q]) = KeyInBktAtAddr(k, newbkt[q])'
              BY Zenon DEF KeyInBktAtAddr
            <6>3. pc[q] \in {"I4", "U4", "R4"} => ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])'
              <7> SUFFICES ASSUME pc[q] \in {"I4", "U4", "R4"}
                           PROVE  ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])'
                OBVIOUS
              <7> DEFINE bkt_arr == MemLocs'[bucket'[q]]
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
              <7>1. ValOfKeyInBktAtAddr(k, bucket[q])' = bkt_arr[idx].val
                BY Zenon DEF ValOfKeyInBktAtAddr
              <7>2. bkt_arr = MemLocs[bucket[q]]
                BY Zenon
              <7>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
                BY Zenon
              <7> QED
                BY <7>1, <7>2, <7>3, Isa DEF ValOfKeyInBktAtAddr
            <6>4. ValOfKeyInBktAtAddr(k, newbkt[q]) = ValOfKeyInBktAtAddr(k, newbkt[q])'
              <7> DEFINE bkt_arr == MemLocs'[newbkt'[q]]
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
              <7>1. ValOfKeyInBktAtAddr(k, newbkt[q])' = bkt_arr[idx].val
                BY Zenon DEF ValOfKeyInBktAtAddr
              <7>2. bkt_arr = MemLocs[newbkt[q]]
                BY Zenon
              <7>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
                BY Zenon
              <7> QED
                BY <7>1, <7>2, <7>3, Isa DEF ValOfKeyInBktAtAddr
            <6> QED
              BY <6>1, <6>2, <6>3, <6>4
          <5>1. CASE pc'[q] = "I4"
            <6> USE <5>1
            <6> SUFFICES /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                         /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                         /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                   /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                      (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
              OBVIOUS
            <6>1. pc[q] = "I4" /\ arg[q].key \in KeyDomain
              BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
            <6>2. /\ KeyInBktAtAddr(arg[q].key, newbkt[q])
                  /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q]) = arg[q].val
                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                            /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                               (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
              BY <6>1, Zenon DEF NewBktOK
            <6> QED
              BY <5>0, <6>1, <6>2, ZenonT(30)
          <5>2. CASE pc'[q] = "U4"
            <6> USE <5>2
            <6> SUFFICES /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                         /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                         /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                   /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                      (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
              OBVIOUS
            <6>1. pc[q] = "U4" /\ arg[q].key \in KeyDomain
              BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
            <6>2. /\ KeyInBktAtAddr(arg[q].key, newbkt[q])
                  /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q]) = arg[q].val
                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                            /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                               (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
              BY <6>1, Zenon DEF NewBktOK
            <6> QED
              BY <5>0, <6>1, <6>2, ZenonT(30)
          <5>3. CASE pc'[q] = "R4"
            <6> USE <5>3
            <6> SUFFICES /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])'
                         /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                   /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                      (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
              OBVIOUS
            <6>1. pc[q] = "R4" /\ arg[q].key \in KeyDomain
              BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
            <6>2. /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])
                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                            /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                               (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
              BY <6>1, Zenon DEF NewBktOK
            <6> QED
              BY <5>0, <6>1, <6>2, ZenonT(30)
          <5> QED
            BY <5>1, <5>2, <5>3
        <4> QED
          BY <4>1, <4>10, <4>11, <4>12, <4>13, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, <4>14, <4>15 DEF Inv
      <3>11. CASE Line = R1(p)
        <4> USE <3>11 DEF R1
        <4>1. PTypeOK'
          BY NextPTypeOK
        <4>2. (pc \in [ProcSet -> LineIDs])'
          BY Isa DEF LineIDs
        <4>3. (A \in [1..N -> AllocAddrs \union {NULL}])'
          OBVIOUS
        <4>4. (MemLocs \in [Addrs -> Seq([key: KeyDomain, val: ValDomain])])'
          OBVIOUS
        <4>5. (AllocAddrs \in SUBSET Addrs)'
          OBVIOUS
        <4>6. (bucket \in [ProcSet -> AllocAddrs \union {NULL}])'
          <5>1. arg[p].key \in KeyDomain
            BY RemDef, Zenon DEF LineIDtoOp, ArgsOf
          <5> QED
            BY <5>1, HashDef, Zenon
        <4>7. (newbkt \in [ProcSet -> AllocAddrs \union {NULL}])'
          OBVIOUS
        <4>8. (r \in [ProcSet -> ValDomain \union {NULL}])'
          OBVIOUS
        <4>9. (arg \in [ProcSet -> ArgDomain])'
          OBVIOUS
        <4>10. (ret \in [ProcSet -> RetDomain])'
          OBVIOUS
        <4>11. (\A p_1 \in ProcSet : (pc[p_1] # RemainderID) => arg[p_1] \in ArgsOf(LineIDtoOp(pc[p_1])))'
          <5> SUFFICES arg[p] \in ArgsOf(LineIDtoOp(pc'[p]))
            BY Zenon
          <5> QED
            BY RemDef, ZenonT(30) DEF LineIDtoOp, ArgsOf
        <4>12. AddrsOK'
          <5> SUFFICES ASSUME NEW p_1 \in ProcSet',
                              (pc[p_1] \in {"I4", "U4", "R4"})'
                       PROVE  (/\ \A q \in ProcSet : (p_1 # q => /\ newbkt[p_1] # bucket[q]
                                                                 /\ newbkt[p_1] # newbkt[q])
                               /\ \A idx \in 1..N  : (A[idx] # newbkt[p_1])
                               /\ newbkt[p_1] # bucket[p_1]
                               /\ newbkt[p_1] \in AllocAddrs)'
            BY DEF AddrsOK
          <5>1. (\A q \in ProcSet : (p_1 # q => /\ newbkt[p_1] # bucket[q]
                                                /\ newbkt[p_1] # newbkt[q]))'
            <6> SUFFICES ASSUME NEW q \in ProcSet,
                                p_1 # q
                         PROVE  newbkt[p_1] # bucket'[q]
              BY ZenonT(30) DEF AddrsOK
            <6>1. CASE p = q
              <7>1. arg[p] \in [key: KeyDomain]
                BY RemDef, Zenon DEF ArgsOf, LineIDtoOp
              <7>2. Hash[arg[p].key] \in 1..N
                BY <7>1, HashDef
              <7>3. A[Hash[arg[p].key]] # newbkt[p_1]
                BY <7>2, Zenon DEF AddrsOK
              <7>4. bucket'[q] # newbkt[p_1]
                BY <6>1, <7>3, Zenon
              <7> QED
                BY <7>4
            <6>2. CASE p # q
              BY <6>2, Zenon DEF AddrsOK
            <6> QED
              BY <6>1, <6>2
          <5>2. (\A idx \in 1..N  : (A[idx] # newbkt[p_1]))'
            BY DEF AddrsOK
          <5>3. (newbkt[p_1] # bucket[p_1])'
            BY DEF AddrsOK
          <5>4. (newbkt[p_1] \in AllocAddrs)'
            BY DEF AddrsOK
          <5>5. QED
            BY <5>1, <5>2, <5>3, <5>4
        <4>13. BktOK'
          <5> SUFFICES ASSUME NEW q \in ProcSet
                       PROVE  (/\ pc'[q] \in {"I3", "I4"} => (/\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                                                              /\ r'[q] = NULL)
                               /\ pc'[q] \in {"U3", "U4"} => (IF KeyInBktAtAddr(arg[q].key, bucket[q])'
                                                                  THEN (/\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                                                                        /\ r'[q] # NULL)
                                                                  ELSE r'[q] = NULL)
                               /\ pc'[q] \in {"R3", "R4"} => (/\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                                                              /\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                                                              /\ r'[q] # NULL))
            BY DEF BktOK
          <5>1. CASE pc'[q] \in {"I3", "I4"}
            <6> USE <5>1
            <6> SUFFICES ~KeyInBktAtAddr(arg[q].key, bucket[q])' /\ r'[q] = NULL
              OBVIOUS
            <6>1. ~KeyInBktAtAddr(arg[q].key, bucket[q]) /\ r[q] = NULL
              BY Zenon DEF BktOK
            <6> QED
              BY <6>1, Zenon DEF KeyInBktAtAddr
          <5>2. CASE pc'[q] \in {"U3", "U4"}
            <6> USE <5>2
            <6> SUFFICES IF KeyInBktAtAddr(arg[q].key, bucket[q])'
                            THEN (/\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                                  /\ r'[q] # NULL)
                            ELSE r'[q] = NULL
              OBVIOUS
            <6>1. IF KeyInBktAtAddr(arg[q].key, bucket[q])
                     THEN (/\ r[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                           /\ r[q] # NULL)
                     ELSE r[q] = NULL
              BY Zenon DEF BktOK
            <6>2. KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
              BY Zenon DEF KeyInBktAtAddr
            <6>3. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs'[bucket'[q]][CHOOSE index \in 1..Len(MemLocs'[bucket'[q]]) :
                                   MemLocs'[bucket'[q]][index].key = arg'[q].key].val
              BY DEF ValOfKeyInBktAtAddr
            <6>4. MemLocs = MemLocs' /\ arg = arg' /\ bucket[q] = bucket'[q]
              BY Zenon
            <6>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs[bucket'[q]][CHOOSE index \in 1..Len(MemLocs[bucket'[q]]) :
                                  MemLocs[bucket'[q]][index].key = arg[q].key].val
              BY Zenon, <6>3, <6>4
            <6>6. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs[bucket[q]][CHOOSE index \in 1..Len(MemLocs[bucket[q]]) :
                                 MemLocs[bucket[q]][index].key = arg[q].key].val
              BY <6>4, <6>5
            <6>7. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
              BY <6>6, Zenon DEF ValOfKeyInBktAtAddr
            <6> QED
              BY <6>1, <6>2, <6>7, Zenon
          <5>3. CASE pc'[q] \in {"R3", "R4"}
            <6> USE <5>3
            <6> SUFFICES /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                         /\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                         /\ r'[q] # NULL
              OBVIOUS
            <6>1. /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                  /\ r[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                  /\ r[q] # NULL
              BY Zenon DEF BktOK
            <6>2. KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
              BY Zenon DEF KeyInBktAtAddr
            <6>3. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs'[bucket'[q]][CHOOSE index \in 1..Len(MemLocs'[bucket'[q]]) :
                                   MemLocs'[bucket'[q]][index].key = arg'[q].key].val
              BY DEF ValOfKeyInBktAtAddr
            <6>4. MemLocs = MemLocs' /\ arg = arg' /\ bucket[q] = bucket'[q]
              BY Zenon
            <6>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs[bucket'[q]][CHOOSE index \in 1..Len(MemLocs[bucket'[q]]) :
                                  MemLocs[bucket'[q]][index].key = arg[q].key].val
              BY Zenon, <6>3, <6>4
            <6>6. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs[bucket[q]][CHOOSE index \in 1..Len(MemLocs[bucket[q]]) :
                                 MemLocs[bucket[q]][index].key = arg[q].key].val
              BY <6>4, <6>5
            <6>7. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
              BY <6>6, Zenon DEF ValOfKeyInBktAtAddr
            <6> QED
              BY <6>1, <6>2, <6>7, Zenon
          <5> QED
            BY <5>1, <5>2, <5>3
        <4>14. Uniq'
          <5> SUFFICES ASSUME NEW addr \in AllocAddrs', 
                              NEW bucket_arr, bucket_arr = MemLocs'[addr],
                              NEW j1 \in 1..Len(bucket_arr),
                              NEW j2 \in 1..Len(bucket_arr),
                              bucket_arr[j1].key = bucket_arr[j2].key
                       PROVE  j1 = j2
            BY Zenon DEF Uniq
          <5> QED
            BY Zenon DEF Uniq
        <4>15. NewBktOK'
          <5> SUFFICES ASSUME NEW q \in ProcSet
                       PROVE  /\ pc'[q] = "I4" => /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                                  /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                                                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                            /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                               (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
                              /\ pc'[q] = "U4" => /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                                  /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                                                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                            /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                               (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
                              /\ pc'[q] = "R4" => /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                            /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                               (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
            BY ZenonT(60) DEF NewBktOK
          <5>0. ASSUME NEW k \in KeyDomain
                PROVE  /\ pc[q] \in {"I4", "U4", "R4"} => KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, bucket[q])'
                       /\ KeyInBktAtAddr(k, newbkt[q]) = KeyInBktAtAddr(k, newbkt[q])'
                       /\ pc[q] \in {"I4", "U4", "R4"} => ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])'
                       /\ ValOfKeyInBktAtAddr(k, newbkt[q]) = ValOfKeyInBktAtAddr(k, newbkt[q])'
            <6> USE <5>0
            <6>1. pc[q] \in {"I4", "U4", "R4"} => KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, bucket[q])'
              BY Zenon DEF KeyInBktAtAddr
            <6>2. KeyInBktAtAddr(k, newbkt[q]) = KeyInBktAtAddr(k, newbkt[q])'
              BY Zenon DEF KeyInBktAtAddr
            <6>3. pc[q] \in {"I4", "U4", "R4"} => ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])'
              <7> SUFFICES ASSUME pc[q] \in {"I4", "U4", "R4"}
                           PROVE  ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])'
                OBVIOUS
              <7> DEFINE bkt_arr == MemLocs'[bucket'[q]]
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
              <7>1. ValOfKeyInBktAtAddr(k, bucket[q])' = bkt_arr[idx].val
                BY Zenon DEF ValOfKeyInBktAtAddr
              <7>2. bkt_arr = MemLocs[bucket[q]]
                BY Zenon
              <7>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
                BY Zenon
              <7> QED
                BY <7>1, <7>2, <7>3, Isa DEF ValOfKeyInBktAtAddr
            <6>4. ValOfKeyInBktAtAddr(k, newbkt[q]) = ValOfKeyInBktAtAddr(k, newbkt[q])'
              <7> DEFINE bkt_arr == MemLocs'[newbkt'[q]]
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
              <7>1. ValOfKeyInBktAtAddr(k, newbkt[q])' = bkt_arr[idx].val
                BY Zenon DEF ValOfKeyInBktAtAddr
              <7>2. bkt_arr = MemLocs[newbkt[q]]
                BY Zenon
              <7>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
                BY Zenon
              <7> QED
                BY <7>1, <7>2, <7>3, Isa DEF ValOfKeyInBktAtAddr
            <6> QED
              BY <6>1, <6>2, <6>3, <6>4
          <5>1. CASE pc'[q] = "I4"
            <6> USE <5>1
            <6> SUFFICES /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                         /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                         /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                   /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                      (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
              OBVIOUS
            <6>1. pc[q] = "I4" /\ arg[q].key \in KeyDomain
              BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
            <6>2. /\ KeyInBktAtAddr(arg[q].key, newbkt[q])
                  /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q]) = arg[q].val
                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                            /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                               (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
              BY <6>1, Zenon DEF NewBktOK
            <6> QED
              BY <5>0, <6>1, <6>2, ZenonT(30)
          <5>2. CASE pc'[q] = "U4"
            <6> USE <5>2
            <6> SUFFICES /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                         /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                         /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                   /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                      (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
              OBVIOUS
            <6>1. pc[q] = "U4" /\ arg[q].key \in KeyDomain
              BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
            <6>2. /\ KeyInBktAtAddr(arg[q].key, newbkt[q])
                  /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q]) = arg[q].val
                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                            /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                               (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
              BY <6>1, Zenon DEF NewBktOK
            <6> QED
              BY <5>0, <6>1, <6>2, ZenonT(30)
          <5>3. CASE pc'[q] = "R4"
            <6> USE <5>3
            <6> SUFFICES /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])'
                         /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                   /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                      (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
              OBVIOUS
            <6>1. pc[q] = "R4" /\ arg[q].key \in KeyDomain
              BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
            <6>2. /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])
                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                            /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                               (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
              BY <6>1, Zenon DEF NewBktOK
            <6> QED
              BY <5>0, <6>1, <6>2, ZenonT(30)
          <5> QED
            BY <5>1, <5>2, <5>3
        <4> QED
          BY <4>1, <4>10, <4>11, <4>12, <4>13, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, <4>14, <4>15 DEF Inv
      <3>12. CASE Line = R2(p)
        <4> USE <3>12 DEF R2
        <4>1. PTypeOK'
          BY NextPTypeOK
        <4>2. (pc \in [ProcSet -> LineIDs])'
          BY Isa DEF LineIDs
        <4>3. (A \in [1..N -> AllocAddrs \union {NULL}])'
          OBVIOUS
        <4>4. (MemLocs \in [Addrs -> Seq([key: KeyDomain, val: ValDomain])])'
          OBVIOUS
        <4>5. (AllocAddrs \in SUBSET Addrs)'
          OBVIOUS
        <4>6. (bucket \in [ProcSet -> AllocAddrs \union {NULL}])'
          OBVIOUS
        <4>7. (newbkt \in [ProcSet -> AllocAddrs \union {NULL}])'
          OBVIOUS
        <4>8. (r \in [ProcSet -> ValDomain \union {NULL}])'
          <5>1. CASE bucket[p] # NULL /\ KeyInBktAtAddr(arg[p].key, bucket[p])
            <6>1. r' = [r EXCEPT ![p] = ValOfKeyInBktAtAddr(arg[p].key, bucket[p])]
              BY <5>1, Zenon
            <6>2. ValOfKeyInBktAtAddr(arg[p].key, bucket[p]) = MemLocs[bucket[p]][CHOOSE index \in 1..Len(MemLocs[bucket[p]]) : MemLocs[bucket[p]][index].key = arg[p].key].val
              BY Zenon DEF ValOfKeyInBktAtAddr
            <6>3. \E index \in 1..Len(MemLocs[bucket[p]]) : MemLocs[bucket[p]][index].key = arg[p].key
              BY <5>1, Zenon DEF KeyInBktAtAddr
            <6>4. PICK index \in 1..Len(MemLocs[bucket[p]]) : /\ MemLocs[bucket[p]][index].key = arg[p].key
                                                              /\ ValOfKeyInBktAtAddr(arg[p].key, bucket[p]) = MemLocs[bucket[p]][index].val
              BY <6>2, <6>3, Zenon
            <6>5. MemLocs[bucket[p]] \in Seq([key: KeyDomain, val: ValDomain])
              BY <5>1
            <6>6. MemLocs[bucket[p]][index] \in [key: KeyDomain, val: ValDomain]
              BY <6>4, <6>5, ElementOfSeq, Zenon
            <6>7. MemLocs[bucket[p]][index].val \in ValDomain
              BY <6>6
            <6> QED
              BY <6>1, <6>4, <6>7, Zenon
          <5>2. CASE bucket[p] = NULL \/ ~KeyInBktAtAddr(arg[p].key, bucket[p])
            BY <5>2, Zenon DEF KeyInBktAtAddr
          <5> QED
            BY <5>1, <5>2
        <4>9. (arg \in [ProcSet -> ArgDomain])'
          OBVIOUS
        <4>10. (ret \in [ProcSet -> RetDomain])'
          OBVIOUS
        <4>11. (\A p_1 \in ProcSet : (pc[p_1] # RemainderID) => arg[p_1] \in ArgsOf(LineIDtoOp(pc[p_1])))'
          <5> SUFFICES arg[p] \in ArgsOf(LineIDtoOp(pc'[p]))
            BY Zenon
          <5> QED
            BY RemDef, ZenonT(45) DEF LineIDtoOp, ArgsOf
        <4>12. AddrsOK'
          <5> SUFFICES ASSUME NEW p_1 \in ProcSet',
                              (pc[p_1] \in {"I4", "U4", "R4"})'
                       PROVE  (/\ \A q \in ProcSet : (p_1 # q => /\ newbkt[p_1] # bucket[q]
                                                                 /\ newbkt[p_1] # newbkt[q])
                               /\ \A idx \in 1..N  : (A[idx] # newbkt[p_1])
                               /\ newbkt[p_1] # bucket[p_1]
                               /\ newbkt[p_1] \in AllocAddrs)'
            BY DEF AddrsOK
          <5>1. (\A q \in ProcSet : (p_1 # q => /\ newbkt[p_1] # bucket[q]
                                                /\ newbkt[p_1] # newbkt[q]))'
            BY DEF AddrsOK
          <5>2. (\A idx \in 1..N  : (A[idx] # newbkt[p_1]))'
            BY DEF AddrsOK
          <5>3. (newbkt[p_1] # bucket[p_1])'
            BY DEF AddrsOK
          <5>4. (newbkt[p_1] \in AllocAddrs)'
            BY DEF AddrsOK
          <5>5. QED
            BY <5>1, <5>2, <5>3, <5>4
        <4>13. BktOK'
          <5> SUFFICES ASSUME NEW q \in ProcSet
                       PROVE  (/\ pc'[q] \in {"I3", "I4"} => (/\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                                                              /\ r'[q] = NULL)
                               /\ pc'[q] \in {"U3", "U4"} => (IF KeyInBktAtAddr(arg[q].key, bucket[q])'
                                                                  THEN (/\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                                                                        /\ r'[q] # NULL)
                                                                  ELSE r'[q] = NULL)
                               /\ pc'[q] \in {"R3", "R4"} => (/\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                                                              /\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                                                              /\ r'[q] # NULL))
            BY DEF BktOK
          <5>1. CASE pc'[q] \in {"I3", "I4"}
            <6> USE <5>1
            <6> SUFFICES ~KeyInBktAtAddr(arg[q].key, bucket[q])' /\ r'[q] = NULL
              OBVIOUS
            <6>1. ~KeyInBktAtAddr(arg[q].key, bucket[q]) /\ r[q] = NULL
              BY Zenon DEF BktOK
            <6> QED
              BY <6>1, Zenon DEF KeyInBktAtAddr
          <5>2. CASE pc'[q] \in {"U3", "U4"}
            <6> USE <5>2
            <6> SUFFICES IF KeyInBktAtAddr(arg[q].key, bucket[q])'
                            THEN (/\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                                  /\ r'[q] # NULL)
                            ELSE r'[q] = NULL
              OBVIOUS
            <6>1. IF KeyInBktAtAddr(arg[q].key, bucket[q])
                     THEN (/\ r[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                           /\ r[q] # NULL)
                     ELSE r[q] = NULL
              BY Zenon DEF BktOK
            <6>2. KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
              BY Zenon DEF KeyInBktAtAddr
            <6>3. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs'[bucket'[q]][CHOOSE index \in 1..Len(MemLocs'[bucket'[q]]) :
                                   MemLocs'[bucket'[q]][index].key = arg'[q].key].val
              BY DEF ValOfKeyInBktAtAddr
            <6>4. MemLocs = MemLocs' /\ arg = arg' /\ bucket[q] = bucket'[q]
              BY Zenon
            <6>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs[bucket'[q]][CHOOSE index \in 1..Len(MemLocs[bucket'[q]]) :
                                  MemLocs[bucket'[q]][index].key = arg[q].key].val
              BY Zenon, <6>3, <6>4
            <6>6. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs[bucket[q]][CHOOSE index \in 1..Len(MemLocs[bucket[q]]) :
                                 MemLocs[bucket[q]][index].key = arg[q].key].val
              BY <6>4, <6>5
            <6>7. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
              BY <6>6, Zenon DEF ValOfKeyInBktAtAddr
            <6> QED
              BY <6>1, <6>2, <6>7, Zenon
          <5>3. CASE pc'[q] \in {"R3", "R4"}
            <6> USE <5>3
            <6> SUFFICES /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                         /\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                         /\ r'[q] # NULL
              OBVIOUS
            <6>A. CASE p = q
              <7> USE <6>A
              <7>1. KeyInBktAtAddr(arg[p].key, bucket[p])
                BY <6>A, Zenon
              <7>B. KeyInBktAtAddr(arg[p].key, bucket[p])'
                BY <7>1, Zenon DEF KeyInBktAtAddr
              <7>2. r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                BY <7>1, Zenon
              <7>3. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
                MemLocs'[bucket'[q]][CHOOSE index \in 1..Len(MemLocs'[bucket'[q]]) :
                                     MemLocs'[bucket'[q]][index].key = arg'[q].key].val
                BY DEF ValOfKeyInBktAtAddr
              <7>4. MemLocs = MemLocs' /\ arg = arg' /\ bucket[q] = bucket'[q]
                BY Zenon
              <7>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
                MemLocs[bucket'[q]][CHOOSE index \in 1..Len(MemLocs[bucket'[q]]) :
                                    MemLocs[bucket'[q]][index].key = arg[q].key].val
                BY Zenon, <7>3, <7>4
              <7>6. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
                MemLocs[bucket[q]][CHOOSE index \in 1..Len(MemLocs[bucket[q]]) :
                                   MemLocs[bucket[q]][index].key = arg[q].key].val
                BY <7>4, <7>5
              <7>7. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                BY <7>6, Zenon DEF ValOfKeyInBktAtAddr
              <7>8. \E index \in 1..Len(MemLocs[bucket[p]]) : MemLocs[bucket[p]][index].key = arg[p].key
                BY <7>1, Zenon DEF KeyInBktAtAddr
              <7>9. ValOfKeyInBktAtAddr(arg[p].key, bucket[p]) = MemLocs[bucket[p]][CHOOSE index \in 1..Len(MemLocs[bucket[p]]) : MemLocs[bucket[p]][index].key = arg[p].key].val
                BY Zenon DEF ValOfKeyInBktAtAddr
              <7>10. PICK index \in 1..Len(MemLocs[bucket[p]]) : /\ MemLocs[bucket[p]][index].key = arg[p].key
                                                                 /\ ValOfKeyInBktAtAddr(arg[p].key, bucket[p]) = MemLocs[bucket[p]][index].val
                BY <7>8, <7>9, Zenon
              <7>11. MemLocs[bucket[p]] \in Seq([key: KeyDomain, val: ValDomain])
                BY <6>A, Zenon DEF KeyInBktAtAddr
              <7>12. MemLocs[bucket[p]][index] \in [key: KeyDomain, val: ValDomain]
                BY <7>10, <7>11, ElementOfSeq, Zenon
              <7>13. MemLocs[bucket[p]][index].val \in ValDomain
                BY <7>12
              <7> SUFFICES r'[q] # NULL
                BY <7>B, <7>2, <7>7
              <7> QED
                BY <7>2, <7>7, <7>10, <7>13, NULLDef
            <6> SUFFICES ASSUME p # q
                         PROVE  /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                                /\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                                /\ r'[q] # NULL
              BY <6>A
            <6>1. /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                  /\ r[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                  /\ r[q] # NULL
              BY Zenon DEF BktOK
            <6>2. KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
              BY Zenon DEF KeyInBktAtAddr
            <6>3. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs'[bucket'[q]][CHOOSE index \in 1..Len(MemLocs'[bucket'[q]]) :
                                   MemLocs'[bucket'[q]][index].key = arg'[q].key].val
              BY DEF ValOfKeyInBktAtAddr
            <6>4. MemLocs = MemLocs' /\ arg = arg' /\ bucket[q] = bucket'[q]
              BY Zenon
            <6>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs[bucket'[q]][CHOOSE index \in 1..Len(MemLocs[bucket'[q]]) :
                                  MemLocs[bucket'[q]][index].key = arg[q].key].val
              BY Zenon, <6>3, <6>4
            <6>6. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs[bucket[q]][CHOOSE index \in 1..Len(MemLocs[bucket[q]]) :
                                 MemLocs[bucket[q]][index].key = arg[q].key].val
              BY <6>4, <6>5
            <6>7. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
              BY <6>6, Zenon DEF ValOfKeyInBktAtAddr
            <6> QED
              BY <6>1, <6>2, <6>7, Zenon
          <5> QED
            BY <5>1, <5>2, <5>3
        <4>14. Uniq'
          <5> SUFFICES ASSUME NEW addr \in AllocAddrs', 
                              NEW bucket_arr, bucket_arr = MemLocs'[addr],
                              NEW j1 \in 1..Len(bucket_arr),
                              NEW j2 \in 1..Len(bucket_arr),
                              bucket_arr[j1].key = bucket_arr[j2].key
                       PROVE  j1 = j2
            BY Zenon DEF Uniq
          <5> QED
            BY Zenon DEF Uniq
        <4>15. NewBktOK'
          <5> SUFFICES ASSUME NEW q \in ProcSet
                       PROVE  /\ pc'[q] = "I4" => /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                                  /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                                                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                            /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                               (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
                              /\ pc'[q] = "U4" => /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                                  /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                                                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                            /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                               (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
                              /\ pc'[q] = "R4" => /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                            /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                               (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
            BY ZenonT(60) DEF NewBktOK
          <5>0. ASSUME NEW k \in KeyDomain
                PROVE  /\ pc[q] \in {"I4", "U4", "R4"} => KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, bucket[q])'
                       /\ KeyInBktAtAddr(k, newbkt[q]) = KeyInBktAtAddr(k, newbkt[q])'
                       /\ pc[q] \in {"I4", "U4", "R4"} => ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])'
                       /\ ValOfKeyInBktAtAddr(k, newbkt[q]) = ValOfKeyInBktAtAddr(k, newbkt[q])'
            <6> USE <5>0
            <6>1. pc[q] \in {"I4", "U4", "R4"} => KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, bucket[q])'
              BY Zenon DEF KeyInBktAtAddr
            <6>2. KeyInBktAtAddr(k, newbkt[q]) = KeyInBktAtAddr(k, newbkt[q])'
              BY Zenon DEF KeyInBktAtAddr
            <6>3. pc[q] \in {"I4", "U4", "R4"} => ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])'
              <7> SUFFICES ASSUME pc[q] \in {"I4", "U4", "R4"}
                           PROVE  ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])'
                OBVIOUS
              <7> DEFINE bkt_arr == MemLocs'[bucket'[q]]
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
              <7>1. ValOfKeyInBktAtAddr(k, bucket[q])' = bkt_arr[idx].val
                BY Zenon DEF ValOfKeyInBktAtAddr
              <7>2. bkt_arr = MemLocs[bucket[q]]
                BY Zenon
              <7>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
                BY Zenon
              <7> QED
                BY <7>1, <7>2, <7>3, Isa DEF ValOfKeyInBktAtAddr
            <6>4. ValOfKeyInBktAtAddr(k, newbkt[q]) = ValOfKeyInBktAtAddr(k, newbkt[q])'
              <7> DEFINE bkt_arr == MemLocs'[newbkt'[q]]
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
              <7>1. ValOfKeyInBktAtAddr(k, newbkt[q])' = bkt_arr[idx].val
                BY Zenon DEF ValOfKeyInBktAtAddr
              <7>2. bkt_arr = MemLocs[newbkt[q]]
                BY Zenon
              <7>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
                BY Zenon
              <7> QED
                BY <7>1, <7>2, <7>3, Isa DEF ValOfKeyInBktAtAddr
            <6> QED
              BY <6>1, <6>2, <6>3, <6>4
          <5>1. CASE pc'[q] = "I4"
            <6> USE <5>1
            <6> SUFFICES /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                         /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                         /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                   /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                      (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
              OBVIOUS
            <6>1. pc[q] = "I4" /\ arg[q].key \in KeyDomain
              BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
            <6>2. /\ KeyInBktAtAddr(arg[q].key, newbkt[q])
                  /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q]) = arg[q].val
                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                            /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                               (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
              BY <6>1, Zenon DEF NewBktOK
            <6> QED
              BY <5>0, <6>1, <6>2, ZenonT(30)
          <5>2. CASE pc'[q] = "U4"
            <6> USE <5>2
            <6> SUFFICES /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                         /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                         /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                   /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                      (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
              OBVIOUS
            <6>1. pc[q] = "U4" /\ arg[q].key \in KeyDomain
              BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
            <6>2. /\ KeyInBktAtAddr(arg[q].key, newbkt[q])
                  /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q]) = arg[q].val
                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                            /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                               (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
              BY <6>1, Zenon DEF NewBktOK
            <6> QED
              BY <5>0, <6>1, <6>2, ZenonT(30)
          <5>3. CASE pc'[q] = "R4"
            <6> USE <5>3
            <6> SUFFICES /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])'
                         /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                   /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                      (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
              OBVIOUS
            <6>1. pc[q] = "R4" /\ arg[q].key \in KeyDomain
              BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
            <6>2. /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])
                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                            /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                               (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
              BY <6>1, Zenon DEF NewBktOK
            <6> QED
              BY <5>0, <6>1, <6>2, ZenonT(30)
          <5> QED
            BY <5>1, <5>2, <5>3
        <4> QED
          BY <4>1, <4>10, <4>11, <4>12, <4>13, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, <4>14, <4>15 DEF Inv
      <3>13. CASE Line = R3(p)
        <4> USE <3>13 DEF R3
        <4>1. PTypeOK'
          BY NextPTypeOK
        <4>2. (pc \in [ProcSet -> LineIDs])'
          BY Isa DEF LineIDs
        <4>3. (A \in [1..N -> AllocAddrs \union {NULL}])'
          BY Zenon
        <4>4. (MemLocs \in [Addrs -> Seq([key: KeyDomain, val: ValDomain])])'
          <5> DEFINE idx == IdxInBktAtAddr(arg[p].key, bucket[p])
          <5> DEFINE bucket_arr == MemLocs[bucket[p]]
          <5>1. PICK addr \in Addrs : 
            /\ addr \notin AllocAddrs
            /\ AllocAddrs' = AllocAddrs \cup {addr}
            /\ newbkt' = [newbkt EXCEPT ![p] = addr]
            /\ MemLocs' = [MemLocs EXCEPT ![addr] = SubSeq(bucket_arr, 1, idx-1) \o SubSeq(bucket_arr, idx+1, Len(bucket_arr))]
            BY Zenon
          <5> SUFFICES MemLocs'[addr] \in Seq([key: KeyDomain, val: ValDomain])
            BY Zenon, <5>1
          <5> SUFFICES /\ SubSeq(bucket_arr, 1, idx-1) \in Seq([key: KeyDomain, val: ValDomain])
                       /\ SubSeq(bucket_arr, idx+1, Len(bucket_arr)) \in Seq([key: KeyDomain, val: ValDomain])
            BY ConcatProperties, Zenon, <5>1
          <5> HIDE DEF R3
          <5> SUFFICES /\ idx \in 1..Len(bucket_arr)
                       /\ \A i \in 1..Len(bucket_arr) : bucket_arr[i] \in [key: KeyDomain, val: ValDomain]
            BY SubSeqProperties
          <5>2. bucket_arr \in Seq([key: KeyDomain, val: ValDomain])
            BY Zenon, NULLDef DEF BktOK, KeyInBktAtAddr, R3
          <5>3. \A i \in 1..Len(bucket_arr) : bucket_arr[i] \in [key: KeyDomain, val: ValDomain]
            BY ElementOfSeq, Zenon, <5>2
          <5>4. idx = CHOOSE index \in 1..Len(bucket_arr) : bucket_arr[index].key = arg[p].key
            BY DEF IdxInBktAtAddr
          <5>5. \E index \in 1..Len(bucket_arr) : bucket_arr[index].key = arg[p].key
            <6>1. KeyInBktAtAddr(arg[p].key, bucket[p])
              BY Zenon DEF BktOK, R3
            <6> QED
              BY <6>1 DEF KeyInBktAtAddr
          <5> QED
            BY <5>3, <5>4, <5>5
        <4>5. (AllocAddrs \in SUBSET Addrs)'
          BY Zenon
        <4>6. (bucket \in [ProcSet -> AllocAddrs \union {NULL}])'
          BY Zenon
        <4>7. (newbkt \in [ProcSet -> AllocAddrs \union {NULL}])'
          BY Zenon
        <4>8. (r \in [ProcSet -> ValDomain \union {NULL}])'
          BY Zenon
        <4>9. (arg \in [ProcSet -> ArgDomain])'
          BY Zenon
        <4>10. (ret \in [ProcSet -> RetDomain])'
          BY Zenon
        <4>11. (\A p_1 \in ProcSet : (pc[p_1] # RemainderID) => arg[p_1] \in ArgsOf(LineIDtoOp(pc[p_1])))'
          <5> SUFFICES arg[p] \in ArgsOf(LineIDtoOp(pc'[p]))
            BY Zenon
          <5> QED
            BY RemDef, ZenonT(45) DEF LineIDtoOp, ArgsOf
        <4>12. AddrsOK'
          <5> SUFFICES ASSUME NEW p_1 \in ProcSet,
                              pc'[p_1] \in {"I4", "U4", "R4"}
                       PROVE  /\ \A q \in ProcSet : (p_1 # q => /\ newbkt'[p_1] # bucket'[q]
                                                                /\ newbkt'[p_1] # newbkt'[q])
                              /\ \A idx \in 1..N  : (A'[idx] # newbkt'[p_1])
                              /\ newbkt'[p_1] # bucket'[p_1]
                              /\ newbkt'[p_1] \in AllocAddrs'
            BY Zenon DEF AddrsOK
          <5>0. PICK addr \in Addrs : /\ addr \notin AllocAddrs
                                      /\ AllocAddrs' = AllocAddrs \cup {addr}
                                      /\ newbkt' = [newbkt EXCEPT ![p] = addr]
            BY Zenon
          <5> HIDE DEF R3
          <5>1. CASE p_1 = p
            <6>1. newbkt'[p_1] \notin AllocAddrs /\ newbkt'[p_1] # NULL
              BY <5>0, <5>1, NULLDef
            <6>2. \A q \in ProcSet : (p_1 # q => /\ newbkt'[p_1] # bucket'[q]
                                                 /\ newbkt'[p_1] # newbkt'[q])
              <7> SUFFICES ASSUME NEW q \in ProcSet,
                                  p_1 # q
                           PROVE  /\ newbkt'[p_1] # bucket'[q]
                                  /\ newbkt'[p_1] # newbkt'[q]
                OBVIOUS
              <7>1. bucket[q] \in AllocAddrs \/ bucket[q] = NULL
                OBVIOUS
              <7>2. bucket'[q] \in AllocAddrs \/ bucket'[q] = NULL
                BY <7>1, Zenon DEF R3
              <7>3. newbkt[q] \in AllocAddrs \/ newbkt[q] = NULL
                OBVIOUS
              <7>4. newbkt'[q] \in AllocAddrs \/ newbkt'[q] = NULL
                BY <5>1, <7>3, Zenon DEF R3
              <7>5. newbkt'[p_1] # bucket'[q]
                BY <5>1, <6>1, <7>2 DEF AddrsOK
              <7>6. newbkt'[p_1] # newbkt'[q]
                BY <5>1, <6>1, <7>4 DEF AddrsOK
              <7>7. QED
                BY <7>5, <7>6
            <6>3. \A idx \in 1..N  : (A'[idx] # newbkt'[p_1])
              <7> SUFFICES ASSUME NEW idx \in 1..N
                           PROVE  A'[idx] # newbkt'[p_1]
                OBVIOUS
              <7>1. A'[idx] \in AllocAddrs \/ A'[idx] = NULL
                BY <4>3, Zenon DEF R3
              <7> QED
                BY <6>1, <7>1
            <6>4. newbkt'[p_1] # bucket'[p_1]
              <7>1. bucket'[p_1] \in AllocAddrs \/ bucket'[p_1] = NULL
                BY Zenon DEF R3
              <7> QED
                BY <6>1, <7>1
            <6>5. newbkt'[p_1] \in AllocAddrs'
              BY <5>1, Zenon DEF AddrsOK, R3
            <6>6. QED
              BY <6>2, <6>3, <6>4, <6>5
          <5>2. CASE p_1 # p
            <6>1. \A q \in ProcSet : (p_1 # q => /\ newbkt'[p_1] # bucket'[q]
                                                 /\ newbkt'[p_1] # newbkt'[q])
              <7> SUFFICES ASSUME NEW q \in ProcSet,
                                  p_1 # q
                           PROVE  /\ newbkt'[p_1] # bucket'[q]
                                  /\ newbkt'[p_1] # newbkt'[q]
                BY <5>2 DEF AddrsOK
              <7>1. newbkt'[p_1] # bucket'[q]
                BY <5>2, Zenon DEF AddrsOK, R3
              <7>2. newbkt'[p_1] # newbkt'[q]
                <8>1. CASE q = p
                  <9>1. newbkt'[q] \notin AllocAddrs
                    BY <8>1, Zenon DEF R3
                  <9>2. newbkt'[p_1] \in AllocAddrs
                    BY <5>2, Zenon DEF AddrsOK, R3
                  <9> QED  
                    BY <9>1, <9>2
                <8>2. CASE q # p
                  BY <5>2, <8>2, Zenon DEF AddrsOK, R3
                <8> QED
                  BY <8>1, <8>2
              <7>3. QED
                BY <7>1, <7>2
            <6>2. \A idx \in 1..N  : (A'[idx] # newbkt'[p_1])
              BY <5>2, Zenon DEF AddrsOK, R3
            <6>3. newbkt'[p_1] # bucket'[p_1]
              BY <5>2, Zenon DEF AddrsOK, R3
            <6>4. newbkt'[p_1] \in AllocAddrs'
              BY <5>2, Zenon DEF AddrsOK, R3
            <6>5. QED
              BY <6>1, <6>2, <6>3, <6>4
          <5> QED
            BY <5>1, <5>2
        <4>13. BktOK'
          <5> SUFFICES ASSUME NEW q \in ProcSet
                       PROVE  (/\ pc'[q] \in {"I3", "I4"} => (/\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                                                              /\ r'[q] = NULL)
                               /\ pc'[q] \in {"U3", "U4"} => (IF KeyInBktAtAddr(arg[q].key, bucket[q])'
                                                                  THEN (/\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                                                                        /\ r'[q] # NULL)
                                                                  ELSE r'[q] = NULL)
                               /\ pc'[q] \in {"R3", "R4"} => (/\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                                                              /\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                                                              /\ r'[q] # NULL))
            BY DEF BktOK
          <5>0. PICK addr \in Addrs : /\ addr \notin AllocAddrs
                                      /\ AllocAddrs' = AllocAddrs \cup {addr}
                                      /\ newbkt' = [newbkt EXCEPT ![p] = addr]
                                      /\ \A a \in Addrs : a # addr => MemLocs[a] = MemLocs'[a]
            BY Zenon
          <5> HIDE DEF R3
          <5>1. CASE pc'[q] \in {"I3", "I4"}
            <6>1. KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
              <7>1. CASE bucket[q] = NULL
                <8> USE <7>1
                <8>1. KeyInBktAtAddr(arg[q].key, bucket[q]) = FALSE
                  BY DEF KeyInBktAtAddr
                <8>2. bucket'[q] = NULL
                  BY Zenon DEF R3
                <8>3. KeyInBktAtAddr(arg[q].key, bucket[q])' = FALSE
                  BY <8>2 DEF KeyInBktAtAddr
                <8> QED
                  BY <8>1, <8>3, Zenon
              <7>2. CASE bucket[q] # NULL
                <8> USE <7>2
                <8>1. KeyInBktAtAddr(arg[q].key, bucket[q]) = \E index \in 1..Len(MemLocs[bucket[q]]) : MemLocs[bucket[q]][index].key = arg[q].key
                  BY Zenon DEF KeyInBktAtAddr, R3
                <8>2. bucket'[q] = bucket[q] /\ bucket[q] \in AllocAddrs
                  BY Zenon DEF R3
                <8>3. MemLocs'[bucket[q]] = MemLocs[bucket[q]] /\ arg' = arg
                  BY <8>2, Zenon DEF R3
                <8>4. KeyInBktAtAddr(arg[q].key, bucket[q])' = \E index \in 1..Len(MemLocs'[bucket'[q]]) : MemLocs'[bucket'[q]][index].key = arg'[q].key
                  BY Zenon DEF KeyInBktAtAddr, R3
                <8>5. KeyInBktAtAddr(arg[q].key, bucket[q])' = \E index \in 1..Len(MemLocs[bucket[q]]) : MemLocs[bucket[q]][index].key = arg[q].key
                  BY <8>2, <8>3, <8>4
                <8> QED
                  BY <8>1, <8>5
              <7> QED
                BY <7>1, <7>2
            <6> USE <5>1
            <6> SUFFICES ~KeyInBktAtAddr(arg[q].key, bucket[q])' /\ r'[q] = NULL
              OBVIOUS
            <6>3. ~KeyInBktAtAddr(arg[q].key, bucket[q]) /\ r[q] = NULL
              BY Zenon DEF BktOK, R3
            <6> QED
              BY <6>3, <6>1, Zenon DEF KeyInBktAtAddr, R3
          <5>2. CASE pc'[q] \in {"U3", "U4"}
            <6> USE <5>2
            <6> SUFFICES IF KeyInBktAtAddr(arg[q].key, bucket[q])'
                            THEN (/\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                                  /\ r'[q] # NULL)
                            ELSE r'[q] = NULL
              OBVIOUS
            <6>1. IF KeyInBktAtAddr(arg[q].key, bucket[q])
                     THEN (/\ r[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                           /\ r[q] # NULL)
                     ELSE r[q] = NULL
              BY Zenon DEF BktOK, R3
            <6>2. KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
              <7>1. CASE bucket[q] = NULL
                <8> USE <7>1
                <8>1. KeyInBktAtAddr(arg[q].key, bucket[q]) = FALSE
                  BY DEF KeyInBktAtAddr
                <8>2. bucket'[q] = NULL
                  BY Zenon DEF R3
                <8>3. KeyInBktAtAddr(arg[q].key, bucket[q])' = FALSE
                  BY <8>2 DEF KeyInBktAtAddr
                <8> QED
                  BY <8>1, <8>3, Zenon
              <7>2. CASE bucket[q] # NULL
                <8> USE <7>2
                <8>1. KeyInBktAtAddr(arg[q].key, bucket[q]) = \E index \in 1..Len(MemLocs[bucket[q]]) : MemLocs[bucket[q]][index].key = arg[q].key
                  BY Zenon DEF KeyInBktAtAddr
                <8>2. bucket'[q] = bucket[q] /\ bucket[q] \in AllocAddrs
                  BY Zenon DEF R3
                <8>3. MemLocs'[bucket[q]] = MemLocs[bucket[q]] /\ arg' = arg
                  BY <8>2, Zenon DEF R3
                <8>4. KeyInBktAtAddr(arg[q].key, bucket[q])' = \E index \in 1..Len(MemLocs'[bucket'[q]]) : MemLocs'[bucket'[q]][index].key = arg'[q].key
                  BY Zenon DEF KeyInBktAtAddr, R3
                <8>5. KeyInBktAtAddr(arg[q].key, bucket[q])' = \E index \in 1..Len(MemLocs[bucket[q]]) : MemLocs[bucket[q]][index].key = arg[q].key
                  BY <8>2, <8>3, <8>4
                <8> QED
                  BY <8>1, <8>5
              <7> QED
                BY <7>1, <7>2
            <6>3. CASE KeyInBktAtAddr(arg[q].key, bucket[q])
              <7>1. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
                MemLocs'[bucket'[q]][CHOOSE index \in 1..Len(MemLocs'[bucket'[q]]) :
                                     MemLocs'[bucket'[q]][index].key = arg'[q].key].val
                BY DEF ValOfKeyInBktAtAddr
              <7>2. bucket'[q] = bucket[q] /\ bucket[q] \in AllocAddrs
                BY Zenon, <6>3 DEF KeyInBktAtAddr, R3
              <7>3. MemLocs'[bucket'[q]] = MemLocs[bucket[q]]
                BY <5>0, <7>2, Zenon DEF R3
              <7>4. arg' = arg
                BY Zenon DEF R3
              <7>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
                MemLocs[bucket[q]][CHOOSE index \in 1..Len(MemLocs[bucket[q]]) :
                                    MemLocs[bucket[q]][index].key = arg[q].key].val
                BY <7>1, <7>3, <7>4
              <7>6. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                BY <7>5, Zenon DEF ValOfKeyInBktAtAddr
              <7>7. r'[q] = r[q]
                BY Zenon DEF R3
              <7> QED
                BY <6>1, <6>2, <6>3, <7>6, <7>7
            <6>4. CASE ~KeyInBktAtAddr(arg[q].key, bucket[q])
              BY <6>1, <6>2, <6>4, Zenon DEF R3
            <6> QED
              BY <6>3, <6>4
          <5>3. CASE pc'[q] \in {"R3", "R4"}
            <6> USE <5>3
            <6> SUFFICES /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                         /\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                         /\ r'[q] # NULL
              OBVIOUS
            <6>1. /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                  /\ r[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                  /\ r[q] # NULL
              BY Zenon DEF BktOK, R3
            <6>2. MemLocs[bucket[q]] = MemLocs'[bucket'[q]]
              <7>1. bucket[q] = bucket'[q]
                BY Zenon DEF R3
              <7>2. bucket[q] \in AllocAddrs
                BY Zenon, <6>1 DEF KeyInBktAtAddr
              <7>3. bucket[q] # addr
                BY <5>0, <7>2
              <7>4. MemLocs'[bucket[q]] = MemLocs[bucket[q]]
                BY <5>0, <7>2, <7>3, Zenon
              <7> QED
                BY <7>1, <7>4
            <6>3. KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
              BY <6>2, Zenon DEF KeyInBktAtAddr, R3
            <6>4. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs'[bucket'[q]][CHOOSE index \in 1..Len(MemLocs'[bucket'[q]]) :
                                   MemLocs'[bucket'[q]][index].key = arg'[q].key].val
              BY DEF ValOfKeyInBktAtAddr
            <6>5. arg = arg'
              BY Zenon DEF R3
            <6>6. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs[bucket[q]][CHOOSE index \in 1..Len(MemLocs[bucket[q]]) :
                                   MemLocs[bucket[q]][index].key = arg'[q].key].val
              BY <6>2, <6>4
            <6>7. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs[bucket[q]][CHOOSE index \in 1..Len(MemLocs[bucket[q]]) :
                                  MemLocs[bucket[q]][index].key = arg[q].key].val
              BY Zenon, <6>6, <6>5
            <6>8. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
              BY <6>7, Zenon DEF ValOfKeyInBktAtAddr
            <6> QED
              BY <6>1, <6>3, <6>8, Zenon DEF R3
          <5> QED
            BY <5>1, <5>2, <5>3
        <4>14. Uniq'
          <5> SUFFICES ASSUME NEW a \in AllocAddrs', 
                              NEW bucket_arr, bucket_arr = MemLocs'[a],
                              NEW j1 \in 1..Len(bucket_arr),
                              NEW j2 \in 1..Len(bucket_arr),
                              bucket_arr[j1].key = bucket_arr[j2].key
                       PROVE  j1 = j2
            BY Zenon DEF Uniq
          <5> idx == IdxInBktAtAddr(arg[p].key, bucket[p])
          <5>1. PICK addr \in Addrs : /\ addr \notin AllocAddrs
                                      /\ AllocAddrs' = AllocAddrs \cup {addr}
                                      /\ MemLocs' = [MemLocs EXCEPT ![addr] = SubSeq(MemLocs[bucket[p]], 1, idx-1) \o SubSeq(MemLocs[bucket[p]], idx+1, Len(MemLocs[bucket[p]]))]
            BY Zenon
          <5>2. \A ad \in Addrs : ad # addr => MemLocs'[ad] = MemLocs[ad]
            BY <5>1, Zenon
          <5>3. CASE a # addr
            BY <5>1, <5>2, <5>3, Zenon DEF Uniq
          <5> SUFFICES ASSUME a = addr
                       PROVE  j1 = j2
            BY <5>3
          <5>4. idx = CHOOSE index \in 1..Len(MemLocs[bucket[p]]) : MemLocs[bucket[p]][index].key = arg[p].key
            BY DEF IdxInBktAtAddr
          <5>5. \E index \in 1..Len(MemLocs[bucket[p]]) : MemLocs[bucket[p]][index].key = arg[p].key
            <6>1. KeyInBktAtAddr(arg[p].key, bucket[p])
              BY Zenon DEF BktOK, R3
            <6> QED
              BY <6>1 DEF KeyInBktAtAddr
          <5>6. bucket[p] # NULL
            BY Zenon DEF BktOK, KeyInBktAtAddr, R3
          <5>7. MemLocs[bucket[p]] \in Seq([key: KeyDomain, val: ValDomain])
            BY <5>6, Zenon
          <5>8. \A i \in 1..Len(MemLocs[bucket[p]]) : MemLocs[bucket[p]][i] \in [key: KeyDomain, val: ValDomain]
            BY <5>7, ElementOfSeq, Zenon
          <5> HIDE DEF R3
          <5>9. idx \in 1..Len(MemLocs[bucket[p]])
            BY <5>4, <5>5, Zenon
          <5>10. \A i \in 1..idx-1 : MemLocs[bucket[p]][i] \in [key: KeyDomain, val: ValDomain]
            BY <5>8, <5>9
          <5>11. \A i \in idx+1..Len(MemLocs[bucket[p]]) : MemLocs[bucket[p]][i] \in [key: KeyDomain, val: ValDomain]
            BY <5>8, <5>9
          <5>12. idx \in Nat \ {0}
            BY <5>7, <5>9, LenProperties
          <5> DEFINE barr == MemLocs[bucket[p]]
          <5> DEFINE s1 == SubSeq(MemLocs[bucket[p]], 1, idx-1) 
          <5> DEFINE s2 == SubSeq(MemLocs[bucket[p]], idx+1, Len(MemLocs[bucket[p]])) 
          <5>13. /\ s1 \in Seq([key: KeyDomain, val: ValDomain])
                 /\ Len(s1) = idx-1
                 /\ \A i \in 1..idx-1 : s1[i] = barr[i]
            BY <5>9, <5>10, <5>12, SubSeqProperties
          <5>14. /\ s2 \in Seq([key: KeyDomain, val: ValDomain])
                 /\ Len(s2) = Len(barr) - idx
                 /\ \A i \in 1..Len(barr)-idx : s2[i] = barr[idx+i]
            BY <5>9, <5>11, <5>12, SubSeqProperties
          <5>15. /\ s2 \in Seq([key: KeyDomain, val: ValDomain])
                 /\ Len(s2) = Len(barr)-idx
                 /\ \A i \in idx..Len(barr)-1 : s2[i-idx+1] = barr[i+1]
            BY <5>9, <5>14, <5>12
          <5>16. /\ s1 \o s2 \in Seq([key: KeyDomain, val: ValDomain])
                 /\ Len(s1 \o s2) = Len(s1) + Len(s2)
                 /\ \A i \in 1 .. Len(s1) + Len(s2) : /\ i <= Len(s1) => (s1 \o s2)[i] = s1[i] 
                                                      /\ i > Len(s1)  => (s1 \o s2)[i] = s2[i - Len(s1)]
            BY <5>13, <5>14, ConcatProperties
          <5>17. /\ Len(s1) + Len(s2) = Len(barr)-1
                 /\ Len(s1) = idx-1
                 /\ Len(s2) = Len(barr)-idx
            BY <5>13, <5>14, <5>12, LenProperties
          <5>18. /\ s1 \o s2 \in Seq([key: KeyDomain, val: ValDomain])
                 /\ Len(s1 \o s2) = Len(barr)-1
                 /\ \A i \in 1 .. Len(barr)-1 : /\ i <= idx-1 => (s1 \o s2)[i] = s1[i] 
                                                /\ i > idx-1  => (s1 \o s2)[i] = s2[i - (idx-1)]
            BY <5>16, <5>17, Zenon
          <5>19. /\ s1 \o s2 \in Seq([key: KeyDomain, val: ValDomain])
                 /\ Len(s1 \o s2) = Len(barr)-1
                 /\ \A i \in 1 .. Len(barr)-1 : /\ i <= idx-1 => (s1 \o s2)[i] = s1[i] 
                                                /\ i > idx-1  => (s1 \o s2)[i] = s2[i-idx+1]
            BY <5>18, <5>12
          <5>20. \A i \in 1..Len(barr)-1 : i <= idx-1 => (s1 \o s2)[i] = barr[i]
            BY <5>13, <5>19, <5>12
          <5>21. \A i \in 1..Len(barr)-1 : i > idx-1 => i \in idx..Len(barr)-1
            BY <5>12, LenProperties, <5>7
          <5>22. \A i \in 1..Len(barr)-1 : i > idx-1 => s2[i-idx+1] = barr[i+1]
            BY <5>15, <5>21, Zenon
          <5>23. \A i \in 1..Len(barr)-1 : i > idx-1  => (s1 \o s2)[i] = barr[i+1]
            BY <5>19, <5>22, Zenon
          <5>24. bucket_arr = s1 \o s2 /\ Len(bucket_arr) = Len(barr)-1
            BY <5>1, <5>18, Zenon
          <5>25. CASE j1 <= idx-1 /\ j2 <= idx-1
            <6>1. (j1 \in 1..Len(barr) /\ j2 \in 1..Len(barr)) => (barr[j1].key = barr[j2].key => j1 = j2)
              BY <5>6, Zenon DEF Uniq
            <6>2. barr[j1].key = barr[j2].key => j1 = j2
              BY <6>1, <5>24
            <6>3. barr[j1] = bucket_arr[j1]
              BY <5>25, <5>20, <5>24, Zenon
            <6>4. barr[j2] = bucket_arr[j2]
              BY <5>25, <5>20, <5>24, Zenon
            <6> QED
              BY <6>2, <6>3, <6>4
          <5>26. CASE j1 <= idx-1 /\ j2 > idx-1
            <6> SUFFICES FALSE
              OBVIOUS
            <6>1. barr[j1] = bucket_arr[j1]
              BY <5>26, <5>20, <5>24, Zenon
            <6>2. barr[j2+1] = bucket_arr[j2]
              BY <5>26, <5>23, <5>24, Zenon
            <6>3. (j1 \in 1..Len(barr) /\ j2+1 \in 1..Len(barr)) => (barr[j1].key = barr[j2+1].key => j1 = j2+1)
              BY <5>6, Zenon DEF Uniq
            <6>4. barr[j1].key = barr[j2+1].key => j1 = j2+1
              BY <6>3, <5>24
            <6>5. j1 = j2+1
              BY <6>1, <6>2, <6>4
            <6> QED
              BY <5>26, <5>12, <6>5
          <5>27. CASE j1 > idx-1 /\ j2 <= idx-1
            <6> SUFFICES FALSE
              OBVIOUS
            <6>1. barr[j1+1] = bucket_arr[j1]
              BY <5>27, <5>23, <5>24, Zenon
            <6>2. barr[j2] = bucket_arr[j2]
              BY <5>27, <5>20, <5>24, Zenon
            <6>3. (j1+1 \in 1..Len(barr) /\ j2 \in 1..Len(barr)) => (barr[j1+1].key = barr[j2].key => j1+1 = j2)
              BY <5>6, Zenon DEF Uniq
            <6>4. barr[j1+1].key = barr[j2].key => j1+1 = j2
              BY <6>3, <5>24
            <6>5. j1+1 = j2
              BY <6>1, <6>2, <6>4
            <6> QED
              BY <5>27, <5>12, <6>5
          <5>28. CASE j1 > idx-1 /\ j2 > idx-1
            <6>1. (j1+1 \in 1..Len(barr) /\ j2+1 \in 1..Len(barr)) => (barr[j1+1].key = barr[j2+1].key => j1+1 = j2+1)
              BY <5>6, Zenon DEF Uniq
            <6>2. barr[j1+1].key = barr[j2+1].key => j1+1 = j2+1
              BY <6>1, <5>24
            <6>3. barr[j1+1] = bucket_arr[j1]
              BY <5>28, <5>23, <5>24, Zenon
            <6>4. barr[j2+1] = bucket_arr[j2]
              BY <5>28, <5>23, <5>24, Zenon
            <6> QED
              BY <6>2, <6>3, <6>4
          <5> QED
            BY <5>12, <5>25, <5>26, <5>27, <5>28
        <4>15. NewBktOK'
          <5> SUFFICES ASSUME NEW q \in ProcSet
                       PROVE  /\ pc'[q] = "I4" => /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                                  /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                                                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                            /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                               (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
                              /\ pc'[q] = "U4" => /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                                  /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                                                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                            /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                               (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
                              /\ pc'[q] = "R4" => /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                            /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                               (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
            BY ZenonT(60) DEF NewBktOK
          <5>1. bucket[p] # NULL
            BY Zenon DEF BktOK, KeyInBktAtAddr
          <5>2. PICK idx \in 1..Len(MemLocs[bucket[p]]) : MemLocs[bucket[p]][idx].key = arg[p].key
            BY Zenon DEF BktOK, KeyInBktAtAddr
          <5> HIDE DEF R3
          <5>3. idx = CHOOSE index \in 1..Len(MemLocs[bucket[p]]) : MemLocs[bucket[p]][index].key = arg[p].key
            BY <5>1, <5>2
          <5>4. PICK addr \in Addrs : /\ addr \notin AllocAddrs
                                      /\ AllocAddrs' = AllocAddrs \cup {addr}
                                      /\ newbkt' = [newbkt EXCEPT ![p] = addr]
                                      /\ MemLocs' = [MemLocs EXCEPT ![addr] = SubSeq(MemLocs[bucket[p]], 1, idx-1) 
                                                                              \o SubSeq(MemLocs[bucket[p]], idx+1, Len(MemLocs[bucket[p]]))]
            BY Zenon, <5>2, <5>3 DEF R3, IdxInBktAtAddr
          <5> USE <5>1, <5>2, <5>3, <5>4
          <5>5. /\ pc[p] = "R3"
                /\ pc' = [pc EXCEPT ![p] = "R4"]
                /\ UNCHANGED <<A, bucket, r, arg, ret>>
            BY Zenon DEF R3
          <5> USE <5>5
          <5>6. \A a \in Addrs : a # addr => MemLocs'[a] = MemLocs[a]
            BY ZenonT(30)
          <5>7. ASSUME NEW k \in KeyDomain, q # p, pc[q] \in {"I4", "U4", "R4"}
                PROVE  /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, bucket[q])'
                       /\ KeyInBktAtAddr(k, newbkt[q]) = KeyInBktAtAddr(k, newbkt[q])'
                       /\ KeyInBktAtAddr(k, bucket[q]) => (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])')
                       /\ KeyInBktAtAddr(k, newbkt[q]) => (ValOfKeyInBktAtAddr(k, newbkt[q]) = ValOfKeyInBktAtAddr(k, newbkt[q])')
            <6> USE <5>7
            <6>1. bucket[q] = bucket'[q] /\ newbkt'[q] = newbkt[q] /\ newbkt[q] \in AllocAddrs
              BY NULLDef, Zenon DEF AddrsOK
            <6>2. MemLocs[newbkt[q]] = MemLocs'[newbkt'[q]]
              BY <5>6, <6>1, Zenon
            <6>3. KeyInBktAtAddr(k, newbkt[q]) = KeyInBktAtAddr(k, newbkt[q])'  
              BY Zenon, <6>1, <6>2 DEF KeyInBktAtAddr
            <6>4. ValOfKeyInBktAtAddr(k, newbkt[q]) = ValOfKeyInBktAtAddr(k, newbkt[q])'
              <7> DEFINE bkt_arr == MemLocs'[newbkt'[q]]
              <7> DEFINE id == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
              <7>1. ValOfKeyInBktAtAddr(k, newbkt[q])' = bkt_arr[id].val
                BY Zenon DEF ValOfKeyInBktAtAddr
              <7>2. bkt_arr = MemLocs[newbkt[q]]
                BY Zenon, <6>2
              <7>3. id = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
                BY Zenon
              <7> QED
                BY <7>1, <7>2, <7>3, Isa DEF ValOfKeyInBktAtAddr
            <6>5. CASE bucket[q] = NULL
              BY <6>1, <6>3, <6>4, <6>5, Zenon DEF KeyInBktAtAddr
            <6> SUFFICES ASSUME bucket[q] \in AllocAddrs
                         PROVE  /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, bucket[q])'
                                /\ KeyInBktAtAddr(k, bucket[q]) => (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])')
              BY NULLDef, <6>5, <6>3, <6>4, Zenon
            <6>6. MemLocs[bucket[q]] = MemLocs'[bucket'[q]]
              BY <5>6, <6>1, Zenon
            <6>7. KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, bucket[q])'  
              BY Zenon, <6>1, <6>6 DEF KeyInBktAtAddr
            <6> SUFFICES ASSUME KeyInBktAtAddr(k, bucket[q])
                         PROVE  ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])'
              BY <6>7, Zenon
            <6>8. ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])'
              <7> DEFINE bkt_arr == MemLocs'[bucket'[q]]
              <7> DEFINE id == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
              <7>1. ValOfKeyInBktAtAddr(k, bucket[q])' = bkt_arr[id].val
                BY Zenon DEF ValOfKeyInBktAtAddr
              <7>2. bkt_arr = MemLocs[bucket[q]]
                BY Zenon, <6>6
              <7>3. id = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
                BY Zenon
              <7> QED
                BY <7>1, <7>2, <7>3, Isa DEF ValOfKeyInBktAtAddr
            <6> QED
              BY <6>8
          <5>8. CASE pc'[q] = "I4"
            <6> USE <5>8
            <6>1. /\ KeyInBktAtAddr(arg[q].key, newbkt[q])
                  /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q]) = arg[q].val
                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                            /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                               (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
              BY Zenon DEF NewBktOK
            <6>2. arg[q].key \in KeyDomain
              BY RemDef, Zenon DEF ArgsOf, LineIDtoOp
            <6> QED
              BY <5>7, <6>1, <6>2, ZenonT(30)
          <5>9. CASE pc'[q] = "U4"
            <6> USE <5>9
            <6>1. /\ KeyInBktAtAddr(arg[q].key, newbkt[q])
                  /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q]) = arg[q].val
                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                            /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                               (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
              BY Zenon DEF NewBktOK
            <6>2. arg[q].key \in KeyDomain
              BY RemDef, Zenon DEF ArgsOf, LineIDtoOp
            <6> QED
              BY <5>7, <6>1, <6>2, ZenonT(30)
          <5>10. CASE pc'[q] = "R4"
            <6> USE <5>10
            <6> SUFFICES /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])'
                         /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                   /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                      (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
              OBVIOUS
            <6>1. CASE q = p
              <7> USE <6>1
              <7> DEFINE old == MemLocs[bucket[p]]
              <7> DEFINE s1 == SubSeq(old, 1, idx-1)
              <7> DEFINE s2 == SubSeq(old, idx+1, Len(old))
              <7> DEFINE new == MemLocs'[newbkt'[p]]
              <7>1. new = s1 \o s2
                BY Zenon
              <7>2. old \in Seq([key: KeyDomain, val: ValDomain])
                BY Zenon
              <7>3. /\ Len(old) \in Nat
                    /\ \A i \in 1..Len(old) : old[i] \in [key: KeyDomain, val: ValDomain]
                BY Zenon, <7>2, ElementOfSeq, LenProperties
              <7>4. idx \in 1..Len(old)
                BY Zenon
              <7>5. \A i \in 1..idx-1 : old[i] \in [key: KeyDomain, val: ValDomain]
                <8> HIDE <5>1, <5>2, <5>3, <5>4
                <8> QED BY Z3T(30), <7>3
              <7>6. 1 \in Int /\ idx-1 \in Int
                <8> HIDE <5>1, <5>2, <5>3, <5>4 
                <8> QED BY Z3T(30)
              <7>7. /\ s1 \in Seq([key: KeyDomain, val: ValDomain])
                    /\ Len(s1) = IF 1 <= idx-1 THEN (idx-1)-1+1 ELSE 0
                    /\ \A i \in 1..(idx-1)-1+1 : s1[i] = old[1+i-1]
                BY <7>5, <7>6, SubSeqProperties, Isa
              <7>8. /\ s1 \in Seq([key: KeyDomain, val: ValDomain])
                    /\ Len(s1) = idx-1
                    /\ \A i \in 1..(idx-1) : s1[i] = old[i]
                <8> HIDE <5>1, <5>2, <5>3, <5>4, <5>10, <6>1, RemDef DEF new, old, TOK, Inv, RemDef
                <8> QED BY Z3T(30), <7>6, <7>7
              <7>9. \A i \in idx+1..Len(old) : old[i] \in [key: KeyDomain, val: ValDomain]
                <8> HIDE <5>1, <5>2, <5>3, <5>4
                <8> QED BY Z3T(30), <7>3
              <7>10. idx \in Nat \ {0}
                <8> HIDE <5>1, <5>2, <5>3, <5>4
                <8> QED BY Z3T(30), <7>2, LenProperties
              <7>11. /\ s2 \in Seq([key: KeyDomain, val: ValDomain])
                     /\ Len(s2) = Len(old) - idx
                     /\ \A i \in 1..Len(old)-idx : s2[i] = old[idx+i]
                <8> HIDE <5>1, <5>2, <5>3, <5>4
                <8> QED BY <7>9, <7>10, SubSeqProperties
              <7>12. /\ s2 \in Seq([key: KeyDomain, val: ValDomain])
                     /\ Len(s2) = Len(old)-idx
                     /\ \A i \in idx..Len(old)-1 : s2[i-idx+1] = old[i+1]
                <8> HIDE <5>1, <5>2, <5>3, <5>4
                <8> QED BY <7>10, <7>11
              <7>13. \A i \in idx+1..Len(old) : s2[i-idx] = old[i]
                <8> HIDE <5>1, <5>2, <5>3, <5>4
                <8> QED BY <7>10, <7>11, <7>12
              <7>14. /\ s1 \o s2 \in Seq([key: KeyDomain, val: ValDomain])
                     /\ Len(s1 \o s2) = Len(s1) + Len(s2)
                     /\ \A i \in 1 .. Len(s1) + Len(s2) : (s1 \o s2)[i] = IF i <= Len(s1) THEN s1[i] ELSE s2[i - Len(s1)]
                <8> HIDE <5>1, <5>2, <5>3, <5>4, <5>10, <6>1, RemDef DEF new, old, s1, s2, TOK, Inv, RemDef
                <8> QED BY <7>8, <7>12, ZenonT(30), ConcatProperties
              <7>15. /\ s1 \o s2 \in Seq([key: KeyDomain, val: ValDomain])
                     /\ Len(s1 \o s2) = Len(s1) + Len(s2)
                     /\ \A i \in 1 .. Len(s1) + Len(s2) : /\ i <= Len(s1) => (s1 \o s2)[i] = s1[i] 
                                                          /\ i > Len(s1)  => (s1 \o s2)[i] = s2[i - Len(s1)]
                <8> HIDE <5>1, <5>2, <5>3, <5>4, <5>10, <6>1, RemDef DEF s1, s2, new, old, TOK, Inv, RemDef
                <8> QED BY <7>10, <7>8, <7>12, <7>14, <7>3
              <7>16. /\ Len(s1) + Len(s2) = Len(old)-1
                     /\ Len(s1) = idx-1
                     /\ Len(s2) = Len(old)-idx
                <8> HIDE <5>1, <5>2, <5>3, <5>4, <5>10, <6>1, RemDef DEF s1, s2, new, old, TOK, Inv, RemDef
                <8> QED BY <7>10, <7>12, <7>8, LenProperties
              <7>17. /\ s1 \o s2 \in Seq([key: KeyDomain, val: ValDomain])
                     /\ Len(s1 \o s2) = Len(old)-1
                     /\ \A i \in 1 .. Len(old)-1 : /\ i <= idx-1 => (s1 \o s2)[i] = s1[i] 
                                                   /\ i > idx-1  => (s1 \o s2)[i] = s2[i - (idx-1)]
                <8> HIDE <5>1, <5>2, <5>3, <5>4, <5>10, <6>1, RemDef DEF s1, s2, new, old, TOK, Inv, RemDef
                <8> QED BY <7>15, <7>16, Zenon
              <7>18. /\ s1 \o s2 \in Seq([key: KeyDomain, val: ValDomain])
                     /\ Len(s1 \o s2) = Len(old)-1
                     /\ \A i \in 1 .. Len(old)-1 : /\ i <= idx-1 => (s1 \o s2)[i] = s1[i] 
                                                   /\ i > idx-1  => (s1 \o s2)[i] = s2[i-idx+1]
                <8> HIDE <5>1, <5>2, <5>3, <5>4, <5>10, <6>1, RemDef DEF s1, s2, new, old, TOK, Inv, RemDef
                <8> QED BY <7>17, <7>10      
              <7>19. \A i \in 1..Len(old)-1 : i <= idx-1 => (s1 \o s2)[i] = old[i]
                <8> HIDE <5>1, <5>2, <5>3, <5>4, <5>10, <6>1, RemDef DEF s1, s2, new, old, TOK, Inv, RemDef
                <8> QED BY  <7>8, <7>18, <7>10
              <7>20. \A i \in 1..Len(old)-1 : i > idx-1 => i \in idx..Len(old)-1
                <8> HIDE <5>1, <5>2, <5>3, <5>4, <5>10, <6>1, RemDef DEF s1, s2, new, old, TOK, Inv, RemDef
                <8> QED BY  <7>10, LenProperties, <7>2
              <7>21. \A i \in 1..Len(old)-1 : i > idx-1 => s2[i-idx+1] = old[i+1]
                <8> HIDE <5>1, <5>2, <5>3, <5>4, <5>10, <6>1, RemDef DEF s1, s2, new, old, TOK, Inv, RemDef
                <8> QED BY  <7>12, <7>20, Zenon
              <7>22. \A i \in 1..Len(old)-1 : i > idx-1  => (s1 \o s2)[i] = old[i+1]
                <8> HIDE <5>1, <5>2, <5>3, <5>4, <5>10, <6>1, RemDef DEF s1, s2, new, old, TOK, Inv, RemDef
                <8> QED BY  <7>18, <7>21, Zenon
              <7>23. \A j2 \in 1..Len(old) : old[idx].key = old[j2].key => idx = j2
                BY ZenonT(30) DEF Uniq
              <7>24. \A j2 \in 1..Len(old) : idx # j2 => arg[p].key # old[j2].key
                BY <7>23, <5>3, Zenon
              <7>25. \A i \in 1..Len(old)-1 : arg[p].key # new[i].key
                <8> SUFFICES ASSUME NEW i \in 1..Len(old)-1
                             PROVE  arg[p].key # new[i].key
                  BY Zenon
                <8>1. CASE i <= idx-1
                  <9>1. new[i] = old[i]
                    BY <7>19, <8>1, Zenon
                  <9>2. i # idx
                    <10> HIDE <5>1, <5>2, <5>3, <5>4, <5>10, <6>1, RemDef DEF s1, s2, new, old, TOK, Inv, RemDef
                    <10> QED  BY <7>10, <8>1
                  <9>3. arg[p].key # old[i].key
                    <10> HIDE <5>1, <5>2, <5>3, <5>4, <5>10, <6>1, RemDef DEF s1, s2, new, old, TOK, Inv, RemDef
                    <10> QED  BY <7>3, <7>24, <8>1, <9>2
                  <9> QED
                    BY <9>1, <9>3, Zenon
                <8>2. CASE i > idx-1 
                  <9>1. new[i] = old[i+1]
                    BY <7>22, <8>2, Zenon
                  <9>2. i+1 # idx
                    <10> HIDE <5>1, <5>2, <5>3, <5>4, <5>10, <6>1, RemDef DEF s1, s2, new, old, TOK, Inv, RemDef
                    <10> QED  BY <7>10, <8>2
                  <9>3. arg[p].key # old[i+1].key
                    <10> HIDE <5>1, <5>2, <5>3, <5>4, <5>10, <6>1, RemDef DEF s1, s2, new, old, TOK, Inv, RemDef
                    <10> QED  BY <7>3, <7>24, <8>2, <9>2
                  <9> QED
                    BY <9>1, <9>3, Zenon
                <8> QED
                  <9> HIDE <5>1, <5>2, <5>3, <5>4, <5>10, <6>1, RemDef DEF s1, s2, new, old, TOK, Inv, RemDef
                  <9> QED  BY <8>1, <8>2, <7>10
              <7>26. ~KeyInBktAtAddr(arg[p].key, newbkt[p])' 
                BY ZenonT(30), <7>25, <7>17 DEF KeyInBktAtAddr 
              <7>27. \A k \in KeyDomain : k # arg[p].key => /\ KeyInBktAtAddr(k, bucket[p])' = KeyInBktAtAddr(k, newbkt[p])'
                                                            /\ KeyInBktAtAddr(k, bucket[p])' =>
                                                               (ValOfKeyInBktAtAddr(k, bucket[p])' = ValOfKeyInBktAtAddr(k, newbkt[p])')
                <8> SUFFICES ASSUME NEW k \in KeyDomain,
                                    k # arg[p].key
                             PROVE  /\ KeyInBktAtAddr(k, bucket[p])' = KeyInBktAtAddr(k, newbkt[p])'
                                    /\ KeyInBktAtAddr(k, bucket[p])' =>
                                       (ValOfKeyInBktAtAddr(k, bucket[p])' = ValOfKeyInBktAtAddr(k, newbkt[p])')
                  BY Zenon
                <8>1. CASE KeyInBktAtAddr(k, bucket[p])' = FALSE
                  <9> USE <8>1
                  <9>1. \A i \in 1..Len(old) : old[i].key # k
                    BY Zenon DEF KeyInBktAtAddr
                  <9> HIDE <5>1, <5>2, <5>3, <5>4, <5>10, <6>1, RemDef DEF s1, s2, new, old, TOK, Inv, RemDef
                  <9>2. \A i \in 1..Len(old)-1 : new[i].key # k
                    <10> SUFFICES ASSUME NEW i \in 1..Len(old)-1
                                  PROVE  new[i].key # k
                      BY Zenon
                    <10>1. CASE i > idx-1
                      <11>1. new[i] = old[i+1]
                        BY <7>22, <10>1, <7>1, Zenon
                      <11>2. old[i+1].key # k
                        BY <9>1, <7>22, <7>3, <7>19, <7>10
                      <11> QED
                        BY <11>1, <11>2
                    <10>2. CASE i <= idx-1
                      <11>1. new[i] = old[i]
                        BY <7>19, <10>2, <7>1, Zenon
                      <11>2. old[i].key # k
                        BY <9>1, <7>22, <7>3, <7>19, <7>10
                      <11> QED
                        BY <11>1, <11>2
                    <10> QED
                      BY <10>1, <10>2, <7>10
                  <9>3. \A i \in 1..Len(new) : new[i].key # k
                    BY <9>2, <7>1, <7>18
                  <9> USE <5>1, <5>2, <5>3, <5>4, <5>10, <6>1, RemDef DEF s1, s2, new, old, TOK, Inv, RemDef
                  <9>4. KeyInBktAtAddr(k, newbkt[p])' = FALSE
                    BY <9>3, <5>4, Zenon DEF KeyInBktAtAddr
                  <9> QED
                    BY <8>1, <9>4, Zenon
                <8>2. CASE KeyInBktAtAddr(k, bucket[p])' = TRUE
                  <9> USE <8>2
                  <9>1. PICK i \in 1..Len(old) : old[i].key = k
                    BY ZenonT(30) DEF KeyInBktAtAddr
                  <9>2. i # idx
                    BY <5>2, <9>1, Zenon
                  <9> HIDE <5>1, <5>2, <5>3, <5>4, <5>10, <6>1, RemDef DEF s1, s2, new, old, TOK, Inv, RemDef
                  <9>3. CASE i < idx
                    <10> USE <9>3
                    <10>1. i <= idx-1
                      BY <7>10, <7>17
                    <10>2. i \in 1..Len(old)-1
                      BY <7>3, <7>4, <7>10, <7>17
                    <10>3. new[i] = old[i]
                      BY <7>1, <7>19, <10>1, <10>2, Zenon
                    <10>4. new[i].key = k
                      BY <9>1, <10>3, Zenon
                    <10> USE <5>1, <5>2, <5>3, <5>4, <5>10, <6>1, RemDef DEF s1, s2, new, old, TOK, Inv, RemDef
                    <10>5. \A j1, j2 \in 1..Len(new) : new[j1].key = new[j2].key => j1 = j2
                      BY <4>14, ZenonT(30) DEF Uniq
                    <10>6. i \in 1..Len(new)
                      BY <10>2, <7>18, Zenon
                    <10>7. \A j2 \in 1..Len(new) : new[i].key = new[j2].key => i = j2
                      BY <10>5, <10>6, Zenon
                    <10>8. \A j2 \in 1..Len(new) : i # j2 => new[i].key # new[j2].key
                      BY <10>7, Zenon
                    <10>9. \A j2 \in 1..Len(new) : i # j2 => new[j2].key # k
                      BY <10>8, <10>4, Zenon
                    <10>10. KeyInBktAtAddr(k, newbkt[p])' = TRUE
                      BY Zenon, NULLDef, <10>4, <10>6 DEF KeyInBktAtAddr
                    <10>11. \A j1, j2 \in 1..Len(old) : old[j1].key = old[j2].key => j1 = j2
                      BY ZenonT(30) DEF Uniq
                    <10>12. \A j2 \in 1..Len(old) : old[i].key = old[j2].key => i = j2
                      BY <9>1, <10>11, Zenon
                    <10>13. \A j2 \in 1..Len(old) : i # j2 => old[j2].key # old[i].key
                      BY <10>12, Zenon
                    <10>14. \A j2 \in 1..Len(old) : i # j2 => old[j2].key # k
                      BY <9>1, <10>13, Zenon
                    <10> HIDE <5>1, <5>2, <5>3, <5>4, <5>10, <6>1, RemDef DEF s1, s2, new, old, TOK, Inv, RemDef
                    <10>15. (CHOOSE index \in 1..Len(old) : old[index].key = k) = i
                      BY <9>1, <10>14
                    <10>16. (CHOOSE index \in 1..Len(new) : new[index].key = k) = i
                      BY <10>4, <10>9
                    <10> USE <5>1, <5>2, <5>3, <5>4, <5>10, <6>1, RemDef DEF s1, s2, new, old, TOK, Inv, RemDef
                    <10>17. ValOfKeyInBktAtAddr(k, bucket[p]) = old[i].val
                      BY Zenon, <10>15 DEF ValOfKeyInBktAtAddr
                    <10>18. MemLocs'[bucket'[p]] = MemLocs[bucket[p]]
                      BY ZenonT(30)
                    <10> HIDE <5>1, <5>2, <5>3, <5>4, <5>10, <6>1, RemDef DEF s1, s2, new, old, TOK, Inv, RemDef
                    <10>19. ValOfKeyInBktAtAddr(k, bucket[p])' = old[i].val
                      BY Zenon, <10>17, <10>18 DEF ValOfKeyInBktAtAddr  
                    <10> USE <5>1, <5>2, <5>3, <5>4, <5>10, <6>1, RemDef DEF s1, s2, new, old, TOK, Inv, RemDef
                    <10>20. ValOfKeyInBktAtAddr(k, newbkt[p])' = new[i].val
                      BY Zenon, <10>16 DEF ValOfKeyInBktAtAddr
                    <10>21. ValOfKeyInBktAtAddr(k, bucket[p])' = ValOfKeyInBktAtAddr(k, newbkt[p])'
                      BY Zenon, <10>3, <10>19, <10>20
                    <10> HIDE <5>1, <5>2, <5>3, <5>4, <5>10, <6>1, RemDef DEF s1, s2, new, old, TOK, Inv, RemDef
                    <10> QED
                      BY <10>10, <10>21, Zenon
                  <9>4. CASE i > idx
                    <10> USE <9>4
                    <10>1. i-1 > idx-1
                      BY <7>10, <7>17
                    <10>2. i-1 \in 1..Len(old)-1
                      BY <7>3, <7>4, <7>10, <7>17, <9>4
                    <10>3A. new[i-1] = old[i-1+1]
                      BY <7>1, <7>22, <10>1, <10>2, Zenon
                    <10>3. new[i-1] = old[i]
                      BY <10>3A
                    <10>4. new[i-1].key = k
                      BY <9>1, <10>3, Zenon
                    <10> USE <5>1, <5>2, <5>3, <5>4, <5>10, <6>1, RemDef DEF s1, s2, new, old, TOK, Inv, RemDef
                    <10>5. \A j1, j2 \in 1..Len(new) : new[j1].key = new[j2].key => j1 = j2
                      BY <4>14, ZenonT(30) DEF Uniq
                    <10>6. i-1 \in 1..Len(new)
                      BY <10>2, <7>18, Zenon
                    <10>7. \A j2 \in 1..Len(new) : new[i-1].key = new[j2].key => i-1 = j2
                      BY <10>5, <10>6, Zenon
                    <10>8. \A j2 \in 1..Len(new) : i-1 # j2 => new[i-1].key # new[j2].key
                      BY <10>7, Zenon
                    <10>9. \A j2 \in 1..Len(new) : i-1 # j2 => new[j2].key # k
                      BY <10>8, <10>4, Zenon
                    <10>10. KeyInBktAtAddr(k, newbkt[p])' = TRUE
                      BY Zenon, NULLDef, <10>4, <10>6 DEF KeyInBktAtAddr
                    <10>11. \A j1, j2 \in 1..Len(old) : old[j1].key = old[j2].key => j1 = j2
                      BY ZenonT(30) DEF Uniq
                    <10>12. \A j2 \in 1..Len(old) : old[i].key = old[j2].key => i = j2
                      BY <9>1, <10>11, Zenon
                    <10>13. \A j2 \in 1..Len(old) : i # j2 => old[j2].key # old[i].key
                      BY <10>12, Zenon
                    <10>14. \A j2 \in 1..Len(old) : i # j2 => old[j2].key # k
                      BY <9>1, <10>13, Zenon
                    <10> HIDE <5>1, <5>2, <5>3, <5>4, <5>10, <6>1, RemDef DEF s1, s2, new, old, TOK, Inv, RemDef
                    <10>15. (CHOOSE index \in 1..Len(old) : old[index].key = k) = i
                      BY <9>1, <10>14
                    <10>16. (CHOOSE index \in 1..Len(new) : new[index].key = k) = i-1
                      BY <10>4, <10>9
                    <10> USE <5>1, <5>2, <5>3, <5>4, <5>10, <6>1, RemDef DEF s1, s2, new, old, TOK, Inv, RemDef
                    <10>17. ValOfKeyInBktAtAddr(k, bucket[p]) = old[i].val
                      BY Zenon, <10>15 DEF ValOfKeyInBktAtAddr
                    <10>18. MemLocs'[bucket'[p]] = MemLocs[bucket[p]]
                      BY ZenonT(30)
                    <10> HIDE <5>1, <5>2, <5>3, <5>4, <5>10, <6>1, RemDef DEF s1, s2, new, old, TOK, Inv, RemDef
                    <10>19. ValOfKeyInBktAtAddr(k, bucket[p])' = old[i].val
                      BY Zenon, <10>17, <10>18 DEF ValOfKeyInBktAtAddr  
                    <10> USE <5>1, <5>2, <5>3, <5>4, <5>10, <6>1, RemDef DEF s1, s2, new, old, TOK, Inv, RemDef
                    <10>20. ValOfKeyInBktAtAddr(k, newbkt[p])' = new[i-1].val
                      BY Zenon, <10>16 DEF ValOfKeyInBktAtAddr
                    <10>21. ValOfKeyInBktAtAddr(k, bucket[p])' = ValOfKeyInBktAtAddr(k, newbkt[p])'
                      BY Zenon, <10>3, <10>19, <10>20
                    <10> HIDE <5>1, <5>2, <5>3, <5>4, <5>10, <6>1, RemDef DEF s1, s2, new, old, TOK, Inv, RemDef
                    <10> QED
                      BY <10>10, <10>21, Zenon
                  <9> QED
                    BY <9>2, <9>3, <9>4, <7>10
                <8> QED
                  BY <8>1, <8>2, Zenon DEF KeyInBktAtAddr
              <7> QED
                BY <7>26, <7>27, Zenon
            <6>2. CASE q # p
              <7> USE <6>2
              <7>1. /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])
                    /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                              /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                                 (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
                BY Zenon DEF NewBktOK
              <7>2. arg[q].key \in KeyDomain
                BY RemDef, Zenon DEF ArgsOf, LineIDtoOp
              <7> QED
                BY <5>7, <7>1, <7>2, ZenonT(30)
            <6> QED
              BY <6>1, <6>2, Zenon
          <5> QED
            BY <5>8, <5>9, <5>10
        <4> QED
          BY <4>1, <4>10, <4>11, <4>12, <4>13, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, <4>14, <4>15 DEF Inv
      <3>14. CASE Line = R4(p)
        <4> USE <3>14 DEF R4
        <4>1. PTypeOK'
          BY NextPTypeOK
        <4>2. (pc \in [ProcSet -> LineIDs])'
          BY Isa DEF LineIDs
        <4>3. (A \in [1..N -> AllocAddrs \union {NULL}])'
          <5>1. CASE A[Hash[arg[p].key]] = bucket[p]
            <6> SUFFICES newbkt[p] \in AllocAddrs \union {NULL}
              BY <5>1, Isa
            <6> QED
              OBVIOUS
          <5>2. CASE A[Hash[arg[p].key]] # bucket[p] 
            BY <5>2
          <5> QED
            BY <5>1, <5>2
        <4>4. (MemLocs \in [Addrs -> Seq([key: KeyDomain, val: ValDomain])])'
          OBVIOUS
        <4>5. (AllocAddrs \in SUBSET Addrs)'
          OBVIOUS
        <4>6. (bucket \in [ProcSet -> AllocAddrs \union {NULL}])'
          OBVIOUS
        <4>7. (newbkt \in [ProcSet -> AllocAddrs \union {NULL}])'
          OBVIOUS
        <4>8. (r \in [ProcSet -> ValDomain \union {NULL}])'
          OBVIOUS
        <4>9. (arg \in [ProcSet -> ArgDomain])'
          OBVIOUS
        <4>10. (ret \in [ProcSet -> RetDomain])'
          OBVIOUS
        <4>11. (\A p_1 \in ProcSet : (pc[p_1] # RemainderID) => arg[p_1] \in ArgsOf(LineIDtoOp(pc[p_1])))'
          <5> SUFFICES arg[p] \in ArgsOf(LineIDtoOp(pc'[p]))
            BY Zenon
          <5> QED
            BY RemDef, ZenonT(30) DEF LineIDtoOp, ArgsOf
        <4>12. AddrsOK'
          <5> SUFFICES ASSUME NEW p_1 \in ProcSet',
                              (pc[p_1] \in {"I4", "U4", "R4"})'
                       PROVE  (/\ \A q \in ProcSet : (p_1 # q => /\ newbkt[p_1] # bucket[q]
                                                                 /\ newbkt[p_1] # newbkt[q])
                               /\ \A idx \in 1..N  : (A[idx] # newbkt[p_1])
                               /\ newbkt[p_1] # bucket[p_1]
                               /\ newbkt[p_1] \in AllocAddrs)'
            BY DEF AddrsOK
          <5>1. (\A q \in ProcSet : (p_1 # q => /\ newbkt[p_1] # bucket[q]
                                                /\ newbkt[p_1] # newbkt[q]))'
            BY DEF AddrsOK
          <5>2. (\A idx \in 1..N  : (A[idx] # newbkt[p_1]))'
            BY DEF AddrsOK
          <5>3. (newbkt[p_1] # bucket[p_1])'
            BY DEF AddrsOK
          <5>4. (newbkt[p_1] \in AllocAddrs)'
            BY DEF AddrsOK
          <5>5. QED
            BY <5>1, <5>2, <5>3, <5>4
        <4>13. BktOK'
          <5> SUFFICES ASSUME NEW q \in ProcSet
                       PROVE  (/\ pc'[q] \in {"I3", "I4"} => (/\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                                                              /\ r'[q] = NULL)
                               /\ pc'[q] \in {"U3", "U4"} => (IF KeyInBktAtAddr(arg[q].key, bucket[q])'
                                                                  THEN (/\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                                                                        /\ r'[q] # NULL)
                                                                  ELSE r'[q] = NULL)
                               /\ pc'[q] \in {"R3", "R4"} => (/\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                                                              /\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                                                              /\ r'[q] # NULL))
            BY DEF BktOK
          <5>1. CASE pc'[q] \in {"I3", "I4"}
            <6> USE <5>1
            <6> SUFFICES ~KeyInBktAtAddr(arg[q].key, bucket[q])' /\ r'[q] = NULL
              OBVIOUS
            <6>1. ~KeyInBktAtAddr(arg[q].key, bucket[q]) /\ r[q] = NULL
              BY Zenon DEF BktOK
            <6> QED
              BY <6>1, Zenon DEF KeyInBktAtAddr
          <5>2. CASE pc'[q] \in {"U3", "U4"}
            <6> USE <5>2
            <6> SUFFICES IF KeyInBktAtAddr(arg[q].key, bucket[q])'
                            THEN (/\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                                  /\ r'[q] # NULL)
                            ELSE r'[q] = NULL
              OBVIOUS
            <6>1. IF KeyInBktAtAddr(arg[q].key, bucket[q])
                     THEN (/\ r[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                           /\ r[q] # NULL)
                     ELSE r[q] = NULL
              BY Zenon DEF BktOK
            <6>2. KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
              BY Zenon DEF KeyInBktAtAddr
            <6>3. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs'[bucket'[q]][CHOOSE index \in 1..Len(MemLocs'[bucket'[q]]) :
                                   MemLocs'[bucket'[q]][index].key = arg'[q].key].val
              BY DEF ValOfKeyInBktAtAddr
            <6>4. MemLocs = MemLocs' /\ arg = arg' /\ bucket[q] = bucket'[q]
              BY Zenon
            <6>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs[bucket'[q]][CHOOSE index \in 1..Len(MemLocs[bucket'[q]]) :
                                  MemLocs[bucket'[q]][index].key = arg[q].key].val
              BY Zenon, <6>3, <6>4
            <6>6. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs[bucket[q]][CHOOSE index \in 1..Len(MemLocs[bucket[q]]) :
                                 MemLocs[bucket[q]][index].key = arg[q].key].val
              BY <6>4, <6>5
            <6>7. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
              BY <6>6, Zenon DEF ValOfKeyInBktAtAddr
            <6> QED
              BY <6>1, <6>2, <6>7, Zenon
          <5>3. CASE pc'[q] \in {"R3", "R4"}
            <6> USE <5>3
            <6> SUFFICES /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                         /\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                         /\ r'[q] # NULL
              OBVIOUS
            <6>1. /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                  /\ r[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                  /\ r[q] # NULL
              BY Zenon DEF BktOK
            <6>2. KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
              BY Zenon DEF KeyInBktAtAddr
            <6>3. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs'[bucket'[q]][CHOOSE index \in 1..Len(MemLocs'[bucket'[q]]) :
                                   MemLocs'[bucket'[q]][index].key = arg'[q].key].val
              BY DEF ValOfKeyInBktAtAddr
            <6>4. MemLocs = MemLocs' /\ arg = arg' /\ bucket[q] = bucket'[q]
              BY Zenon
            <6>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs[bucket'[q]][CHOOSE index \in 1..Len(MemLocs[bucket'[q]]) :
                                  MemLocs[bucket'[q]][index].key = arg[q].key].val
              BY Zenon, <6>3, <6>4
            <6>6. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs[bucket[q]][CHOOSE index \in 1..Len(MemLocs[bucket[q]]) :
                                 MemLocs[bucket[q]][index].key = arg[q].key].val
              BY <6>4, <6>5
            <6>7. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
              BY <6>6, Zenon DEF ValOfKeyInBktAtAddr
            <6> QED
              BY <6>1, <6>2, <6>7, Zenon
          <5> QED
            BY <5>1, <5>2, <5>3
        <4>14. Uniq'
          <5> SUFFICES ASSUME NEW addr \in AllocAddrs', 
                              NEW bucket_arr, bucket_arr = MemLocs'[addr],
                              NEW j1 \in 1..Len(bucket_arr),
                              NEW j2 \in 1..Len(bucket_arr),
                              bucket_arr[j1].key = bucket_arr[j2].key
                       PROVE  j1 = j2
            BY Zenon DEF Uniq
          <5> QED
            BY Zenon DEF Uniq
        <4>15. NewBktOK'
          <5> SUFFICES ASSUME NEW q \in ProcSet
                       PROVE  /\ pc'[q] = "I4" => /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                                  /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                                                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                            /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                               (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
                              /\ pc'[q] = "U4" => /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                                  /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                                                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                            /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                               (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
                              /\ pc'[q] = "R4" => /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                            /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                               (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
            BY ZenonT(60) DEF NewBktOK
          <5>0. ASSUME NEW k \in KeyDomain
                PROVE  /\ pc[q] \in {"I4", "U4", "R4"} => KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, bucket[q])'
                       /\ KeyInBktAtAddr(k, newbkt[q]) = KeyInBktAtAddr(k, newbkt[q])'
                       /\ pc[q] \in {"I4", "U4", "R4"} => ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])'
                       /\ ValOfKeyInBktAtAddr(k, newbkt[q]) = ValOfKeyInBktAtAddr(k, newbkt[q])'
            <6> USE <5>0
            <6>1. pc[q] \in {"I4", "U4", "R4"} => KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, bucket[q])'
              BY Zenon DEF KeyInBktAtAddr
            <6>2. KeyInBktAtAddr(k, newbkt[q]) = KeyInBktAtAddr(k, newbkt[q])'
              BY Zenon DEF KeyInBktAtAddr
            <6>3. pc[q] \in {"I4", "U4", "R4"} => ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])'
              <7> SUFFICES ASSUME pc[q] \in {"I4", "U4", "R4"}
                           PROVE  ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])'
                OBVIOUS
              <7> DEFINE bkt_arr == MemLocs'[bucket'[q]]
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
              <7>1. ValOfKeyInBktAtAddr(k, bucket[q])' = bkt_arr[idx].val
                BY Zenon DEF ValOfKeyInBktAtAddr
              <7>2. bkt_arr = MemLocs[bucket[q]]
                BY Zenon
              <7>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
                BY Zenon
              <7> QED
                BY <7>1, <7>2, <7>3, Isa DEF ValOfKeyInBktAtAddr
            <6>4. ValOfKeyInBktAtAddr(k, newbkt[q]) = ValOfKeyInBktAtAddr(k, newbkt[q])'
              <7> DEFINE bkt_arr == MemLocs'[newbkt'[q]]
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
              <7>1. ValOfKeyInBktAtAddr(k, newbkt[q])' = bkt_arr[idx].val
                BY Zenon DEF ValOfKeyInBktAtAddr
              <7>2. bkt_arr = MemLocs[newbkt[q]]
                BY Zenon
              <7>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
                BY Zenon
              <7> QED
                BY <7>1, <7>2, <7>3, Isa DEF ValOfKeyInBktAtAddr
            <6> QED
              BY <6>1, <6>2, <6>3, <6>4
          <5>1. CASE pc'[q] = "I4"
            <6> USE <5>1
            <6> SUFFICES /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                         /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                         /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                   /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                      (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
              OBVIOUS
            <6>1. pc[q] = "I4" /\ arg[q].key \in KeyDomain
              BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
            <6>2. /\ KeyInBktAtAddr(arg[q].key, newbkt[q])
                  /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q]) = arg[q].val
                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                            /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                               (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
              BY <6>1, Zenon DEF NewBktOK
            <6> QED
              BY <5>0, <6>1, <6>2, ZenonT(30)
          <5>2. CASE pc'[q] = "U4"
            <6> USE <5>2
            <6> SUFFICES /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                         /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                         /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                   /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                      (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
              OBVIOUS
            <6>1. pc[q] = "U4" /\ arg[q].key \in KeyDomain
              BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
            <6>2. /\ KeyInBktAtAddr(arg[q].key, newbkt[q])
                  /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q]) = arg[q].val
                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                            /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                               (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
              BY <6>1, Zenon DEF NewBktOK
            <6> QED
              BY <5>0, <6>1, <6>2, ZenonT(30)
          <5>3. CASE pc'[q] = "R4"
            <6> USE <5>3
            <6> SUFFICES /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])'
                         /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                   /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                      (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
              OBVIOUS
            <6>1. pc[q] = "R4" /\ arg[q].key \in KeyDomain
              BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
            <6>2. /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])
                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                            /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                               (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
              BY <6>1, Zenon DEF NewBktOK
            <6> QED
              BY <5>0, <6>1, <6>2, ZenonT(30)
          <5> QED
            BY <5>1, <5>2, <5>3
        <4> QED
          BY <4>1, <4>10, <4>11, <4>12, <4>13, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, <4>14, <4>15 DEF Inv
      <3> QED
        BY Zenon, <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, 
                  <3>7, <3>8, <3>9, <3>10, <3>11, <3>12, <3>13, <3>14 DEF IntLines
    <2>3. ASSUME NEW p \in ProcSet, 
                 RetLine(p)
          PROVE  Inv'
      <3> SUFFICES ASSUME NEW Line \in RetLines(p), Line
                   PROVE  Inv'
        BY <2>3, Zenon DEF RetLine
      <3>1. CASE Line = F3(p)
        <4> USE <3>1, RemDef DEF F3
        <4>1. PTypeOK'
          BY NextPTypeOK
        <4>2. (pc \in [ProcSet -> LineIDs])'
          BY Isa DEF LineIDs
        <4>3. (A \in [1..N -> AllocAddrs \union {NULL}])'
          OBVIOUS
        <4>4. (MemLocs \in [Addrs -> Seq([key: KeyDomain, val: ValDomain])])'
          OBVIOUS
        <4>5. (AllocAddrs \in SUBSET Addrs)'
          OBVIOUS
        <4>6. (bucket \in [ProcSet -> AllocAddrs \union {NULL}])'
          OBVIOUS
        <4>7. (newbkt \in [ProcSet -> AllocAddrs \union {NULL}])'
          OBVIOUS
        <4>8. (r \in [ProcSet -> ValDomain \union {NULL}])'
          OBVIOUS
        <4>9. (arg \in [ProcSet -> ArgDomain])'
          OBVIOUS
        <4>10. (ret \in [ProcSet -> RetDomain])'
          BY Zenon DEF RetDomain
        <4>11. (\A p_1 \in ProcSet : (pc[p_1] # RemainderID) => arg[p_1] \in ArgsOf(LineIDtoOp(pc[p_1])))'
          <5> SUFFICES pc'[p] = RemainderID
            BY Zenon
          <5> QED
            BY Zenon
        <4>12. AddrsOK'
          <5> SUFFICES ASSUME NEW p_1 \in ProcSet',
                              (pc[p_1] \in {"I4", "U4", "R4"})'
                       PROVE  (/\ \A q \in ProcSet : (p_1 # q => /\ newbkt[p_1] # bucket[q]
                                                                 /\ newbkt[p_1] # newbkt[q])
                               /\ \A idx \in 1..N  : (A[idx] # newbkt[p_1])
                               /\ newbkt[p_1] # bucket[p_1]
                               /\ newbkt[p_1] \in AllocAddrs)'
            BY DEF AddrsOK
          <5>1. (\A q \in ProcSet : (p_1 # q => /\ newbkt[p_1] # bucket[q]
                                                /\ newbkt[p_1] # newbkt[q]))'
            BY DEF AddrsOK
          <5>2. (\A idx \in 1..N  : (A[idx] # newbkt[p_1]))'
            BY DEF AddrsOK
          <5>3. (newbkt[p_1] # bucket[p_1])'
            BY DEF AddrsOK
          <5>4. (newbkt[p_1] \in AllocAddrs)'
            BY DEF AddrsOK
          <5>5. QED
            BY <5>1, <5>2, <5>3, <5>4
        <4>13. BktOK'
          <5> SUFFICES ASSUME NEW q \in ProcSet
                       PROVE  (/\ pc'[q] \in {"I3", "I4"} => (/\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                                                              /\ r'[q] = NULL)
                               /\ pc'[q] \in {"U3", "U4"} => (IF KeyInBktAtAddr(arg[q].key, bucket[q])'
                                                                  THEN (/\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                                                                        /\ r'[q] # NULL)
                                                                  ELSE r'[q] = NULL)
                               /\ pc'[q] \in {"R3", "R4"} => (/\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                                                              /\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                                                              /\ r'[q] # NULL))
            BY DEF BktOK
          <5>1. CASE pc'[q] \in {"I3", "I4"}
            <6> USE <5>1
            <6> SUFFICES ~KeyInBktAtAddr(arg[q].key, bucket[q])' /\ r'[q] = NULL
              OBVIOUS
            <6>1. ~KeyInBktAtAddr(arg[q].key, bucket[q]) /\ r[q] = NULL
              BY Zenon DEF BktOK
            <6> QED
              BY <6>1, Zenon DEF KeyInBktAtAddr
          <5>2. CASE pc'[q] \in {"U3", "U4"}
            <6> USE <5>2
            <6> SUFFICES IF KeyInBktAtAddr(arg[q].key, bucket[q])'
                            THEN (/\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                                  /\ r'[q] # NULL)
                            ELSE r'[q] = NULL
              OBVIOUS
            <6>1. IF KeyInBktAtAddr(arg[q].key, bucket[q])
                     THEN (/\ r[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                           /\ r[q] # NULL)
                     ELSE r[q] = NULL
              BY Zenon DEF BktOK
            <6>2. KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
              BY Zenon DEF KeyInBktAtAddr
            <6>3. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs'[bucket'[q]][CHOOSE index \in 1..Len(MemLocs'[bucket'[q]]) :
                                   MemLocs'[bucket'[q]][index].key = arg'[q].key].val
              BY DEF ValOfKeyInBktAtAddr
            <6>4. MemLocs = MemLocs' /\ arg = arg' /\ bucket[q] = bucket'[q]
              BY Zenon
            <6>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs[bucket'[q]][CHOOSE index \in 1..Len(MemLocs[bucket'[q]]) :
                                  MemLocs[bucket'[q]][index].key = arg[q].key].val
              BY Zenon, <6>3, <6>4
            <6>6. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs[bucket[q]][CHOOSE index \in 1..Len(MemLocs[bucket[q]]) :
                                 MemLocs[bucket[q]][index].key = arg[q].key].val
              BY <6>4, <6>5
            <6>7. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
              BY <6>6, Zenon DEF ValOfKeyInBktAtAddr
            <6> QED
              BY <6>1, <6>2, <6>7, Zenon
          <5>3. CASE pc'[q] \in {"R3", "R4"}
            <6> USE <5>3
            <6> SUFFICES /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                         /\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                         /\ r'[q] # NULL
              OBVIOUS
            <6>1. /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                  /\ r[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                  /\ r[q] # NULL
              BY Zenon DEF BktOK
            <6>2. KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
              BY Zenon DEF KeyInBktAtAddr
            <6>3. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs'[bucket'[q]][CHOOSE index \in 1..Len(MemLocs'[bucket'[q]]) :
                                   MemLocs'[bucket'[q]][index].key = arg'[q].key].val
              BY DEF ValOfKeyInBktAtAddr
            <6>4. MemLocs = MemLocs' /\ arg = arg' /\ bucket[q] = bucket'[q]
              BY Zenon
            <6>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs[bucket'[q]][CHOOSE index \in 1..Len(MemLocs[bucket'[q]]) :
                                  MemLocs[bucket'[q]][index].key = arg[q].key].val
              BY Zenon, <6>3, <6>4
            <6>6. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs[bucket[q]][CHOOSE index \in 1..Len(MemLocs[bucket[q]]) :
                                 MemLocs[bucket[q]][index].key = arg[q].key].val
              BY <6>4, <6>5
            <6>7. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
              BY <6>6, Zenon DEF ValOfKeyInBktAtAddr
            <6> QED
              BY <6>1, <6>2, <6>7, Zenon
          <5> QED
            BY <5>1, <5>2, <5>3
        <4>14. Uniq'
          <5> SUFFICES ASSUME NEW addr \in AllocAddrs', 
                              NEW bucket_arr, bucket_arr = MemLocs'[addr],
                              NEW j1 \in 1..Len(bucket_arr),
                              NEW j2 \in 1..Len(bucket_arr),
                              bucket_arr[j1].key = bucket_arr[j2].key
                       PROVE  j1 = j2
            BY Zenon DEF Uniq
          <5> QED
            BY Zenon DEF Uniq
        <4>15. NewBktOK'
          <5> SUFFICES ASSUME NEW q \in ProcSet
                       PROVE  /\ pc'[q] = "I4" => /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                                  /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                                                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                            /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                               (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
                              /\ pc'[q] = "U4" => /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                                  /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                                                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                            /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                               (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
                              /\ pc'[q] = "R4" => /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                            /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                               (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
            BY ZenonT(60) DEF NewBktOK
          <5>0. ASSUME NEW k \in KeyDomain
                PROVE  /\ pc[q] \in {"I4", "U4", "R4"} => KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, bucket[q])'
                       /\ KeyInBktAtAddr(k, newbkt[q]) = KeyInBktAtAddr(k, newbkt[q])'
                       /\ pc[q] \in {"I4", "U4", "R4"} => ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])'
                       /\ ValOfKeyInBktAtAddr(k, newbkt[q]) = ValOfKeyInBktAtAddr(k, newbkt[q])'
            <6> USE <5>0
            <6>1. pc[q] \in {"I4", "U4", "R4"} => KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, bucket[q])'
              BY Zenon DEF KeyInBktAtAddr
            <6>2. KeyInBktAtAddr(k, newbkt[q]) = KeyInBktAtAddr(k, newbkt[q])'
              BY Zenon DEF KeyInBktAtAddr
            <6>3. pc[q] \in {"I4", "U4", "R4"} => ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])'
              <7> SUFFICES ASSUME pc[q] \in {"I4", "U4", "R4"}
                           PROVE  ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])'
                OBVIOUS
              <7> DEFINE bkt_arr == MemLocs'[bucket'[q]]
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
              <7>1. ValOfKeyInBktAtAddr(k, bucket[q])' = bkt_arr[idx].val
                BY Zenon DEF ValOfKeyInBktAtAddr
              <7>2. bkt_arr = MemLocs[bucket[q]]
                BY Zenon
              <7>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
                BY Zenon
              <7> QED
                BY <7>1, <7>2, <7>3, Isa DEF ValOfKeyInBktAtAddr
            <6>4. ValOfKeyInBktAtAddr(k, newbkt[q]) = ValOfKeyInBktAtAddr(k, newbkt[q])'
              <7> DEFINE bkt_arr == MemLocs'[newbkt'[q]]
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
              <7>1. ValOfKeyInBktAtAddr(k, newbkt[q])' = bkt_arr[idx].val
                BY Zenon DEF ValOfKeyInBktAtAddr
              <7>2. bkt_arr = MemLocs[newbkt[q]]
                BY Zenon
              <7>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
                BY Zenon
              <7> QED
                BY <7>1, <7>2, <7>3, Isa DEF ValOfKeyInBktAtAddr
            <6> QED
              BY <6>1, <6>2, <6>3, <6>4
          <5>1. CASE pc'[q] = "I4"
            <6> USE <5>1
            <6> SUFFICES /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                         /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                         /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                   /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                      (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
              OBVIOUS
            <6>1. pc[q] = "I4" /\ arg[q].key \in KeyDomain
              BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
            <6>2. /\ KeyInBktAtAddr(arg[q].key, newbkt[q])
                  /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q]) = arg[q].val
                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                            /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                               (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
              BY <6>1, Zenon DEF NewBktOK
            <6> QED
              BY <5>0, <6>1, <6>2, ZenonT(30)
          <5>2. CASE pc'[q] = "U4"
            <6> USE <5>2
            <6> SUFFICES /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                         /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                         /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                   /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                      (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
              OBVIOUS
            <6>1. pc[q] = "U4" /\ arg[q].key \in KeyDomain
              BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
            <6>2. /\ KeyInBktAtAddr(arg[q].key, newbkt[q])
                  /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q]) = arg[q].val
                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                            /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                               (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
              BY <6>1, Zenon DEF NewBktOK
            <6> QED
              BY <5>0, <6>1, <6>2, ZenonT(30)
          <5>3. CASE pc'[q] = "R4"
            <6> USE <5>3
            <6> SUFFICES /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])'
                         /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                   /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                      (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
              OBVIOUS
            <6>1. pc[q] = "R4" /\ arg[q].key \in KeyDomain
              BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
            <6>2. /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])
                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                            /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                               (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
              BY <6>1, Zenon DEF NewBktOK
            <6> QED
              BY <5>0, <6>1, <6>2, ZenonT(30)
          <5> QED
            BY <5>1, <5>2, <5>3
        <4> QED
          BY <4>1, <4>10, <4>11, <4>12, <4>13, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, <4>14, <4>15 DEF Inv
      <3>2. CASE Line = I5(p)
        <4> USE <3>2, RemDef DEF I5
        <4>1. PTypeOK'
          BY NextPTypeOK
        <4>2. (pc \in [ProcSet -> LineIDs])'
          BY Isa DEF LineIDs
        <4>3. (A \in [1..N -> AllocAddrs \union {NULL}])'
          OBVIOUS
        <4>4. (MemLocs \in [Addrs -> Seq([key: KeyDomain, val: ValDomain])])'
          OBVIOUS
        <4>5. (AllocAddrs \in SUBSET Addrs)'
          OBVIOUS
        <4>6. (bucket \in [ProcSet -> AllocAddrs \union {NULL}])'
          OBVIOUS
        <4>7. (newbkt \in [ProcSet -> AllocAddrs \union {NULL}])'
          OBVIOUS
        <4>8. (r \in [ProcSet -> ValDomain \union {NULL}])'
          OBVIOUS
        <4>9. (arg \in [ProcSet -> ArgDomain])'
          OBVIOUS
        <4>10. (ret \in [ProcSet -> RetDomain])'
          BY Zenon DEF RetDomain
        <4>11. (\A p_1 \in ProcSet : (pc[p_1] # RemainderID) => arg[p_1] \in ArgsOf(LineIDtoOp(pc[p_1])))'
          <5> SUFFICES pc'[p] = RemainderID
            BY Zenon
          <5> QED
            BY Zenon
        <4>12. AddrsOK'
          <5> SUFFICES ASSUME NEW p_1 \in ProcSet',
                              (pc[p_1] \in {"I4", "U4", "R4"})'
                       PROVE  (/\ \A q \in ProcSet : (p_1 # q => /\ newbkt[p_1] # bucket[q]
                                                                 /\ newbkt[p_1] # newbkt[q])
                               /\ \A idx \in 1..N  : (A[idx] # newbkt[p_1])
                               /\ newbkt[p_1] # bucket[p_1]
                               /\ newbkt[p_1] \in AllocAddrs)'
            BY DEF AddrsOK
          <5>1. (\A q \in ProcSet : (p_1 # q => /\ newbkt[p_1] # bucket[q]
                                                /\ newbkt[p_1] # newbkt[q]))'
            BY DEF AddrsOK
          <5>2. (\A idx \in 1..N  : (A[idx] # newbkt[p_1]))'
            BY DEF AddrsOK
          <5>3. (newbkt[p_1] # bucket[p_1])'
            BY DEF AddrsOK
          <5>4. (newbkt[p_1] \in AllocAddrs)'
            BY DEF AddrsOK
          <5>5. QED
            BY <5>1, <5>2, <5>3, <5>4
        <4>13. BktOK'
          <5> SUFFICES ASSUME NEW q \in ProcSet
                       PROVE  (/\ pc'[q] \in {"I3", "I4"} => (/\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                                                              /\ r'[q] = NULL)
                               /\ pc'[q] \in {"U3", "U4"} => (IF KeyInBktAtAddr(arg[q].key, bucket[q])'
                                                                  THEN (/\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                                                                        /\ r'[q] # NULL)
                                                                  ELSE r'[q] = NULL)
                               /\ pc'[q] \in {"R3", "R4"} => (/\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                                                              /\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                                                              /\ r'[q] # NULL))
            BY DEF BktOK
          <5>1. CASE pc'[q] \in {"I3", "I4"}
            <6> USE <5>1
            <6> SUFFICES ~KeyInBktAtAddr(arg[q].key, bucket[q])' /\ r'[q] = NULL
              OBVIOUS
            <6>1. ~KeyInBktAtAddr(arg[q].key, bucket[q]) /\ r[q] = NULL
              BY Zenon DEF BktOK
            <6> QED
              BY <6>1, Zenon DEF KeyInBktAtAddr
          <5>2. CASE pc'[q] \in {"U3", "U4"}
            <6> USE <5>2
            <6> SUFFICES IF KeyInBktAtAddr(arg[q].key, bucket[q])'
                            THEN (/\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                                  /\ r'[q] # NULL)
                            ELSE r'[q] = NULL
              OBVIOUS
            <6>1. IF KeyInBktAtAddr(arg[q].key, bucket[q])
                     THEN (/\ r[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                           /\ r[q] # NULL)
                     ELSE r[q] = NULL
              BY Zenon DEF BktOK
            <6>2. KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
              BY Zenon DEF KeyInBktAtAddr
            <6>3. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs'[bucket'[q]][CHOOSE index \in 1..Len(MemLocs'[bucket'[q]]) :
                                   MemLocs'[bucket'[q]][index].key = arg'[q].key].val
              BY DEF ValOfKeyInBktAtAddr
            <6>4. MemLocs = MemLocs' /\ arg = arg' /\ bucket[q] = bucket'[q]
              BY Zenon
            <6>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs[bucket'[q]][CHOOSE index \in 1..Len(MemLocs[bucket'[q]]) :
                                  MemLocs[bucket'[q]][index].key = arg[q].key].val
              BY Zenon, <6>3, <6>4
            <6>6. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs[bucket[q]][CHOOSE index \in 1..Len(MemLocs[bucket[q]]) :
                                 MemLocs[bucket[q]][index].key = arg[q].key].val
              BY <6>4, <6>5
            <6>7. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
              BY <6>6, Zenon DEF ValOfKeyInBktAtAddr
            <6> QED
              BY <6>1, <6>2, <6>7, Zenon
          <5>3. CASE pc'[q] \in {"R3", "R4"}
            <6> USE <5>3
            <6> SUFFICES /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                         /\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                         /\ r'[q] # NULL
              OBVIOUS
            <6>1. /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                  /\ r[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                  /\ r[q] # NULL
              BY Zenon DEF BktOK
            <6>2. KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
              BY Zenon DEF KeyInBktAtAddr
            <6>3. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs'[bucket'[q]][CHOOSE index \in 1..Len(MemLocs'[bucket'[q]]) :
                                   MemLocs'[bucket'[q]][index].key = arg'[q].key].val
              BY DEF ValOfKeyInBktAtAddr
            <6>4. MemLocs = MemLocs' /\ arg = arg' /\ bucket[q] = bucket'[q]
              BY Zenon
            <6>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs[bucket'[q]][CHOOSE index \in 1..Len(MemLocs[bucket'[q]]) :
                                  MemLocs[bucket'[q]][index].key = arg[q].key].val
              BY Zenon, <6>3, <6>4
            <6>6. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs[bucket[q]][CHOOSE index \in 1..Len(MemLocs[bucket[q]]) :
                                 MemLocs[bucket[q]][index].key = arg[q].key].val
              BY <6>4, <6>5
            <6>7. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
              BY <6>6, Zenon DEF ValOfKeyInBktAtAddr
            <6> QED
              BY <6>1, <6>2, <6>7, Zenon
          <5> QED
            BY <5>1, <5>2, <5>3
        <4>14. Uniq'
          <5> SUFFICES ASSUME NEW addr \in AllocAddrs', 
                              NEW bucket_arr, bucket_arr = MemLocs'[addr],
                              NEW j1 \in 1..Len(bucket_arr),
                              NEW j2 \in 1..Len(bucket_arr),
                              bucket_arr[j1].key = bucket_arr[j2].key
                       PROVE  j1 = j2
            BY Zenon DEF Uniq
          <5> QED
            BY Zenon DEF Uniq
        <4>15. NewBktOK'
          <5> SUFFICES ASSUME NEW q \in ProcSet
                       PROVE  /\ pc'[q] = "I4" => /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                                  /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                                                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                            /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                               (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
                              /\ pc'[q] = "U4" => /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                                  /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                                                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                            /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                               (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
                              /\ pc'[q] = "R4" => /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                            /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                               (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
            BY ZenonT(60) DEF NewBktOK
          <5>0. ASSUME NEW k \in KeyDomain
                PROVE  /\ pc[q] \in {"I4", "U4", "R4"} => KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, bucket[q])'
                       /\ KeyInBktAtAddr(k, newbkt[q]) = KeyInBktAtAddr(k, newbkt[q])'
                       /\ pc[q] \in {"I4", "U4", "R4"} => ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])'
                       /\ ValOfKeyInBktAtAddr(k, newbkt[q]) = ValOfKeyInBktAtAddr(k, newbkt[q])'
            <6> USE <5>0
            <6>1. pc[q] \in {"I4", "U4", "R4"} => KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, bucket[q])'
              BY Zenon DEF KeyInBktAtAddr
            <6>2. KeyInBktAtAddr(k, newbkt[q]) = KeyInBktAtAddr(k, newbkt[q])'
              BY Zenon DEF KeyInBktAtAddr
            <6>3. pc[q] \in {"I4", "U4", "R4"} => ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])'
              <7> SUFFICES ASSUME pc[q] \in {"I4", "U4", "R4"}
                           PROVE  ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])'
                OBVIOUS
              <7> DEFINE bkt_arr == MemLocs'[bucket'[q]]
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
              <7>1. ValOfKeyInBktAtAddr(k, bucket[q])' = bkt_arr[idx].val
                BY Zenon DEF ValOfKeyInBktAtAddr
              <7>2. bkt_arr = MemLocs[bucket[q]]
                BY Zenon
              <7>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
                BY Zenon
              <7> QED
                BY <7>1, <7>2, <7>3, Isa DEF ValOfKeyInBktAtAddr
            <6>4. ValOfKeyInBktAtAddr(k, newbkt[q]) = ValOfKeyInBktAtAddr(k, newbkt[q])'
              <7> DEFINE bkt_arr == MemLocs'[newbkt'[q]]
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
              <7>1. ValOfKeyInBktAtAddr(k, newbkt[q])' = bkt_arr[idx].val
                BY Zenon DEF ValOfKeyInBktAtAddr
              <7>2. bkt_arr = MemLocs[newbkt[q]]
                BY Zenon
              <7>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
                BY Zenon
              <7> QED
                BY <7>1, <7>2, <7>3, Isa DEF ValOfKeyInBktAtAddr
            <6> QED
              BY <6>1, <6>2, <6>3, <6>4
          <5>1. CASE pc'[q] = "I4"
            <6> USE <5>1
            <6> SUFFICES /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                         /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                         /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                   /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                      (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
              OBVIOUS
            <6>1. pc[q] = "I4" /\ arg[q].key \in KeyDomain
              BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
            <6>2. /\ KeyInBktAtAddr(arg[q].key, newbkt[q])
                  /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q]) = arg[q].val
                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                            /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                               (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
              BY <6>1, Zenon DEF NewBktOK
            <6> QED
              BY <5>0, <6>1, <6>2, ZenonT(30)
          <5>2. CASE pc'[q] = "U4"
            <6> USE <5>2
            <6> SUFFICES /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                         /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                         /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                   /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                      (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
              OBVIOUS
            <6>1. pc[q] = "U4" /\ arg[q].key \in KeyDomain
              BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
            <6>2. /\ KeyInBktAtAddr(arg[q].key, newbkt[q])
                  /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q]) = arg[q].val
                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                            /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                               (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
              BY <6>1, Zenon DEF NewBktOK
            <6> QED
              BY <5>0, <6>1, <6>2, ZenonT(30)
          <5>3. CASE pc'[q] = "R4"
            <6> USE <5>3
            <6> SUFFICES /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])'
                         /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                   /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                      (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
              OBVIOUS
            <6>1. pc[q] = "R4" /\ arg[q].key \in KeyDomain
              BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
            <6>2. /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])
                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                            /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                               (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
              BY <6>1, Zenon DEF NewBktOK
            <6> QED
              BY <5>0, <6>1, <6>2, ZenonT(30)
          <5> QED
            BY <5>1, <5>2, <5>3
        <4> QED
          BY <4>1, <4>10, <4>11, <4>12, <4>13, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, <4>14, <4>15 DEF Inv
      <3>3. CASE Line = U5(p)
        <4> USE <3>3, RemDef DEF U5
        <4>1. PTypeOK'
          BY NextPTypeOK
        <4>2. (pc \in [ProcSet -> LineIDs])'
          BY Isa DEF LineIDs
        <4>3. (A \in [1..N -> AllocAddrs \union {NULL}])'
          OBVIOUS
        <4>4. (MemLocs \in [Addrs -> Seq([key: KeyDomain, val: ValDomain])])'
          OBVIOUS
        <4>5. (AllocAddrs \in SUBSET Addrs)'
          OBVIOUS
        <4>6. (bucket \in [ProcSet -> AllocAddrs \union {NULL}])'
          OBVIOUS
        <4>7. (newbkt \in [ProcSet -> AllocAddrs \union {NULL}])'
          OBVIOUS
        <4>8. (r \in [ProcSet -> ValDomain \union {NULL}])'
          OBVIOUS
        <4>9. (arg \in [ProcSet -> ArgDomain])'
          OBVIOUS
        <4>10. (ret \in [ProcSet -> RetDomain])'
          BY Zenon DEF RetDomain
        <4>11. (\A p_1 \in ProcSet : (pc[p_1] # RemainderID) => arg[p_1] \in ArgsOf(LineIDtoOp(pc[p_1])))'
          <5> SUFFICES pc'[p] = RemainderID
            BY Zenon
          <5> QED
            BY Zenon
        <4>12. AddrsOK'
          <5> SUFFICES ASSUME NEW p_1 \in ProcSet',
                              (pc[p_1] \in {"I4", "U4", "R4"})'
                       PROVE  (/\ \A q \in ProcSet : (p_1 # q => /\ newbkt[p_1] # bucket[q]
                                                                 /\ newbkt[p_1] # newbkt[q])
                               /\ \A idx \in 1..N  : (A[idx] # newbkt[p_1])
                               /\ newbkt[p_1] # bucket[p_1]
                               /\ newbkt[p_1] \in AllocAddrs)'
            BY DEF AddrsOK
          <5>1. (\A q \in ProcSet : (p_1 # q => /\ newbkt[p_1] # bucket[q]
                                                /\ newbkt[p_1] # newbkt[q]))'
            BY DEF AddrsOK
          <5>2. (\A idx \in 1..N  : (A[idx] # newbkt[p_1]))'
            BY DEF AddrsOK
          <5>3. (newbkt[p_1] # bucket[p_1])'
            BY DEF AddrsOK
          <5>4. (newbkt[p_1] \in AllocAddrs)'
            BY DEF AddrsOK
          <5>5. QED
            BY <5>1, <5>2, <5>3, <5>4
        <4>13. BktOK'
          <5> SUFFICES ASSUME NEW q \in ProcSet
                       PROVE  (/\ pc'[q] \in {"I3", "I4"} => (/\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                                                              /\ r'[q] = NULL)
                               /\ pc'[q] \in {"U3", "U4"} => (IF KeyInBktAtAddr(arg[q].key, bucket[q])'
                                                                  THEN (/\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                                                                        /\ r'[q] # NULL)
                                                                  ELSE r'[q] = NULL)
                               /\ pc'[q] \in {"R3", "R4"} => (/\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                                                              /\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                                                              /\ r'[q] # NULL))
            BY DEF BktOK
          <5>1. CASE pc'[q] \in {"I3", "I4"}
            <6> USE <5>1
            <6> SUFFICES ~KeyInBktAtAddr(arg[q].key, bucket[q])' /\ r'[q] = NULL
              OBVIOUS
            <6>1. ~KeyInBktAtAddr(arg[q].key, bucket[q]) /\ r[q] = NULL
              BY Zenon DEF BktOK
            <6> QED
              BY <6>1, Zenon DEF KeyInBktAtAddr
          <5>2. CASE pc'[q] \in {"U3", "U4"}
            <6> USE <5>2
            <6> SUFFICES IF KeyInBktAtAddr(arg[q].key, bucket[q])'
                            THEN (/\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                                  /\ r'[q] # NULL)
                            ELSE r'[q] = NULL
              OBVIOUS
            <6>1. IF KeyInBktAtAddr(arg[q].key, bucket[q])
                     THEN (/\ r[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                           /\ r[q] # NULL)
                     ELSE r[q] = NULL
              BY Zenon DEF BktOK
            <6>2. KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
              BY Zenon DEF KeyInBktAtAddr
            <6>3. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs'[bucket'[q]][CHOOSE index \in 1..Len(MemLocs'[bucket'[q]]) :
                                   MemLocs'[bucket'[q]][index].key = arg'[q].key].val
              BY DEF ValOfKeyInBktAtAddr
            <6>4. MemLocs = MemLocs' /\ arg = arg' /\ bucket[q] = bucket'[q]
              BY Zenon
            <6>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs[bucket'[q]][CHOOSE index \in 1..Len(MemLocs[bucket'[q]]) :
                                  MemLocs[bucket'[q]][index].key = arg[q].key].val
              BY Zenon, <6>3, <6>4
            <6>6. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs[bucket[q]][CHOOSE index \in 1..Len(MemLocs[bucket[q]]) :
                                 MemLocs[bucket[q]][index].key = arg[q].key].val
              BY <6>4, <6>5
            <6>7. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
              BY <6>6, Zenon DEF ValOfKeyInBktAtAddr
            <6> QED
              BY <6>1, <6>2, <6>7, Zenon
          <5>3. CASE pc'[q] \in {"R3", "R4"}
            <6> USE <5>3
            <6> SUFFICES /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                         /\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                         /\ r'[q] # NULL
              OBVIOUS
            <6>1. /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                  /\ r[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                  /\ r[q] # NULL
              BY Zenon DEF BktOK
            <6>2. KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
              BY Zenon DEF KeyInBktAtAddr
            <6>3. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs'[bucket'[q]][CHOOSE index \in 1..Len(MemLocs'[bucket'[q]]) :
                                   MemLocs'[bucket'[q]][index].key = arg'[q].key].val
              BY DEF ValOfKeyInBktAtAddr
            <6>4. MemLocs = MemLocs' /\ arg = arg' /\ bucket[q] = bucket'[q]
              BY Zenon
            <6>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs[bucket'[q]][CHOOSE index \in 1..Len(MemLocs[bucket'[q]]) :
                                  MemLocs[bucket'[q]][index].key = arg[q].key].val
              BY Zenon, <6>3, <6>4
            <6>6. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs[bucket[q]][CHOOSE index \in 1..Len(MemLocs[bucket[q]]) :
                                 MemLocs[bucket[q]][index].key = arg[q].key].val
              BY <6>4, <6>5
            <6>7. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
              BY <6>6, Zenon DEF ValOfKeyInBktAtAddr
            <6> QED
              BY <6>1, <6>2, <6>7, Zenon
          <5> QED
            BY <5>1, <5>2, <5>3
        <4>14. Uniq'
          <5> SUFFICES ASSUME NEW addr \in AllocAddrs', 
                              NEW bucket_arr, bucket_arr = MemLocs'[addr],
                              NEW j1 \in 1..Len(bucket_arr),
                              NEW j2 \in 1..Len(bucket_arr),
                              bucket_arr[j1].key = bucket_arr[j2].key
                       PROVE  j1 = j2
            BY Zenon DEF Uniq
          <5> QED
            BY Zenon DEF Uniq
        <4>15. NewBktOK'
          <5> SUFFICES ASSUME NEW q \in ProcSet
                       PROVE  /\ pc'[q] = "I4" => /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                                  /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                                                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                            /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                               (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
                              /\ pc'[q] = "U4" => /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                                  /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                                                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                            /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                               (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
                              /\ pc'[q] = "R4" => /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                            /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                               (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
            BY ZenonT(60) DEF NewBktOK
          <5>0. ASSUME NEW k \in KeyDomain
                PROVE  /\ pc[q] \in {"I4", "U4", "R4"} => KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, bucket[q])'
                       /\ KeyInBktAtAddr(k, newbkt[q]) = KeyInBktAtAddr(k, newbkt[q])'
                       /\ pc[q] \in {"I4", "U4", "R4"} => ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])'
                       /\ ValOfKeyInBktAtAddr(k, newbkt[q]) = ValOfKeyInBktAtAddr(k, newbkt[q])'
            <6> USE <5>0
            <6>1. pc[q] \in {"I4", "U4", "R4"} => KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, bucket[q])'
              BY Zenon DEF KeyInBktAtAddr
            <6>2. KeyInBktAtAddr(k, newbkt[q]) = KeyInBktAtAddr(k, newbkt[q])'
              BY Zenon DEF KeyInBktAtAddr
            <6>3. pc[q] \in {"I4", "U4", "R4"} => ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])'
              <7> SUFFICES ASSUME pc[q] \in {"I4", "U4", "R4"}
                           PROVE  ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])'
                OBVIOUS
              <7> DEFINE bkt_arr == MemLocs'[bucket'[q]]
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
              <7>1. ValOfKeyInBktAtAddr(k, bucket[q])' = bkt_arr[idx].val
                BY Zenon DEF ValOfKeyInBktAtAddr
              <7>2. bkt_arr = MemLocs[bucket[q]]
                BY Zenon
              <7>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
                BY Zenon
              <7> QED
                BY <7>1, <7>2, <7>3, Isa DEF ValOfKeyInBktAtAddr
            <6>4. ValOfKeyInBktAtAddr(k, newbkt[q]) = ValOfKeyInBktAtAddr(k, newbkt[q])'
              <7> DEFINE bkt_arr == MemLocs'[newbkt'[q]]
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
              <7>1. ValOfKeyInBktAtAddr(k, newbkt[q])' = bkt_arr[idx].val
                BY Zenon DEF ValOfKeyInBktAtAddr
              <7>2. bkt_arr = MemLocs[newbkt[q]]
                BY Zenon
              <7>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
                BY Zenon
              <7> QED
                BY <7>1, <7>2, <7>3, Isa DEF ValOfKeyInBktAtAddr
            <6> QED
              BY <6>1, <6>2, <6>3, <6>4
          <5>1. CASE pc'[q] = "I4"
            <6> USE <5>1
            <6> SUFFICES /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                         /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                         /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                   /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                      (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
              OBVIOUS
            <6>1. pc[q] = "I4" /\ arg[q].key \in KeyDomain
              BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
            <6>2. /\ KeyInBktAtAddr(arg[q].key, newbkt[q])
                  /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q]) = arg[q].val
                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                            /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                               (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
              BY <6>1, Zenon DEF NewBktOK
            <6> QED
              BY <5>0, <6>1, <6>2, ZenonT(30)
          <5>2. CASE pc'[q] = "U4"
            <6> USE <5>2
            <6> SUFFICES /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                         /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                         /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                   /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                      (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
              OBVIOUS
            <6>1. pc[q] = "U4" /\ arg[q].key \in KeyDomain
              BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
            <6>2. /\ KeyInBktAtAddr(arg[q].key, newbkt[q])
                  /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q]) = arg[q].val
                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                            /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                               (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
              BY <6>1, Zenon DEF NewBktOK
            <6> QED
              BY <5>0, <6>1, <6>2, ZenonT(30)
          <5>3. CASE pc'[q] = "R4"
            <6> USE <5>3
            <6> SUFFICES /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])'
                         /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                   /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                      (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
              OBVIOUS
            <6>1. pc[q] = "R4" /\ arg[q].key \in KeyDomain
              BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
            <6>2. /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])
                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                            /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                               (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
              BY <6>1, Zenon DEF NewBktOK
            <6> QED
              BY <5>0, <6>1, <6>2, ZenonT(30)
          <5> QED
            BY <5>1, <5>2, <5>3
        <4> QED
          BY <4>1, <4>10, <4>11, <4>12, <4>13, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, <4>14, <4>15 DEF Inv
      <3>4. CASE Line = R5(p)
        <4> USE <3>4, RemDef DEF R5
        <4>1. PTypeOK'
          BY NextPTypeOK
        <4>2. (pc \in [ProcSet -> LineIDs])'
          BY Isa DEF LineIDs
        <4>3. (A \in [1..N -> AllocAddrs \union {NULL}])'
          OBVIOUS
        <4>4. (MemLocs \in [Addrs -> Seq([key: KeyDomain, val: ValDomain])])'
          OBVIOUS
        <4>5. (AllocAddrs \in SUBSET Addrs)'
          OBVIOUS
        <4>6. (bucket \in [ProcSet -> AllocAddrs \union {NULL}])'
          OBVIOUS
        <4>7. (newbkt \in [ProcSet -> AllocAddrs \union {NULL}])'
          OBVIOUS
        <4>8. (r \in [ProcSet -> ValDomain \union {NULL}])'
          OBVIOUS
        <4>9. (arg \in [ProcSet -> ArgDomain])'
          OBVIOUS
        <4>10. (ret \in [ProcSet -> RetDomain])'
          BY Zenon DEF RetDomain
        <4>11. (\A p_1 \in ProcSet : (pc[p_1] # RemainderID) => arg[p_1] \in ArgsOf(LineIDtoOp(pc[p_1])))'
          <5> SUFFICES pc'[p] = RemainderID
            BY Zenon
          <5> QED
            BY Zenon
        <4>12. AddrsOK'
          <5> SUFFICES ASSUME NEW p_1 \in ProcSet',
                              (pc[p_1] \in {"I4", "U4", "R4"})'
                       PROVE  (/\ \A q \in ProcSet : (p_1 # q => /\ newbkt[p_1] # bucket[q]
                                                                 /\ newbkt[p_1] # newbkt[q])
                               /\ \A idx \in 1..N  : (A[idx] # newbkt[p_1])
                               /\ newbkt[p_1] # bucket[p_1]
                               /\ newbkt[p_1] \in AllocAddrs)'
            BY DEF AddrsOK
          <5>1. (\A q \in ProcSet : (p_1 # q => /\ newbkt[p_1] # bucket[q]
                                                /\ newbkt[p_1] # newbkt[q]))'
            BY DEF AddrsOK
          <5>2. (\A idx \in 1..N  : (A[idx] # newbkt[p_1]))'
            BY DEF AddrsOK
          <5>3. (newbkt[p_1] # bucket[p_1])'
            BY DEF AddrsOK
          <5>4. (newbkt[p_1] \in AllocAddrs)'
            BY DEF AddrsOK
          <5>5. QED
            BY <5>1, <5>2, <5>3, <5>4
        <4>13. BktOK'
          <5> SUFFICES ASSUME NEW q \in ProcSet
                       PROVE  (/\ pc'[q] \in {"I3", "I4"} => (/\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                                                              /\ r'[q] = NULL)
                               /\ pc'[q] \in {"U3", "U4"} => (IF KeyInBktAtAddr(arg[q].key, bucket[q])'
                                                                  THEN (/\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                                                                        /\ r'[q] # NULL)
                                                                  ELSE r'[q] = NULL)
                               /\ pc'[q] \in {"R3", "R4"} => (/\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                                                              /\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                                                              /\ r'[q] # NULL))
            BY DEF BktOK
          <5>1. CASE pc'[q] \in {"I3", "I4"}
            <6> USE <5>1
            <6> SUFFICES ~KeyInBktAtAddr(arg[q].key, bucket[q])' /\ r'[q] = NULL
              OBVIOUS
            <6>1. ~KeyInBktAtAddr(arg[q].key, bucket[q]) /\ r[q] = NULL
              BY Zenon DEF BktOK
            <6> QED
              BY <6>1, Zenon DEF KeyInBktAtAddr
          <5>2. CASE pc'[q] \in {"U3", "U4"}
            <6> USE <5>2
            <6> SUFFICES IF KeyInBktAtAddr(arg[q].key, bucket[q])'
                            THEN (/\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                                  /\ r'[q] # NULL)
                            ELSE r'[q] = NULL
              OBVIOUS
            <6>1. IF KeyInBktAtAddr(arg[q].key, bucket[q])
                     THEN (/\ r[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                           /\ r[q] # NULL)
                     ELSE r[q] = NULL
              BY Zenon DEF BktOK
            <6>2. KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
              BY Zenon DEF KeyInBktAtAddr
            <6>3. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs'[bucket'[q]][CHOOSE index \in 1..Len(MemLocs'[bucket'[q]]) :
                                   MemLocs'[bucket'[q]][index].key = arg'[q].key].val
              BY DEF ValOfKeyInBktAtAddr
            <6>4. MemLocs = MemLocs' /\ arg = arg' /\ bucket[q] = bucket'[q]
              BY Zenon
            <6>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs[bucket'[q]][CHOOSE index \in 1..Len(MemLocs[bucket'[q]]) :
                                  MemLocs[bucket'[q]][index].key = arg[q].key].val
              BY Zenon, <6>3, <6>4
            <6>6. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs[bucket[q]][CHOOSE index \in 1..Len(MemLocs[bucket[q]]) :
                                 MemLocs[bucket[q]][index].key = arg[q].key].val
              BY <6>4, <6>5
            <6>7. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
              BY <6>6, Zenon DEF ValOfKeyInBktAtAddr
            <6> QED
              BY <6>1, <6>2, <6>7, Zenon
          <5>3. CASE pc'[q] \in {"R3", "R4"}
            <6> USE <5>3
            <6> SUFFICES /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                         /\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                         /\ r'[q] # NULL
              OBVIOUS
            <6>1. /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                  /\ r[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                  /\ r[q] # NULL
              BY Zenon DEF BktOK
            <6>2. KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
              BY Zenon DEF KeyInBktAtAddr
            <6>3. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs'[bucket'[q]][CHOOSE index \in 1..Len(MemLocs'[bucket'[q]]) :
                                   MemLocs'[bucket'[q]][index].key = arg'[q].key].val
              BY DEF ValOfKeyInBktAtAddr
            <6>4. MemLocs = MemLocs' /\ arg = arg' /\ bucket[q] = bucket'[q]
              BY Zenon
            <6>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs[bucket'[q]][CHOOSE index \in 1..Len(MemLocs[bucket'[q]]) :
                                  MemLocs[bucket'[q]][index].key = arg[q].key].val
              BY Zenon, <6>3, <6>4
            <6>6. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs[bucket[q]][CHOOSE index \in 1..Len(MemLocs[bucket[q]]) :
                                 MemLocs[bucket[q]][index].key = arg[q].key].val
              BY <6>4, <6>5
            <6>7. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
              BY <6>6, Zenon DEF ValOfKeyInBktAtAddr
            <6> QED
              BY <6>1, <6>2, <6>7, Zenon
          <5> QED
            BY <5>1, <5>2, <5>3
        <4>14. Uniq'
          <5> SUFFICES ASSUME NEW addr \in AllocAddrs', 
                              NEW bucket_arr, bucket_arr = MemLocs'[addr],
                              NEW j1 \in 1..Len(bucket_arr),
                              NEW j2 \in 1..Len(bucket_arr),
                              bucket_arr[j1].key = bucket_arr[j2].key
                       PROVE  j1 = j2
            BY Zenon DEF Uniq
          <5> QED
            BY Zenon DEF Uniq
        <4>15. NewBktOK'
          <5> SUFFICES ASSUME NEW q \in ProcSet
                       PROVE  /\ pc'[q] = "I4" => /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                                  /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                                                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                            /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                               (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
                              /\ pc'[q] = "U4" => /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                                  /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                                                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                            /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                               (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
                              /\ pc'[q] = "R4" => /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                            /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                               (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
            BY ZenonT(60) DEF NewBktOK
          <5>0. ASSUME NEW k \in KeyDomain
                PROVE  /\ pc[q] \in {"I4", "U4", "R4"} => KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, bucket[q])'
                       /\ KeyInBktAtAddr(k, newbkt[q]) = KeyInBktAtAddr(k, newbkt[q])'
                       /\ pc[q] \in {"I4", "U4", "R4"} => ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])'
                       /\ ValOfKeyInBktAtAddr(k, newbkt[q]) = ValOfKeyInBktAtAddr(k, newbkt[q])'
            <6> USE <5>0
            <6>1. pc[q] \in {"I4", "U4", "R4"} => KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, bucket[q])'
              BY Zenon DEF KeyInBktAtAddr
            <6>2. KeyInBktAtAddr(k, newbkt[q]) = KeyInBktAtAddr(k, newbkt[q])'
              BY Zenon DEF KeyInBktAtAddr
            <6>3. pc[q] \in {"I4", "U4", "R4"} => ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])'
              <7> SUFFICES ASSUME pc[q] \in {"I4", "U4", "R4"}
                           PROVE  ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])'
                OBVIOUS
              <7> DEFINE bkt_arr == MemLocs'[bucket'[q]]
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
              <7>1. ValOfKeyInBktAtAddr(k, bucket[q])' = bkt_arr[idx].val
                BY Zenon DEF ValOfKeyInBktAtAddr
              <7>2. bkt_arr = MemLocs[bucket[q]]
                BY Zenon
              <7>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
                BY Zenon
              <7> QED
                BY <7>1, <7>2, <7>3, Isa DEF ValOfKeyInBktAtAddr
            <6>4. ValOfKeyInBktAtAddr(k, newbkt[q]) = ValOfKeyInBktAtAddr(k, newbkt[q])'
              <7> DEFINE bkt_arr == MemLocs'[newbkt'[q]]
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
              <7>1. ValOfKeyInBktAtAddr(k, newbkt[q])' = bkt_arr[idx].val
                BY Zenon DEF ValOfKeyInBktAtAddr
              <7>2. bkt_arr = MemLocs[newbkt[q]]
                BY Zenon
              <7>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
                BY Zenon
              <7> QED
                BY <7>1, <7>2, <7>3, Isa DEF ValOfKeyInBktAtAddr
            <6> QED
              BY <6>1, <6>2, <6>3, <6>4
          <5>1. CASE pc'[q] = "I4"
            <6> USE <5>1
            <6> SUFFICES /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                         /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                         /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                   /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                      (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
              OBVIOUS
            <6>1. pc[q] = "I4" /\ arg[q].key \in KeyDomain
              BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
            <6>2. /\ KeyInBktAtAddr(arg[q].key, newbkt[q])
                  /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q]) = arg[q].val
                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                            /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                               (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
              BY <6>1, Zenon DEF NewBktOK
            <6> QED
              BY <5>0, <6>1, <6>2, ZenonT(30)
          <5>2. CASE pc'[q] = "U4"
            <6> USE <5>2
            <6> SUFFICES /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                         /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                         /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                   /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                      (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
              OBVIOUS
            <6>1. pc[q] = "U4" /\ arg[q].key \in KeyDomain
              BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
            <6>2. /\ KeyInBktAtAddr(arg[q].key, newbkt[q])
                  /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q]) = arg[q].val
                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                            /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                               (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
              BY <6>1, Zenon DEF NewBktOK
            <6> QED
              BY <5>0, <6>1, <6>2, ZenonT(30)
          <5>3. CASE pc'[q] = "R4"
            <6> USE <5>3
            <6> SUFFICES /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])'
                         /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                   /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                      (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
              OBVIOUS
            <6>1. pc[q] = "R4" /\ arg[q].key \in KeyDomain
              BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
            <6>2. /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])
                  /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                            /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                               (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
              BY <6>1, Zenon DEF NewBktOK
            <6> QED
              BY <5>0, <6>1, <6>2, ZenonT(30)
          <5> QED
            BY <5>1, <5>2, <5>3
        <4> QED
          BY <4>1, <4>10, <4>11, <4>12, <4>13, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, <4>14, <4>15 DEF Inv
      <3> QED
        BY Zenon, <3>1, <3>2, <3>3, <3>4 DEF RetLines
    <2> QED
      BY <1>1, <2>1, <2>2, <2>3 DEF Next
  <1>2. CASE UNCHANGED vars
    <2> USE <1>2 DEF vars, algvars
    <2>1. PTypeOK'
      BY NextPTypeOK
    <2>2. (pc \in [ProcSet -> LineIDs])'
      BY DEF LineIDs
    <2>3. (A \in [1..N -> AllocAddrs \union {NULL}])'
      OBVIOUS
    <2>4. (MemLocs \in [Addrs -> Seq([key: KeyDomain, val: ValDomain])])'
      <3> DEFINE D == Addrs
      <3> DEFINE R == Seq([key: KeyDomain, val: ValDomain])
      <3>0. MemLocs \in [D -> R]
        BY Zenon
      <3> SUFFICES MemLocs' \in [D' -> R']
        BY Zenon
      <3>1. D = D'
        OBVIOUS
      <3>2. R = R'
        OBVIOUS
      <3>3. MemLocs = MemLocs'
        OBVIOUS
      <3> HIDE DEF D, R
      <3> QED
        BY <3>0, <3>1, <3>2, <3>3
    <2>5. (AllocAddrs \in SUBSET Addrs)'
      OBVIOUS
    <2>6. (bucket \in [ProcSet -> AllocAddrs \union {NULL}])'
      OBVIOUS
    <2>7. (newbkt \in [ProcSet -> AllocAddrs \union {NULL}])'
      OBVIOUS
    <2>8. (r \in [ProcSet -> ValDomain \union {NULL}])'
      OBVIOUS
    <2>9. (arg \in [ProcSet -> ArgDomain])'
      OBVIOUS
    <2>10. (ret \in [ProcSet -> RetDomain])'
      BY DEF RetDomain
    <2>11. (\A p_1 \in ProcSet : (pc[p_1] # RemainderID) => arg[p_1] \in ArgsOf(LineIDtoOp(pc[p_1])))'
      OBVIOUS
    <2>12. AddrsOK'
      <3> SUFFICES ASSUME NEW p \in ProcSet',
                          (pc[p] \in {"I4", "U4", "R4"})'
                   PROVE  (/\ \A q \in ProcSet : (p # q => /\ newbkt[p] # bucket[q]
                                                           /\ newbkt[p] # newbkt[q])
                           /\ \A idx \in 1..N  : (A[idx] # newbkt[p])
                           /\ newbkt[p] # bucket[p]
                           /\ newbkt[p] \in AllocAddrs)'
        BY DEF AddrsOK
      <3>1. (\A q \in ProcSet : (p # q => /\ newbkt[p] # bucket[q]
                                          /\ newbkt[p] # newbkt[q]))'
        BY DEF AddrsOK
      <3>2. A = A' /\ newbkt = newbkt'
        OBVIOUS
      <3>3. (\A idx \in 1..N  : (A[idx] # newbkt[p]))'
        BY <3>2 DEF AddrsOK
      <3>4. (newbkt[p] # bucket[p])'
        BY DEF AddrsOK
      <3>5. (newbkt[p] \in AllocAddrs)'
        BY DEF AddrsOK
      <3>6. QED
        BY <3>1, <3>3, <3>4, <3>5
    <2>13. BktOK'
      <3> SUFFICES ASSUME NEW q \in ProcSet'
                   PROVE  (/\ pc[q] \in {"I3", "I4"} => (/\ ~KeyInBktAtAddr(arg[q].key, bucket[q]) 
                                                         /\ r[q] = NULL)
                           /\ pc[q] \in {"U3", "U4"} => (IF KeyInBktAtAddr(arg[q].key, bucket[q])
                                                            THEN (/\ r[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q]) 
                                                                  /\ r[q] # NULL)
                                                            ELSE r[q] = NULL)
                           /\ pc[q] \in {"R3", "R4"} => (/\ KeyInBktAtAddr(arg[q].key, bucket[q]) 
                                                         /\ r[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q]) 
                                                         /\ r[q] # NULL))'
        BY DEF BktOK
      <3>1. CASE pc'[q] \in {"I3", "I4"}
        <4> USE <3>1
        <4> SUFFICES ~KeyInBktAtAddr(arg[q].key, bucket[q])' /\ r'[q] = NULL
          OBVIOUS
        <4> pc[q] \in {"I3", "I4"}
          OBVIOUS
        <4>1. ~KeyInBktAtAddr(arg[q].key, bucket[q]) /\ r[q] = NULL
          BY Zenon DEF BktOK
        <4> QED
          BY <4>1 DEF KeyInBktAtAddr
      <3>2. CASE pc'[q] \in {"U3", "U4"}
        <4> USE <3>2
        <4> SUFFICES IF KeyInBktAtAddr(arg[q].key, bucket[q])'
                            THEN (/\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                                  /\ r'[q] # NULL)
                            ELSE r'[q] = NULL
          OBVIOUS
        <4> pc[q] \in {"U3", "U4"}
          OBVIOUS
        <4>1. IF KeyInBktAtAddr(arg[q].key, bucket[q])
                     THEN (/\ r[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                           /\ r[q] # NULL)
                     ELSE r[q] = NULL
          BY Zenon DEF BktOK
        <4>2. KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
          BY DEF KeyInBktAtAddr
        <4>3. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
          MemLocs'[bucket'[q]][CHOOSE index \in 1..Len(MemLocs'[bucket'[q]]) :
                                   MemLocs'[bucket'[q]][index].key = arg'[q].key].val
          BY DEF ValOfKeyInBktAtAddr
        <4>4. MemLocs = MemLocs' /\ arg = arg' /\ bucket[q] = bucket'[q]
          OBVIOUS
        <4>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs[bucket'[q]][CHOOSE index \in 1..Len(MemLocs[bucket'[q]]) :
                                  MemLocs[bucket'[q]][index].key = arg[q].key].val
          BY Zenon, <4>3, <4>4
        <4>6. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs[bucket[q]][CHOOSE index \in 1..Len(MemLocs[bucket[q]]) :
                                 MemLocs[bucket[q]][index].key = arg[q].key].val
          BY <4>4, <4>5
        <4>7. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
          BY <4>6, Zenon DEF ValOfKeyInBktAtAddr
        <4> QED
          BY <4>1, <4>2, <4>7
      <3>3. CASE pc'[q] \in {"R3", "R4"}
        <4> USE <3>3
        <4> SUFFICES /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                     /\ r'[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' 
                     /\ r'[q] # NULL
          OBVIOUS
        <4> pc[q] \in {"R3", "R4"}
          OBVIOUS
        <4>1. /\ KeyInBktAtAddr(arg[q].key, bucket[q])
              /\ r[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
              /\ r[q] # NULL
          BY Zenon DEF BktOK
        <4>2. KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
          BY DEF KeyInBktAtAddr
        <4>3. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs'[bucket'[q]][CHOOSE index \in 1..Len(MemLocs'[bucket'[q]]) :
                                   MemLocs'[bucket'[q]][index].key = arg'[q].key].val
          BY DEF ValOfKeyInBktAtAddr
        <4>4. MemLocs = MemLocs' /\ arg = arg' /\ bucket[q] = bucket'[q]
          OBVIOUS
        <4>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs[bucket'[q]][CHOOSE index \in 1..Len(MemLocs[bucket'[q]]) :
                                  MemLocs[bucket'[q]][index].key = arg[q].key].val
          BY Zenon, <4>3, <4>4
        <4>6. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = 
              MemLocs[bucket[q]][CHOOSE index \in 1..Len(MemLocs[bucket[q]]) :
                                 MemLocs[bucket[q]][index].key = arg[q].key].val
          BY <4>4, <4>5
        <4>7. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
          BY <4>6, Zenon DEF ValOfKeyInBktAtAddr
        <4> QED
          BY <4>1, <4>2, <4>7
      <3> QED
        BY <3>1, <3>2, <3>3     
    <2>14. Uniq'
      <3> SUFFICES ASSUME NEW addr \in AllocAddrs', 
                          NEW bucket_arr, bucket_arr = MemLocs'[addr],
                          NEW j1 \in 1..Len(bucket_arr),
                          NEW j2 \in 1..Len(bucket_arr),
                          bucket_arr[j1].key = bucket_arr[j2].key
                   PROVE  j1 = j2
        BY Zenon DEF Uniq
      <3> QED
        BY DEF Uniq
    <2>15. NewBktOK'
      <3> SUFFICES ASSUME NEW q \in ProcSet
                       PROVE  /\ pc'[q] = "I4" => /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                                  /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                                                  /\ \A k \in KeyDomain : k # arg'[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                             /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                               (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
                              /\ pc'[q] = "U4" => /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                                  /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                                                  /\ \A k \in KeyDomain : k # arg'[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                             /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                               (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
                              /\ pc'[q] = "R4" => /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                                  /\ \A k \in KeyDomain : k # arg'[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                             /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                               (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
            BY DEF NewBktOK
      <3>A. arg = arg'
        OBVIOUS
      <3>B. SUFFICES /\ pc'[q] = "I4" => /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                         /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                                         /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                   /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                      (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
                     /\ pc'[q] = "U4" => /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                         /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                                         /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                   /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                      (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
                     /\ pc'[q] = "R4" => /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])'
                                         /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                                                   /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                                      (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
        BY <3>A
      <3>0. ASSUME NEW k \in KeyDomain
            PROVE  /\ pc[q] \in {"I4", "U4", "R4"} => KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, bucket[q])'
                   /\ KeyInBktAtAddr(k, newbkt[q]) = KeyInBktAtAddr(k, newbkt[q])'
                   /\ pc[q] \in {"I4", "U4", "R4"} => ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])'
                   /\ ValOfKeyInBktAtAddr(k, newbkt[q]) = ValOfKeyInBktAtAddr(k, newbkt[q])'
        <4> USE <3>0
        <4>1. pc[q] \in {"I4", "U4", "R4"} => KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, bucket[q])'
          BY DEF KeyInBktAtAddr
        <4>2. KeyInBktAtAddr(k, newbkt[q]) = KeyInBktAtAddr(k, newbkt[q])'
          BY DEF KeyInBktAtAddr
        <4>3. pc[q] \in {"I4", "U4", "R4"} => ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])'
          <5> SUFFICES ASSUME pc[q] \in {"I4", "U4", "R4"}
                       PROVE  ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, bucket[q])'
            OBVIOUS
          <5> DEFINE bkt_arr == MemLocs'[bucket'[q]]
          <5> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
          <5>1. ValOfKeyInBktAtAddr(k, bucket[q])' = bkt_arr[idx].val
            BY Zenon DEF ValOfKeyInBktAtAddr
          <5>2. bkt_arr = MemLocs[bucket[q]]
            OBVIOUS
          <5>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
            BY Zenon
          <5> QED
            BY <5>1, <5>2, <5>3, Isa DEF ValOfKeyInBktAtAddr
        <4>4. ValOfKeyInBktAtAddr(k, newbkt[q]) = ValOfKeyInBktAtAddr(k, newbkt[q])'
          <5> DEFINE bkt_arr == MemLocs'[newbkt'[q]]
          <5> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
          <5>1. ValOfKeyInBktAtAddr(k, newbkt[q])' = bkt_arr[idx].val
            BY Zenon DEF ValOfKeyInBktAtAddr
          <5>2. bkt_arr = MemLocs[newbkt[q]]
            OBVIOUS
          <5>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
            BY Zenon
          <5> QED
            BY <5>1, <5>2, <5>3, Isa DEF ValOfKeyInBktAtAddr
        <4> QED
          BY <4>1, <4>2, <4>3, <4>4
      <3>1. CASE pc'[q] = "I4"
        <4> USE <3>1
        <4> SUFFICES /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                     /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                     /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                               /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                  (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
          OBVIOUS
        <4>1. pc[q] = "I4" /\ arg[q].key \in KeyDomain
          BY RemDef DEF ArgsOf, LineIDtoOp
        <4>2. /\ KeyInBktAtAddr(arg[q].key, newbkt[q])
              /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q]) = arg[q].val
              /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                        /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                           (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
          BY <4>1, Zenon DEF NewBktOK
        <4> QED
          BY <3>0, <4>1, <4>2
      <3>2. CASE pc'[q] = "U4"
        <4> USE <3>2
        <4> SUFFICES /\ KeyInBktAtAddr(arg[q].key, newbkt[q])'
                     /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q])' = arg[q].val
                     /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                               /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                  (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
          OBVIOUS
        <4>1. pc[q] = "U4" /\ arg[q].key \in KeyDomain
          BY RemDef DEF ArgsOf, LineIDtoOp
        <4>2. /\ KeyInBktAtAddr(arg[q].key, newbkt[q])
              /\ ValOfKeyInBktAtAddr(arg[q].key, newbkt[q]) = arg[q].val
              /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                        /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                           (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
          BY <4>1, Zenon DEF NewBktOK
        <4> QED
          BY <3>0, <4>1, <4>2
      <3>3. CASE pc'[q] = "R4"
        <4> USE <3>3
        <4> SUFFICES /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])'
                     /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q])' = KeyInBktAtAddr(k, newbkt[q])'
                                                               /\ KeyInBktAtAddr(k, bucket[q])' =>
                                                                  (ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, newbkt[q])')
          OBVIOUS
        <4>1. pc[q] = "R4" /\ arg[q].key \in KeyDomain
          BY RemDef DEF ArgsOf, LineIDtoOp
        <4>2. /\ ~KeyInBktAtAddr(arg[q].key, newbkt[q])
              /\ \A k \in KeyDomain : k # arg[q].key => /\ KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, newbkt[q])
                                                        /\ KeyInBktAtAddr(k, bucket[q]) =>
                                                           (ValOfKeyInBktAtAddr(k, bucket[q]) = ValOfKeyInBktAtAddr(k, newbkt[q]))
          BY <4>1, Zenon DEF NewBktOK
        <4> QED
          BY <3>0, <4>1, <4>2
      <3> QED
        BY <3>1, <3>2, <3>3
    <2> QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10, <2>11, <2>12, <2>13, <2>14, <2>15 DEF Inv
  <1> QED
    BY <1>1, <1>2

===========================================================================
\* Modification History
\* Last modified Thu Aug 08 09:39:50 EDT 2024 by uguryavuz
\* Created Thu Aug 08 09:37:36 EDT 2024 by uguryavuz
