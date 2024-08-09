---------------------------- MODULE PHash_Proof3 ----------------------------
EXTENDS PHash_Proof2_HO, FiniteSetTheorems

InvL2 == S # {}
InvWithL2 == Inv /\ InvL2

THEOREM L2Init == AInit => InvWithL2
  <1> SUFFICES ASSUME AInit
               PROVE  InvWithL2
    OBVIOUS
  <1>1. Inv
    BY InitInv
  <1>2. InvL2
    <2> SUFFICES \E c \in ConfigDomain : c \in S
      BY Zenon DEF InvL2, S
    <2> DEFINE c == [state |-> [k \in KeyDomain |-> NULL],
                     op    |-> [p \in ProcSet   |-> BOT],
                     arg   |-> [p \in ProcSet   |-> BOT],
                     res   |-> [p \in ProcSet   |-> BOT]]
    <2>1. c \in ConfigDomain
      BY DEF OpDomain, ArgDomain, ResDomain, ConfigDomain, StateDomain
    <2>2. \A k \in KeyDomain : ~KeyInBktAtAddr(k, A[Hash[k]])
      <3> SUFFICES ASSUME NEW k \in KeyDomain
                   PROVE  A[Hash[k]] = NULL
        BY Zenon DEF KeyInBktAtAddr
      <3>1. Hash[k] \in 1..N
        BY HashDef
      <3>2. A[Hash[k]] = NULL
        BY <3>1 DEF AInit, Init
      <3> QED
        BY <3>2
    <2>3. c.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) 
                                             THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) 
                                             ELSE NULL]
      BY <2>2
    <2>4. \A p \in ProcSet : pc[p] = RemainderID
      BY DEF AInit, Init
    <2>5. \A p \in ProcSet : c.op[p] = BOT /\ c.arg[p] = BOT /\ c.res[p] = BOT
      OBVIOUS
    <2>6. c \in S
      BY <2>1, <2>3, <2>4, <2>5, RemDef, Zenon DEF S
    <2> QED
      BY <2>1, <2>6
  <1> QED
    BY <1>1, <1>2 DEF InvWithL2

THEOREM L2Next == InvWithL2 /\ [Next]_vars => InvL2'
  <1> USE DEF InvWithL2, Inv, TOK
  <1> SUFFICES ASSUME InvWithL2 /\ [Next]_vars
               PROVE  InvL2'
    OBVIOUS
  <1> SUFFICES \E c \in ConfigDomain : c \in S'
    BY DEF InvL2
  <1>1. TOK'
    BY Zenon, NextInv
  <1> DEFINE op == [p \in ProcSet |-> CASE pc'[p] = RemainderID -> BOT
                                        [] pc'[p] \in {"F1", "F2", "F3"} -> "Find"
                                        [] pc'[p] \in {"I1", "I2", "I3", "I4", "I5"} -> "Insert"
                                        [] pc'[p] \in {"U1", "U2", "U3", "U4", "U5"} -> "Upsert"
                                        [] pc'[p] \in {"R1", "R2", "R3", "R4", "R5"} -> "Remove"]
  <1>2. op \in [ProcSet -> OpDomain]
    BY <1>1 DEF OpDomain, LineIDs
  <1> DEFINE carg == [p \in ProcSet |-> IF pc'[p] = RemainderID 
                                           THEN BOT 
                                           ELSE arg'[p]]
  <1>3. carg \in [ProcSet -> ArgDomain]
    BY <1>1 DEF OpDomain, LineIDs, ArgDomain
  <1> state == [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]])' 
                                       THEN ValOfKeyInBktAtAddr(k, A[Hash[k]])'
                                       ELSE NULL]
  <1>4. state \in StateDomain
    <2> SUFFICES ASSUME NEW k \in KeyDomain,
                        KeyInBktAtAddr(k, A[Hash[k]])' 
                 PROVE  ValOfKeyInBktAtAddr(k, A[Hash[k]])' \in ValDomain
      BY DEF StateDomain
    <2>1. A'[Hash[k]] \in AllocAddrs'
      BY <1>1, HashDef DEF KeyInBktAtAddr
    <2>2. PICK idx \in 1..Len(MemLocs'[A'[Hash[k]]]) : MemLocs'[A'[Hash[k]]][idx].key = k
      BY DEF KeyInBktAtAddr
    <2>3. ValOfKeyInBktAtAddr(k, A[Hash[k]])' = 
          MemLocs'[A'[Hash[k]]][CHOOSE index \in 1..Len(MemLocs'[A'[Hash[k]]]) : MemLocs'[A'[Hash[k]]][index].key = k].val
      BY Zenon DEF ValOfKeyInBktAtAddr
    <2>4. idx = CHOOSE index \in 1..Len(MemLocs'[A'[Hash[k]]]) : MemLocs'[A'[Hash[k]]][index].key = k
      BY <2>2
    <2>5. ValOfKeyInBktAtAddr(k, A[Hash[k]])' = MemLocs'[A'[Hash[k]]][idx].val
      BY <2>3, <2>4, Zenon
    <2>6. MemLocs'[A'[Hash[k]]] \in Seq([key: KeyDomain, val: ValDomain])
      BY <1>1, <2>1, Zenon
    <2>7. MemLocs'[A'[Hash[k]]][idx] \in [key: KeyDomain, val: ValDomain]
      BY <2>2, <2>6, ElementOfSeq, Zenon
    <2>8. MemLocs'[A'[Hash[k]]][idx].val \in ValDomain
      BY <2>7
    <2> QED
      BY <2>5, <2>8
  <1> DEFINE res == 
        [p \in ProcSet |->
           CASE pc'[p] = RemainderID 
                -> BOT
             [] pc'[p] = "F1"        
                -> BOT
             [] pc'[p] = "F2" /\ KeyInBktAtAddr(arg[p].key, bucket[p])'
                -> ValOfKeyInBktAtAddr(arg[p].key, bucket[p])'
             [] pc'[p] = "F2" /\ ~KeyInBktAtAddr(arg[p].key, bucket[p])'
                -> NULL
             [] pc'[p] = "F3"
                -> r'[p]
             [] pc'[p] \in {"I1", "I3", "I4"}   
                -> BOT
             [] pc'[p] = "I2" /\ KeyInBktAtAddr(arg[p].key, bucket[p])'
                -> ValOfKeyInBktAtAddr(arg[p].key, bucket[p])'
             [] pc'[p] = "I2" /\ ~KeyInBktAtAddr(arg[p].key, bucket[p])'
                -> BOT
             [] pc'[p] = "I5"
                -> r'[p]
             [] pc'[p] \in {"U1", "U2", "U3", "U4"}
                -> BOT
             [] pc'[p] = "U5"
                -> r'[p]
             [] pc'[p] \in {"R1", "R3", "R4"}        
                -> BOT
             [] pc'[p] = "R2" /\ KeyInBktAtAddr(arg[p].key, bucket[p])'
                -> BOT
             [] pc'[p] = "R2" /\ ~KeyInBktAtAddr(arg[p].key, bucket[p])'
                -> NULL
             [] pc'[p] = "R5"
                -> r'[p]]
  <1>5. res \in [ProcSet -> ResDomain]
    <2> SUFFICES ASSUME NEW p \in ProcSet
                 PROVE  res[p] \in ResDomain
      BY Zenon
    <2> USE RemDef
    <2>1. CASE pc'[p] = RemainderID
      BY <2>1 DEF ResDomain
    <2>2. CASE pc'[p] = "F1"
      BY <2>2 DEF ResDomain
    <2>3. CASE pc'[p] = "F2" /\ KeyInBktAtAddr(arg[p].key, bucket[p])'
      <3> SUFFICES ValOfKeyInBktAtAddr(arg[p].key, bucket[p])' \in ValDomain
        BY <2>3 DEF ResDomain
      <3>1. PICK idx \in 1..Len(MemLocs'[bucket'[p]]) : MemLocs'[bucket'[p]][idx].key = arg'[p].key
        BY Zenon, <2>3 DEF KeyInBktAtAddr
      <3>2. ValOfKeyInBktAtAddr(arg[p].key, bucket[p])' = 
            MemLocs'[bucket'[p]][CHOOSE index \in 1..Len(MemLocs'[bucket'[p]]) : MemLocs'[bucket'[p]][index].key = arg'[p].key].val
        BY Zenon DEF ValOfKeyInBktAtAddr
      <3>3. idx = CHOOSE index \in 1..Len(MemLocs'[bucket'[p]]) : MemLocs'[bucket'[p]][index].key = arg'[p].key
        BY <3>1
      <3>4. ValOfKeyInBktAtAddr(arg[p].key, bucket[p])' = MemLocs'[bucket'[p]][idx].val
        BY <3>2, <3>3, Zenon
      <3>5. MemLocs'[bucket'[p]] \in Seq([key: KeyDomain, val: ValDomain])
        BY <1>1, <2>3, Zenon DEF KeyInBktAtAddr
      <3>6. MemLocs'[bucket'[p]][idx] \in [key: KeyDomain, val: ValDomain]
        BY <3>1, <3>5, ElementOfSeq, Zenon
      <3>7. MemLocs'[bucket'[p]][idx].val \in ValDomain
        BY <3>6
      <3>8. ValOfKeyInBktAtAddr(arg[p].key, bucket[p])' \in ValDomain
        BY <3>4, <3>7
      <3> QED
        BY <2>3, <3>8
    <2>4. CASE pc'[p] = "F2" /\ ~KeyInBktAtAddr(arg[p].key, bucket[p])'
      BY <2>4 DEF ResDomain
    <2>5. CASE pc'[p] = "F3"
      BY <1>1, <2>5 DEF ResDomain
    <2>6. CASE pc'[p] \in {"I1", "I3", "I4"}
      BY <2>6 DEF ResDomain
    <2>7. CASE pc'[p] = "I2" /\ KeyInBktAtAddr(arg[p].key, bucket[p])'
      <3> SUFFICES ValOfKeyInBktAtAddr(arg[p].key, bucket[p])' \in ValDomain
        BY <2>7 DEF ResDomain
      <3>1. PICK idx \in 1..Len(MemLocs'[bucket'[p]]) : MemLocs'[bucket'[p]][idx].key = arg'[p].key
        BY Zenon, <2>7 DEF KeyInBktAtAddr
      <3>2. ValOfKeyInBktAtAddr(arg[p].key, bucket[p])' = 
            MemLocs'[bucket'[p]][CHOOSE index \in 1..Len(MemLocs'[bucket'[p]]) : MemLocs'[bucket'[p]][index].key = arg'[p].key].val
        BY Zenon DEF ValOfKeyInBktAtAddr
      <3>3. idx = CHOOSE index \in 1..Len(MemLocs'[bucket'[p]]) : MemLocs'[bucket'[p]][index].key = arg'[p].key
        BY <3>1
      <3>4. ValOfKeyInBktAtAddr(arg[p].key, bucket[p])' = MemLocs'[bucket'[p]][idx].val
        BY <3>2, <3>3, Zenon
      <3>5. MemLocs'[bucket'[p]] \in Seq([key: KeyDomain, val: ValDomain])
        BY <1>1, <2>7, Zenon DEF KeyInBktAtAddr
      <3>6. MemLocs'[bucket'[p]][idx] \in [key: KeyDomain, val: ValDomain]
        BY <3>1, <3>5, ElementOfSeq, Zenon
      <3>7. MemLocs'[bucket'[p]][idx].val \in ValDomain
        BY <3>6
      <3>8. ValOfKeyInBktAtAddr(arg[p].key, bucket[p])' \in ValDomain
        BY <3>4, <3>7
      <3> QED
        BY <2>7, <3>8
    <2>8. CASE pc'[p] = "I2" /\ ~KeyInBktAtAddr(arg[p].key, bucket[p])'
      BY <2>8 DEF ResDomain
    <2>9. CASE pc'[p] = "I5"
      BY <1>1, <2>9 DEF ResDomain
    <2>10. CASE pc'[p] \in {"U1", "U2", "U3", "U4"}
      BY <2>10 DEF ResDomain
    <2>11. CASE pc'[p] = "U5"
      BY <1>1, <2>11 DEF ResDomain
    <2>12. CASE pc'[p] \in {"R1", "R3", "R4"}
      BY <2>12 DEF ResDomain
    <2>13. CASE pc'[p] = "R2" /\ KeyInBktAtAddr(arg[p].key, bucket[p])'
      BY <2>13 DEF ResDomain
    <2>14. CASE pc'[p] = "R2" /\ ~KeyInBktAtAddr(arg[p].key, bucket[p])'
      BY <2>14 DEF ResDomain
    <2>15. CASE pc'[p] = "R5"
      BY <1>1, <2>15 DEF ResDomain
    <2> QED
      BY <1>1, <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, 
         <2>10, <2>11, <2>12, <2>13, <2>14, <2>15, Zenon DEF LineIDs
  <1> DEFINE c == [state |-> state, op |-> op, arg |-> carg, res |-> res]
  <1>6. c \in ConfigDomain
    BY <1>2, <1>3, <1>4, <1>5, Zenon DEF ConfigDomain
  <1>7. ASSUME NEW q \in ProcSet
          PROVE
            CASE pc'[q] = RemainderID 
                  -> (c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT)
               [] pc'[q] = "F1"
                  -> (c.op[q] = "Find" /\ c.arg[q] = arg'[q] /\ c.res[q] = BOT)
               [] pc'[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                  -> (c.op[q] = "Find" /\ c.arg[q] = arg'[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])')
               [] pc'[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                  -> (c.op[q] = "Find" /\ c.arg[q] = arg'[q] /\ c.res[q] = NULL)
               [] pc'[q] = "F3"
                  -> (c.op[q] = "Find" /\ c.arg[q] = arg'[q] /\ c.res[q] = r'[q])
               [] pc'[q] \in {"I1", "I3", "I4"}
                  -> (c.op[q] = "Insert" /\ c.arg[q] = arg'[q] /\ c.res[q] = BOT)
               [] pc'[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                  -> (c.op[q] = "Insert" /\ c.arg[q] = arg'[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])')
               [] pc'[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                  -> (c.op[q] = "Insert" /\ c.arg[q] = arg'[q] /\ c.res[q] = BOT)
               [] pc'[q] = "I5"
                  -> (c.op[q] = "Insert" /\ c.arg[q] = arg'[q] /\ c.res[q] = r'[q])
               [] pc'[q] \in {"U1", "U2", "U3", "U4"}
                  -> (c.op[q] = "Upsert" /\ c.arg[q] = arg'[q] /\ c.res[q] = BOT)
               [] pc'[q] = "U5"
                  -> (c.op[q] = "Upsert" /\ c.arg[q] = arg'[q] /\ c.res[q] = r'[q])
               [] pc'[q] \in {"R1", "R3", "R4"}
                  -> (c.op[q] = "Remove" /\ c.arg[q] = arg'[q] /\ c.res[q] = BOT)
               [] pc'[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                  -> (c.op[q] = "Remove" /\ c.arg[q] = arg'[q] /\ c.res[q] = BOT)
               [] pc'[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                  -> (c.op[q] = "Remove" /\ c.arg[q] = arg'[q] /\ c.res[q] = NULL)
               [] pc'[q] = "R5"
                  -> (c.op[q] = "Remove" /\ c.arg[q] = arg'[q] /\ c.res[q] = r'[q])
    <2> USE <1>7, RemDef
    <2>1. CASE pc'[q] = RemainderID
      BY <2>1, Zenon
    <2>2. CASE pc'[q] = "F1"
      BY <2>2, Zenon
    <2>3. CASE pc'[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
      BY <2>3, Zenon
    <2>4. CASE pc'[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
      BY <2>4, Zenon
    <2>5. CASE pc'[q] = "F3"
      BY <2>5, Zenon
    <2>6. CASE pc'[q] \in {"I1", "I3", "I4"}
      BY <2>6, Zenon
    <2>7. CASE pc'[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
      BY <2>7, Zenon
    <2>8. CASE pc'[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
      BY <2>8, Zenon
    <2>9. CASE pc'[q] = "I5"
      BY <2>9, Zenon
    <2>10. CASE pc'[q] \in {"U1", "U2", "U3", "U4"}
      BY <2>10, Zenon
    <2>11. CASE pc'[q] = "U5"
      BY <2>11, Zenon
    <2>12. CASE pc'[q] \in {"R1", "R3", "R4"}
      BY <2>12, Zenon
    <2>13. CASE pc'[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
      BY <2>13, Zenon
    <2>14. CASE pc'[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
      BY <2>14, Zenon
    <2>15. CASE pc'[q] = "R5"
      BY <2>15, Zenon
    <2> QED
      BY <1>1, <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, 
         <2>10, <2>11, <2>12, <2>13, <2>14, <2>15, ZenonT(120) DEF LineIDs
  <1>8. c \in S'
    BY <1>6, <1>7, SPrimeRewrite, Zenon DEF SPrime
  <1> QED
    BY <1>6, <1>8, Zenon

InvSL == Cardinality(S) = 1
InvL2SL == Inv /\ InvL2 /\ InvSL

THEOREM SLInit == AInit => InvL2SL
  <1> SUFFICES ASSUME AInit
               PROVE  InvL2SL
    OBVIOUS
  <1>1. Inv
    BY InitInv
  <1>2. InvL2
    BY L2Init DEF InvWithL2
  <1>3. InvSL
    <2>1. ASSUME NEW c1 \in S, NEW c2 \in S
          PROVE  c1 = c2
      <3> USE <2>1
      <3> c1 \in ConfigDomain /\ c2 \in ConfigDomain
        BY DEF S
      <3> SUFFICES /\ c1.state = c2.state
                   /\ c1.op    = c2.op
                   /\ c1.arg   = c2.arg
                   /\ c1.res   = c2.res
        BY DEF ConfigDomain
      <3>1. c1.state = c2.state
        BY DEF S
      <3>2. /\ c1.op = c2.op
            /\ c1.arg = c2.arg
            /\ c1.res = c2.res
        <4> SUFFICES ASSUME NEW p \in ProcSet
                     PROVE  /\ c1.op[p] = c2.op[p]
                            /\ c1.arg[p] = c2.arg[p]
                            /\ c1.res[p] = c2.res[p]
          BY DEF ConfigDomain
        <4> USE RemDef 
        <4>1. CASE pc[p] = RemainderID
          BY <4>1, Zenon DEF S
        <4>2. CASE pc[p] \in {"F1", "F2", "F3"}
          BY <4>2, Zenon DEF S 
        <4>3. CASE pc[p] \in {"I1", "I2", "I3", "I4", "I5"}
          BY <4>3, Zenon DEF S
        <4>4. CASE pc[p] \in {"U1", "U2", "U3", "U4", "U5"}
          BY <4>4, Zenon DEF S
        <4>5. CASE pc[p] \in {"R1", "R2", "R3", "R4", "R5"}
          BY <4>5, Zenon DEF S
        <4> QED
          BY <4>1, <4>2, <4>3, <4>4, <4>5, <1>1 DEF LineIDs, Inv, TOK
      <3> QED
        BY <3>1, <3>2
    <2>2. PICK c \in S : TRUE
      BY <1>2 DEF InvL2
    <2>3. S = {c}
      BY <2>1, <2>2
    <2>4. Cardinality(S) = 1
      BY <2>3, FS_Singleton, Zenon
    <2> QED
      BY <2>4 DEF InvSL
  <1> QED
    BY <1>1, <1>2, <1>3 DEF InvL2SL

THEOREM SLNext == InvL2SL /\ [Next]_vars => InvL2SL'
  <1> USE DEF InvL2SL
  <1> SUFFICES ASSUME InvL2SL /\ [Next]_vars
               PROVE  InvL2SL'
    OBVIOUS
  <1>1. Inv'
    BY NextInv
  <1>2. InvL2'
    BY L2Next DEF InvWithL2
  <1>3. InvSL'
    <2>1. ASSUME NEW c1 \in S', NEW c2 \in S'
          PROVE  c1 = c2
      <3> USE <2>1
      <3> c1 \in ConfigDomain /\ c2 \in ConfigDomain
        BY DEF S
      <3> SUFFICES /\ c1.state = c2.state
                   /\ c1.op    = c2.op
                   /\ c1.arg   = c2.arg
                   /\ c1.res   = c2.res
        BY DEF ConfigDomain
      <3>1. c1.state = c2.state
        BY DEF S
      <3>2. /\ c1.op = c2.op
            /\ c1.arg = c2.arg
            /\ c1.res = c2.res
        <4> SUFFICES ASSUME NEW p \in ProcSet
                     PROVE  /\ c1.op[p] = c2.op[p]
                            /\ c1.arg[p] = c2.arg[p]
                            /\ c1.res[p] = c2.res[p]
          BY DEF ConfigDomain
        <4> USE RemDef 
        <4>1. CASE pc'[p] = RemainderID
          BY <4>1, Zenon, SPrimeRewrite DEF SPrime
        <4>2. CASE pc'[p] \in {"F1", "F2", "F3"}
          BY <4>2, Zenon DEF S 
        <4>3. CASE pc'[p] \in {"I1", "I2", "I3", "I4", "I5"}
          BY <4>3, Zenon DEF S
        <4>4. CASE pc'[p] \in {"U1", "U2", "U3", "U4", "U5"}
          BY <4>4, Zenon DEF S
        <4>5. CASE pc'[p] \in {"R1", "R2", "R3", "R4", "R5"}
          BY <4>5, Zenon DEF S
        <4> QED
          BY <4>1, <4>2, <4>3, <4>4, <4>5, <1>1 DEF LineIDs, Inv, TOK
      <3> QED
        BY <3>1, <3>2
    <2>2. PICK c \in S' : TRUE
      BY <1>2 DEF InvL2
    <2>3. S' = {c}
      BY <2>1, <2>2
    <2>4. Cardinality(S') = 1
      BY <2>3, FS_Singleton, Zenon
    <2> QED 
      BY <2>4 DEF InvSL
  <1> QED
    BY <1>1, <1>2, <1>3 DEF InvL2SL

=============================================================================
\* Modification History
\* Last modified Fri Aug 09 11:48:42 EDT 2024 by uguryavuz
\* Last modified Thu Aug 08 18:01:34 UTC 2024 by uyavuz
\* Created Thu Aug 08 17:54:53 UTC 2024 by uyavuz
