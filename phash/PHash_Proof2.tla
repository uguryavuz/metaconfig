--------------------------- MODULE PHash_Proof2 ---------------------------
EXTENDS PHash_Proof1_HO, FiniteSetTheorems

S == {c \in ConfigDomain :
        /\ c.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) 
                                             THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) 
                                             ELSE NULL]
        /\ \A p \in ProcSet :
           CASE pc[p] = RemainderID 
                -> (c.op[p] = BOT /\ c.arg[p] = BOT /\ c.res[p] = BOT)
             [] pc[p] = "F1"
                -> (c.op[p] = "Find" /\ c.arg[p] = arg[p] /\ c.res[p] = BOT)
             [] pc[p] = "F2" /\ KeyInBktAtAddr(arg[p].key, bucket[p])
                -> (c.op[p] = "Find" /\ c.arg[p] = arg[p] /\ c.res[p] = ValOfKeyInBktAtAddr(arg[p].key, bucket[p]))
             [] pc[p] = "F2" /\ ~KeyInBktAtAddr(arg[p].key, bucket[p])
                -> (c.op[p] = "Find" /\ c.arg[p] = arg[p] /\ c.res[p] = NULL)
             [] pc[p] = "F3"
                -> (c.op[p] = "Find" /\ c.arg[p] = arg[p] /\ c.res[p] = r[p])
             [] pc[p] \in {"I1", "I3", "I4"}
                -> (c.op[p] = "Insert" /\ c.arg[p] = arg[p] /\ c.res[p] = BOT)
             [] pc[p] = "I2" /\ KeyInBktAtAddr(arg[p].key, bucket[p])
                -> (c.op[p] = "Insert" /\ c.arg[p] = arg[p] /\ c.res[p] = ValOfKeyInBktAtAddr(arg[p].key, bucket[p]))
             [] pc[p] = "I2" /\ ~KeyInBktAtAddr(arg[p].key, bucket[p])
                -> (c.op[p] = "Insert" /\ c.arg[p] = arg[p] /\ c.res[p] = BOT)
             [] pc[p] = "I5"
                -> (c.op[p] = "Insert" /\ c.arg[p] = arg[p] /\ c.res[p] = r[p])
             [] pc[p] \in {"U1", "U2", "U3", "U4"}
                -> (c.op[p] = "Upsert" /\ c.arg[p] = arg[p] /\ c.res[p] = BOT)
             [] pc[p] = "U5"
                -> (c.op[p] = "Upsert" /\ c.arg[p] = arg[p] /\ c.res[p] = r[p])
             [] pc[p] \in {"R1", "R3", "R4"}
                -> (c.op[p] = "Remove" /\ c.arg[p] = arg[p] /\ c.res[p] = BOT)
             [] pc[p] = "R2" /\ KeyInBktAtAddr(arg[p].key, bucket[p])
                -> (c.op[p] = "Remove" /\ c.arg[p] = arg[p] /\ c.res[p] = BOT)
             [] pc[p] = "R2" /\ ~KeyInBktAtAddr(arg[p].key, bucket[p])
                -> (c.op[p] = "Remove" /\ c.arg[p] = arg[p] /\ c.res[p] = NULL)
             [] pc[p] = "R5"
                -> (c.op[p] = "Remove" /\ c.arg[p] = arg[p] /\ c.res[p] = r[p])}
                
SPrime == 
     {c \in ConfigDomain :
        /\ c.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]])' 
                                             THEN ValOfKeyInBktAtAddr(k, A[Hash[k]])' 
                                             ELSE NULL]
        /\ \A p \in ProcSet :
           CASE pc'[p] = RemainderID
                -> (c.op[p] = BOT /\ c.arg[p] = BOT /\ c.res[p] = BOT)
             [] pc'[p] = "F1"
                -> (c.op[p] = "Find" /\ c.arg[p] = arg'[p] /\ c.res[p] = BOT)
             [] pc'[p] = "F2" /\ KeyInBktAtAddr(arg[p].key, bucket[p])'
                -> (c.op[p] = "Find" /\ c.arg[p] = arg'[p] /\ c.res[p] = ValOfKeyInBktAtAddr(arg[p].key, bucket[p])')
             [] pc'[p] = "F2" /\ ~KeyInBktAtAddr(arg[p].key, bucket[p])'
                -> (c.op[p] = "Find" /\ c.arg[p] = arg'[p] /\ c.res[p] = NULL)
             [] pc'[p] = "F3"
                -> (c.op[p] = "Find" /\ c.arg[p] = arg'[p] /\ c.res[p] = r'[p])
             [] pc'[p] \in {"I1", "I3", "I4"}
                -> (c.op[p] = "Insert" /\ c.arg[p] = arg'[p] /\ c.res[p] = BOT)
             [] pc'[p] = "I2" /\ KeyInBktAtAddr(arg[p].key, bucket[p])'
                -> (c.op[p] = "Insert" /\ c.arg[p] = arg'[p] /\ c.res[p] = ValOfKeyInBktAtAddr(arg[p].key, bucket[p])')
             [] pc'[p] = "I2" /\ ~KeyInBktAtAddr(arg[p].key, bucket[p])'
                -> (c.op[p] = "Insert" /\ c.arg[p] = arg'[p] /\ c.res[p] = BOT)
             [] pc'[p] = "I5"
                -> (c.op[p] = "Insert" /\ c.arg[p] = arg'[p] /\ c.res[p] = r'[p])
             [] pc'[p] \in {"U1", "U2", "U3", "U4"}
                -> (c.op[p] = "Upsert" /\ c.arg[p] = arg'[p] /\ c.res[p] = BOT)
             [] pc'[p] = "U5"
                -> (c.op[p] = "Upsert" /\ c.arg[p] = arg'[p] /\ c.res[p] = r'[p])
             [] pc'[p] \in {"R1", "R3", "R4"}
                -> (c.op[p] = "Remove" /\ c.arg[p] = arg'[p] /\ c.res[p] = BOT)
             [] pc'[p] = "R2" /\ KeyInBktAtAddr(arg[p].key, bucket[p])'
                -> (c.op[p] = "Remove" /\ c.arg[p] = arg'[p] /\ c.res[p] = BOT)
             [] pc'[p] = "R2" /\ ~KeyInBktAtAddr(arg[p].key, bucket[p])'
                -> (c.op[p] = "Remove" /\ c.arg[p] = arg'[p] /\ c.res[p] = NULL)
             [] pc'[p] = "R5"
                -> (c.op[p] = "Remove" /\ c.arg[p] = arg'[p] /\ c.res[p] = r'[p])}

LEMMA SPrimeRewrite == S' = SPrime
  BY ZenonT(120) DEF S, SPrime

THEOREM LinInit == Init => (S = {[state |-> [k \in KeyDomain |-> NULL],
                                  op    |-> [p \in ProcSet   |-> BOT],
                                  arg   |-> [p \in ProcSet   |-> BOT],
                                  res   |-> [p \in ProcSet   |-> BOT]]})
  <1> DEFINE m0 == [state |-> [k \in KeyDomain |-> NULL],
                    op    |-> [p \in ProcSet   |-> BOT],
                    arg   |-> [p \in ProcSet   |-> BOT],
                    res   |-> [p \in ProcSet   |-> BOT]]
  <1> SUFFICES ASSUME Init PROVE /\ m0 \in S
                                 /\ \A c \in S : c = m0
    OBVIOUS
  <1>1. m0 \in S
    <2>1. m0 \in ConfigDomain
      BY DEF ConfigDomain, StateDomain, OpDomain, ArgDomain, ResDomain
    <2>2. m0.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL]
      <3> SUFFICES ASSUME NEW k \in KeyDomain
                   PROVE  ~KeyInBktAtAddr(k, A[Hash[k]])
        OBVIOUS
      <3> QED
        BY HashDef DEF KeyInBktAtAddr, Init
    <2>3. \A p \in ProcSet : pc[p] = RemainderID
      BY DEF Init
    <2> SUFFICES \A p \in ProcSet : m0.op[p] = BOT /\ m0.arg[p] = BOT /\ m0.res[p] = BOT
      BY <2>1, <2>2, <2>3, RemDef, Zenon DEF S
    <2> QED
      OBVIOUS
  <1>2. ASSUME NEW c \in S PROVE c = m0
    <2> USE <1>2
    <2>1. c.state = [k \in KeyDomain |-> NULL]
      BY HashDef DEF KeyInBktAtAddr, Init, S
    <2>2. c.op = [p \in ProcSet   |-> BOT]
      BY RemDef, Zenon DEF S, Init, ConfigDomain
    <2>3. c.arg = [p \in ProcSet  |-> BOT]
      BY RemDef, Zenon DEF S, Init, ConfigDomain
    <2>4. c.res = [p \in ProcSet  |-> BOT]
      BY RemDef, Zenon DEF S, Init, ConfigDomain
    <2>5. c \in ConfigDomain
      BY DEF S
    <2> QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF ConfigDomain
  <1> QED  
    BY <1>1, <1>2

THEOREM LinNE == TypeOK => S # {}
  <1> SUFFICES ASSUME TypeOK
               PROVE  \E c \in ConfigDomain : c \in S
    BY Zenon DEF S
  <1> USE DEF TypeOK
  <1> DEFINE op == [p \in ProcSet |-> CASE pc[p] = RemainderID -> BOT
                                        [] pc[p] \in {"F1", "F2", "F3"} -> "Find"
                                        [] pc[p] \in {"I1", "I2", "I3", "I4", "I5"} -> "Insert"
                                        [] pc[p] \in {"U1", "U2", "U3", "U4", "U5"} -> "Upsert"
                                        [] pc[p] \in {"R1", "R2", "R3", "R4", "R5"} -> "Remove"]
  <1>1. op \in [ProcSet -> OpDomain]
    BY DEF OpDomain, LineIDs
  <1> DEFINE carg == [p \in ProcSet |-> IF pc[p] = RemainderID THEN BOT ELSE arg[p]]
  <1>2. carg \in [ProcSet -> ArgDomain]
    BY DEF OpDomain, LineIDs, ArgDomain
  <1> DEFINE state == [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL]
  <1>3. state \in StateDomain
    <2> SUFFICES ASSUME NEW k \in KeyDomain,
                        KeyInBktAtAddr(k, A[Hash[k]])
                 PROVE  ValOfKeyInBktAtAddr(k, A[Hash[k]]) \in ValDomain
      BY DEF StateDomain
    <2>1. A[Hash[k]] \in AllocAddrs
      BY HashDef DEF KeyInBktAtAddr
    <2>2. PICK idx \in 1..Len(MemLocs[A[Hash[k]]]) : MemLocs[A[Hash[k]]][idx].key = k
      BY DEF KeyInBktAtAddr
    <2>3. idx = CHOOSE index \in 1..Len(MemLocs[A[Hash[k]]]) : MemLocs[A[Hash[k]]][index].key = k
      BY <2>2 
    <2>4. ValOfKeyInBktAtAddr(k, A[Hash[k]]) = MemLocs[A[Hash[k]]][idx].val
      BY <2>3, Zenon DEF ValOfKeyInBktAtAddr
    <2>5. MemLocs[A[Hash[k]]] \in Seq([key: KeyDomain, val: ValDomain])
      BY <2>1, Zenon
    <2>6. MemLocs[A[Hash[k]]][idx] \in [key: KeyDomain, val: ValDomain]
      BY <2>2, <2>5, ElementOfSeq, Zenon
    <2>7. MemLocs[A[Hash[k]]][idx].val \in ValDomain
      BY <2>6
    <2> QED
      BY <2>4, <2>7
  <1> DEFINE res == 
        [p \in ProcSet |->
           CASE pc[p] = RemainderID 
                -> BOT
             [] pc[p] = "F1"        
                -> BOT
             [] pc[p] = "F2" /\ KeyInBktAtAddr(arg[p].key, bucket[p])
                -> ValOfKeyInBktAtAddr(arg[p].key, bucket[p])
             [] pc[p] = "F2" /\ ~KeyInBktAtAddr(arg[p].key, bucket[p])
                -> NULL
             [] pc[p] = "F3"
                -> r[p]
             [] pc[p] \in {"I1", "I3", "I4"}   
                -> BOT
             [] pc[p] = "I2" /\ KeyInBktAtAddr(arg[p].key, bucket[p])
                -> ValOfKeyInBktAtAddr(arg[p].key, bucket[p])
             [] pc[p] = "I2" /\ ~KeyInBktAtAddr(arg[p].key, bucket[p])
                -> BOT
             [] pc[p] = "I5"
                -> r[p]
             [] pc[p] \in {"U1", "U2", "U3", "U4"}
                -> BOT
             [] pc[p] = "U5"
                -> r[p]
             [] pc[p] \in {"R1", "R3", "R4"}        
                -> BOT
             [] pc[p] = "R2" /\ KeyInBktAtAddr(arg[p].key, bucket[p])
                -> BOT
             [] pc[p] = "R2" /\ ~KeyInBktAtAddr(arg[p].key, bucket[p])
                -> NULL
             [] pc[p] = "R5"
                -> r[p]]
  <1>4. res \in [ProcSet -> ResDomain]
    <2> SUFFICES ASSUME NEW p \in ProcSet
                 PROVE  res[p] \in ResDomain
      BY Zenon
    <2> USE RemDef
    <2>1. CASE pc[p] = RemainderID
      BY <2>1 DEF ResDomain
    <2>2. CASE pc[p] = "F1"
      BY <2>2 DEF ResDomain
    <2>3. CASE pc[p] = "F2" /\ KeyInBktAtAddr(arg[p].key, bucket[p])
      <3> SUFFICES ValOfKeyInBktAtAddr(arg[p].key, bucket[p]) \in ValDomain
        BY <2>3 DEF ResDomain
      <3>1. PICK idx \in 1..Len(MemLocs[bucket[p]]) : MemLocs[bucket[p]][idx].key = arg[p].key
        BY Zenon, <2>3 DEF KeyInBktAtAddr
      <3>2. ValOfKeyInBktAtAddr(arg[p].key, bucket[p]) = 
            MemLocs[bucket[p]][CHOOSE index \in 1..Len(MemLocs[bucket[p]]) : MemLocs[bucket[p]][index].key = arg[p].key].val
        BY Zenon DEF ValOfKeyInBktAtAddr
      <3>3. idx = CHOOSE index \in 1..Len(MemLocs[bucket[p]]) : MemLocs[bucket[p]][index].key = arg[p].key
        BY <3>1
      <3>4. ValOfKeyInBktAtAddr(arg[p].key, bucket[p]) = MemLocs[bucket[p]][idx].val
        BY <3>2, <3>3, Zenon
      <3>5. MemLocs[bucket[p]] \in Seq([key: KeyDomain, val: ValDomain])
        BY <2>3, Zenon DEF KeyInBktAtAddr
      <3>6. MemLocs[bucket[p]][idx] \in [key: KeyDomain, val: ValDomain]
        BY <3>1, <3>5, ElementOfSeq, Zenon
      <3>7. MemLocs[bucket[p]][idx].val \in ValDomain
        BY <3>6
      <3>8. ValOfKeyInBktAtAddr(arg[p].key, bucket[p]) \in ValDomain
        BY <3>4, <3>7
      <3> QED
        BY <2>3, <3>8
    <2>4. CASE pc[p] = "F2" /\ ~KeyInBktAtAddr(arg[p].key, bucket[p])
      BY <2>4 DEF ResDomain
    <2>5. CASE pc[p] = "F3"
      BY <2>5 DEF ResDomain
    <2>6. CASE pc[p] \in {"I1", "I3", "I4"}
      BY <2>6 DEF ResDomain
    <2>7. CASE pc[p] = "I2" /\ KeyInBktAtAddr(arg[p].key, bucket[p])
      <3> SUFFICES ValOfKeyInBktAtAddr(arg[p].key, bucket[p]) \in ValDomain
        BY <2>7 DEF ResDomain
      <3>1. PICK idx \in 1..Len(MemLocs[bucket[p]]) : MemLocs[bucket[p]][idx].key = arg[p].key
        BY Zenon, <2>7 DEF KeyInBktAtAddr
      <3>2. ValOfKeyInBktAtAddr(arg[p].key, bucket[p]) = 
            MemLocs[bucket[p]][CHOOSE index \in 1..Len(MemLocs[bucket[p]]) : MemLocs[bucket[p]][index].key = arg[p].key].val
        BY Zenon DEF ValOfKeyInBktAtAddr
      <3>3. idx = CHOOSE index \in 1..Len(MemLocs[bucket[p]]) : MemLocs[bucket[p]][index].key = arg[p].key
        BY <3>1
      <3>4. ValOfKeyInBktAtAddr(arg[p].key, bucket[p]) = MemLocs[bucket[p]][idx].val
        BY <3>2, <3>3, Zenon
      <3>5. MemLocs[bucket[p]] \in Seq([key: KeyDomain, val: ValDomain])
        BY <2>7, Zenon DEF KeyInBktAtAddr
      <3>6. MemLocs[bucket[p]][idx] \in [key: KeyDomain, val: ValDomain]
        BY <3>1, <3>5, ElementOfSeq, Zenon
      <3>7. MemLocs[bucket[p]][idx].val \in ValDomain
        BY <3>6
      <3>8. ValOfKeyInBktAtAddr(arg[p].key, bucket[p]) \in ValDomain
        BY <3>4, <3>7
      <3> QED
        BY <2>7, <3>8
    <2>8. CASE pc[p] = "I2" /\ ~KeyInBktAtAddr(arg[p].key, bucket[p])
      BY <2>8 DEF ResDomain
    <2>9. CASE pc[p] = "I5"
      BY <2>9 DEF ResDomain
    <2>10. CASE pc[p] \in {"U1", "U2", "U3", "U4"}
      BY <2>10 DEF ResDomain
    <2>11. CASE pc[p] = "U5"
      BY <2>11 DEF ResDomain
    <2>12. CASE pc[p] \in {"R1", "R3", "R4"}
      BY <2>12 DEF ResDomain
    <2>13. CASE pc[p] = "R2" /\ KeyInBktAtAddr(arg[p].key, bucket[p])
      BY <2>13 DEF ResDomain
    <2>14. CASE pc[p] = "R2" /\ ~KeyInBktAtAddr(arg[p].key, bucket[p])
      BY <2>14 DEF ResDomain
    <2>15. CASE pc[p] = "R5"
      BY <2>15 DEF ResDomain
    <2> QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, 
         <2>10, <2>11, <2>12, <2>13, <2>14, <2>15, Zenon DEF LineIDs
  <1> DEFINE c == [state |-> state, op |-> op, arg |-> carg, res |-> res]
  <1>5. c \in ConfigDomain
    BY <1>1, <1>2, <1>3, <1>4, Zenon DEF ConfigDomain
  <1>6. ASSUME NEW q \in ProcSet
          PROVE
            CASE pc[q] = RemainderID 
                  -> (c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT)
               [] pc[q] = "F1"
                  -> (c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
               [] pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                  -> (c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q]))
               [] pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                  -> (c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL)
               [] pc[q] = "F3"
                  -> (c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q])
               [] pc[q] \in {"I1", "I3", "I4"}
                  -> (c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
               [] pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                  -> (c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q]))
               [] pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                  -> (c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
               [] pc[q] = "I5"
                  -> (c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q])
               [] pc[q] \in {"U1", "U2", "U3", "U4"}
                  -> (c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
               [] pc[q] = "U5"
                  -> (c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q])
               [] pc[q] \in {"R1", "R3", "R4"}
                  -> (c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
               [] pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                  -> (c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
               [] pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                  -> (c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL)
               [] pc[q] = "R5"
                  -> (c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q])
    <2> USE <1>6, RemDef
    <2>1. CASE pc[q] = RemainderID
      BY <2>1, Zenon
    <2>2. CASE pc[q] = "F1"
      BY <2>2, Zenon
    <2>3. CASE pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
      BY <2>3, Zenon
    <2>4. CASE pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
      BY <2>4, Zenon
    <2>5. CASE pc[q] = "F3"
      BY <2>5, Zenon
    <2>6. CASE pc[q] \in {"I1", "I3", "I4"}
      BY <2>6, Zenon
    <2>7. CASE pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
      BY <2>7, Zenon
    <2>8. CASE pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
      BY <2>8, Zenon
    <2>9. CASE pc[q] = "I5"
      BY <2>9, Zenon
    <2>10. CASE pc[q] \in {"U1", "U2", "U3", "U4"}
      BY <2>10, Zenon
    <2>11. CASE pc[q] = "U5"
      BY <2>11, Zenon
    <2>12. CASE pc[q] \in {"R1", "R3", "R4"}
      BY <2>12, Zenon
    <2>13. CASE pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
      BY <2>13, Zenon
    <2>14. CASE pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
      BY <2>14, Zenon
    <2>15. CASE pc[q] = "R5"
      BY <2>15, Zenon
    <2> QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, 
         <2>10, <2>11, <2>12, <2>13, <2>14, <2>15, ZenonT(120) DEF LineIDs
  <1>7. c \in S
    BY <1>5, <1>6, Zenon DEF S
  <1> QED
    BY <1>5, <1>7, Zenon

THEOREM LinSingleton == TypeOK => Cardinality(S) = 1
  <1> SUFFICES ASSUME TypeOK
               PROVE  Cardinality(S) = 1
    OBVIOUS
  <1>1. ASSUME NEW c1 \in S, NEW c2 \in S
        PROVE  c1 = c2
    <2> USE <1>1
    <2> c1 \in ConfigDomain /\ c2 \in ConfigDomain
      BY DEF S
    <2> SUFFICES /\ c1.state = c2.state
                 /\ c1.op = c2.op
                 /\ c1.arg = c2.arg
                 /\ c1.res = c2.res
      BY DEF ConfigDomain
    <2>1. c1.state = c2.state
      BY DEF S
    <2>2. /\ c1.op = c2.op
          /\ c1.arg = c2.arg
          /\ c1.res = c2.res
      <3> SUFFICES ASSUME NEW p \in ProcSet
                   PROVE  /\ c1.op[p] = c2.op[p]
                          /\ c1.arg[p] = c2.arg[p]
                          /\ c1.res[p] = c2.res[p]
        BY DEF ConfigDomain
      <3> USE RemDef
      <3>1. CASE pc[p] = RemainderID
        BY <3>1, Zenon DEF S
      <3>2. CASE pc[p] \in {"F1", "F2", "F3"}
        BY <3>2, Zenon DEF S
      <3>3. CASE pc[p] \in {"I1", "I2", "I3", "I4", "I5"}
        BY <3>3, Zenon DEF S
      <3>4. CASE pc[p] \in {"U1", "U2", "U3", "U4", "U5"}
        BY <3>4, Zenon DEF S
      <3>5. CASE pc[p] \in {"R1", "R2", "R3", "R4", "R5"}
        BY <3>5, Zenon DEF S
      <3> QED
        BY <3>1, <3>2, <3>3, <3>4, <3>5 DEF LineIDs, Inv, TypeOK
    <2> QED
      BY <2>1, <2>2
  <1>2. PICK c \in S : TRUE
    BY LinNE 
  <1>3. S = {c}
    BY <1>1, <1>2
  <1>4. Cardinality(S) = 1
    BY <1>3, FS_Singleton, Zenon
  <1> QED
    BY <1>4

InvokerProc == CHOOSE p \in ProcSet : InvokeLine(p)

LEMMA UniqueInvoker == TypeOK => (\A q \in ProcSet : InvokeLine(q) => q = InvokerProc)
  <1> SUFFICES ASSUME NEW p1 \in ProcSet, InvokeLine(p1),
                      NEW p2 \in ProcSet, InvokeLine(p2), 
                      TypeOK, p1 # p2
               PROVE  FALSE
    BY DEF InvokerProc
  <1>1. pc[p1] = RemainderID
    BY DEF InvokeLine
  <1>2. pc'[p1] # RemainderID
    BY Zenon, RemDef DEF InvokeLine, TypeOK, OpNames, OpToInvocLine
  <1>3. \A q \in ProcSet : q # p2 => pc[q] = pc'[q]
    BY DEF InvokeLine
  <1> QED
    BY <1>1, <1>2, <1>3 

THEOREM LinInvocationLine ==
    Inv /\ InvocnAction => S' \in SUBSET Evolve(Invoke(S, InvokerProc, LineIDtoOp(pc'[InvokerProc]), arg'[InvokerProc]))
  <1> SUFFICES ASSUME Inv,
                      NEW p \in ProcSet,
                      InvokeLine(p)
               PROVE  S' \in SUBSET Evolve(Invoke(S, p, LineIDtoOp(pc'[p]), arg'[p]))
    BY UniqueInvoker DEF Inv, InvocnAction
  <1> SUFFICES ASSUME pc[p] = RemainderID,
                      NEW op \in OpNames,
                      pc' = [pc EXCEPT ![p] = OpToInvocLine(op)],
                      NEW new_arg \in ArgsOf(op),
                      arg' = [arg EXCEPT ![p] = new_arg],
                      UNCHANGED <<A, MemLocs, AllocAddrs, bucket, newbkt, r, ret>>
               PROVE  S' \in SUBSET Evolve(Invoke(S, p, LineIDtoOp(pc'[p]), arg'[p]))
    BY Zenon DEF InvokeLine
  <1>A. LineIDtoOp(pc'[p]) = op
    BY ZenonT(120) DEF Inv, TypeOK, OpToInvocLine, LineIDtoOp, OpNames
  <1>B. arg'[p] \in ArgsOf(op)
    BY DEF Inv, TypeOK 
  <1> SUFFICES ASSUME NEW c \in ConfigDomain,
                      c \in S'
               PROVE  c \in Evolve(Invoke(S, p, op, arg'[p]))
    BY <1>A, Zenon DEF S
  <1> USE DEF Inv, TypeOK
  <1> DEFINE c_pred == [state |-> c.state,
                        op    |-> [c.op EXCEPT ![p] = BOT],
                        arg   |-> [c.arg EXCEPT ![p] = BOT],
                        res   |-> [c.res EXCEPT ![p] = BOT]]
  <1>1. c_pred \in ConfigDomain
    <2>1. c_pred.state \in StateDomain
      BY DEF ConfigDomain
    <2>2. c_pred.op \in [ProcSet -> OpDomain]
      BY DEF ConfigDomain, OpDomain
    <2>3. c_pred.arg \in [ProcSet -> ArgDomain]
      BY DEF ConfigDomain, ArgDomain
    <2>4. c_pred.res \in [ProcSet -> ResDomain]
      BY DEF ConfigDomain, ResDomain
    <2> QED
      BY <2>1, <2>2, <2>3, <2>4 DEF ConfigDomain
  <1>2. c_pred \in S
    <2>1. c_pred.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL]
      <3>1. c_pred.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL]
        <4>1. c_pred.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]])' THEN ValOfKeyInBktAtAddr(k, A[Hash[k]])' ELSE NULL]
          BY Zenon, SPrimeRewrite DEF SPrime
        <4>2. \A k \in KeyDomain : KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
          BY Zenon DEF KeyInBktAtAddr
        <4>3. \A k \in KeyDomain : ValOfKeyInBktAtAddr(k, A[Hash[k]])' = ValOfKeyInBktAtAddr(k, A[Hash[k]])
          <5> SUFFICES ASSUME NEW k \in KeyDomain
                        PROVE  ValOfKeyInBktAtAddr(k, A[Hash[k]])' = ValOfKeyInBktAtAddr(k, A[Hash[k]])
            OBVIOUS
          <5> bkt_arr == MemLocs'[A'[Hash[k]]]
          <5> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
          <5>1. ValOfKeyInBktAtAddr(k, A[Hash[k]])' = bkt_arr[idx].val
            BY DEF ValOfKeyInBktAtAddr
          <5>2. bkt_arr = MemLocs[A[Hash[k]]]
            BY Zenon
          <5> QED
            BY <5>1, <5>2, ZenonT(30) DEF ValOfKeyInBktAtAddr
        <4> QED
          BY <4>1, <4>2, <4>3
      <3> QED
        BY <3>1
    <2>2. ASSUME NEW q \in ProcSet
            PROVE
                CASE pc[q] = RemainderID 
                    -> (c_pred.op[q] = BOT /\ c_pred.arg[q] = BOT /\ c_pred.res[q] = BOT)
                  [] pc[q] = "F1"
                    -> (c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q]))
                  [] pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = NULL)
                  [] pc[q] = "F3"
                    -> (c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q])
                  [] pc[q] \in {"I1", "I3", "I4"}
                    -> (c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q]))
                  [] pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "I5"
                    -> (c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q])
                  [] pc[q] \in {"U1", "U2", "U3", "U4"}
                    -> (c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "U5"
                    -> (c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q])
                  [] pc[q] \in {"R1", "R3", "R4"}
                    -> (c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = NULL)
                  [] pc[q] = "R5"
                    -> (c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q])
      <3> USE <2>2
      <3>1. CASE pc[q] = RemainderID
        <4> SUFFICES c_pred.op[q] = BOT /\ c_pred.arg[q] = BOT /\ c_pred.res[q] = BOT
          BY <3>1, RemDef, Zenon
        <4>A. CASE q = p
          BY <4>A DEF ConfigDomain
        <4> SUFFICES ASSUME q # p
                      PROVE  c_pred.op[q] = BOT /\ c_pred.arg[q] = BOT /\ c_pred.res[q] = BOT
          BY <4>A
        <4>1. q # p
          BY <3>1, RemDef, Zenon
        <4>X. c_pred.op = [c.op EXCEPT ![p] = BOT]
          OBVIOUS
        <4>Y. \A p1 \in ProcSet : p1 # p => c_pred.op[p1] = c.op[p1]
          OBVIOUS

        <4>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
          BY <4>1
        <4>3. pc'[q] = RemainderID
          BY <3>1, RemDef, Zenon
        <4>4. c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
          BY <4>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2, <4>4
      <3>2. CASE pc[q] = "F1"
        <4> USE <3>2
        <4> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
          BY RemDef, Zenon
        <4>1. q # p
          BY RemDef, Zenon
        <4>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
          BY <4>1
        <4>3. pc'[q] = "F1"
          BY RemDef, Zenon
        <4>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY <4>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2, <4>4
      <3>3. CASE pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
        <4> USE <3>3
        <4> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
          BY RemDef, Zenon
        <4>1. q # p
          BY RemDef, Zenon
        <4>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
          BY <4>1
        <4>3. pc'[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
          BY RemDef, Zenon DEF KeyInBktAtAddr
        <4>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
          BY <4>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
          <5> DEFINE bkt_arr == MemLocs'[bucket'[q]]
          <5> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg'[q].key
          <5>1. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = bkt_arr[idx].val
            BY Zenon DEF ValOfKeyInBktAtAddr
          <5>2. bkt_arr = MemLocs[bucket[q]]
            BY Zenon
          <5>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
            BY <4>1, Zenon
          <5>4. ValOfKeyInBktAtAddr(arg[q].key, bucket[q]) =
                MemLocs[bucket[q]][CHOOSE index \in 1..Len(MemLocs[bucket[q]]) : MemLocs[bucket[q]][index].key = arg[q].key].val
            BY Zenon DEF ValOfKeyInBktAtAddr
          <5>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q]) = bkt_arr[idx].val
            BY <5>2, <5>3, <5>4, Zenon
          <5> QED
            BY <5>1, <5>5
        <4> QED
          BY <4>2, <4>4, <4>5
      <3>4. CASE pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
        <4> USE <3>4
        <4> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = NULL
          BY RemDef, Zenon
        <4>1. q # p
          BY RemDef, Zenon
        <4>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
          BY <4>1
        <4>3. pc'[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
          BY RemDef, Zenon DEF KeyInBktAtAddr
        <4>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
          BY <4>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2, <4>4
      <3>5. CASE pc[q] = "F3"
        <4> USE <3>5
        <4> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
          BY <3>5, RemDef, Zenon
        <4>1. q # p
          BY RemDef, Zenon
        <4>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
          BY <4>1
        <4>3. pc'[q] = "F3"
          BY <3>5, RemDef, Zenon
        <4>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
          BY <4>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2, <4>4
      <3>6. CASE pc[q] \in {"I1", "I3", "I4"}
        <4> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
          BY <3>6, RemDef, Zenon
        <4>1. q # p
          BY <3>6, RemDef, Zenon
        <4>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
          BY <4>1
        <4>3. pc'[q] \in {"I1", "I3", "I4"}
          BY <3>6, RemDef, Zenon
        <4>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY <4>1, <4>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2, <4>4
      <3>7. CASE pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
        <4> USE <3>7
        <4> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
          BY RemDef, Zenon
        <4>1. q # p
          BY RemDef, Zenon
        <4>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
          BY <4>1
        <4>3. pc'[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
          BY RemDef, Zenon DEF KeyInBktAtAddr
        <4>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
          BY <4>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
          <5> DEFINE bkt_arr == MemLocs'[bucket'[q]]
          <5> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg'[q].key
          <5>1. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = bkt_arr[idx].val
            BY Zenon DEF ValOfKeyInBktAtAddr
          <5>2. bkt_arr = MemLocs[bucket[q]]
            BY Zenon
          <5>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
            BY <4>1, Zenon
          <5>4. ValOfKeyInBktAtAddr(arg[q].key, bucket[q]) =
                MemLocs[bucket[q]][CHOOSE index \in 1..Len(MemLocs[bucket[q]]) : MemLocs[bucket[q]][index].key = arg[q].key].val
            BY Zenon DEF ValOfKeyInBktAtAddr
          <5>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q]) = bkt_arr[idx].val
            BY <5>2, <5>3, <5>4, Zenon
          <5> QED
            BY <5>1, <5>5
        <4> QED
          BY <4>2, <4>4, <4>5
      <3>8. CASE pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
        <4> USE <3>8
        <4> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
          BY RemDef, Zenon
        <4>1. q # p
          BY RemDef, Zenon
        <4>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
          BY <4>1
        <4>3. pc'[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
          BY RemDef, Zenon DEF KeyInBktAtAddr
        <4>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY <4>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2, <4>4
      <3>9. CASE pc[q] = "I5"
        <4> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
          BY <3>9, RemDef, Zenon
        <4>1. q # p
          BY <3>9, RemDef, Zenon
        <4>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
          BY <4>1
        <4>3. pc'[q] = "I5"
          BY <3>9, RemDef, Zenon
        <4>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
          BY <4>1, <4>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2, <4>4
      <3>10. CASE pc[q] \in {"U1", "U2", "U3", "U4"}
        <4> USE <3>10
        <4> SUFFICES c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
          BY RemDef, Zenon
        <4>1. q # p
          BY RemDef, Zenon
        <4>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
          BY <4>1
        <4>3. pc'[q] \in {"U1", "U2", "U3", "U4"}
          BY RemDef, Zenon
        <4>4. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY <4>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2, <4>4
      <3>11. CASE pc[q] = "U5"
        <4> USE <3>11
        <4> SUFFICES c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
          BY RemDef, Zenon
        <4>1. q # p
          BY RemDef, Zenon
        <4>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
          BY <4>1
        <4>3. pc'[q] = "U5"
          BY RemDef, Zenon
        <4>4. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
          BY <4>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2, <4>4
      <3>12. CASE pc[q] \in {"R1", "R3", "R4"}
        <4> USE <3>12
        <4> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
          BY RemDef, Zenon
        <4>1. q # p
          BY RemDef, Zenon
        <4>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
          BY <4>1
        <4>3. pc'[q] \in {"R1", "R3", "R4"}
          BY RemDef, Zenon
        <4>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY <4>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2, <4>4
      <3>13. CASE pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
        <4> USE <3>13
        <4> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
          BY RemDef, Zenon
        <4>1. q # p
          BY RemDef, Zenon
        <4>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
          BY <4>1
        <4>3. pc'[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
          BY RemDef, Zenon DEF KeyInBktAtAddr
        <4>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY <4>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2, <4>4
      <3>14. CASE pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
        <4> USE <3>14
        <4> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = NULL
          BY RemDef, Zenon
        <4>1. q # p
          BY RemDef, Zenon
        <4>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
          BY <4>1
        <4>3. pc'[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
          BY RemDef, Zenon DEF KeyInBktAtAddr
        <4>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
          BY <4>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2, <4>4
      <3>15. CASE pc[q] = "R5"
        <4> USE <3>15
        <4> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
          BY RemDef, Zenon
        <4>1. q # p
          BY RemDef, Zenon
        <4>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
          BY <4>1
        <4>3. pc'[q] = "R5"
          BY RemDef, Zenon
        <4>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
          BY <4>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2, <4>4
      <3> QED
        BY RemDef, ZenonT(120),
            <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9, 
            <3>10, <3>11, <3>12, <3>13, <3>14, <3>15
        DEF LineIDs
    <2> QED
      BY <1>1, <2>1, <2>2, Zenon DEF S
  <1>3. c_pred.op[p] = BOT /\ c_pred.arg[p] = BOT /\ c_pred.res[p] = BOT
    BY <1>1 DEF ConfigDomain
  <1>4. c.op[p] = op /\ c.arg[p] = arg'[p] /\ c.res[p] = BOT
    <2>1. CASE op = "Find"   /\ pc'[p] = "F1"
      BY <2>1, Zenon, RemDef, SPrimeRewrite DEF SPrime
    <2>2. CASE op = "Insert" /\ pc'[p] = "I1"
      BY <2>2, Zenon, RemDef, SPrimeRewrite DEF SPrime
    <2>3. CASE op = "Upsert" /\ pc'[p] = "U1"
      BY <2>3, Zenon, RemDef, SPrimeRewrite DEF SPrime
    <2>4. CASE op = "Remove" /\ pc'[p] = "R1"
      BY <2>4, Zenon, RemDef, SPrimeRewrite DEF SPrime
    <2> QED
      BY <2>1, <2>2, <2>3, <2>4, Zenon DEF OpNames, OpToInvocLine
  <1>5. c \in Invoke(S, p, op, new_arg)
    <2>1. c.op = [c_pred.op EXCEPT ![p] = op]
      BY <1>4, Zenon DEF ConfigDomain
    <2>2. c.arg = [c_pred.arg EXCEPT ![p] = new_arg]
      BY <1>4, Zenon DEF ConfigDomain
    <2>3. c.res = [c_pred.res EXCEPT ![p] = BOT]
      BY <1>4, Zenon DEF ConfigDomain
    <2> QED
      BY <1>2, <1>3, <2>1, <2>2, <2>3, Zenon DEF Invoke
  <1> QED
    BY <1>5, EmptySeqEvolve

ReturnProc == CHOOSE p \in ProcSet : (\E LineAction \in RetLines(p) : LineAction)

LEMMA UniqueReturner == TypeOK => (\A q \in ProcSet : (\E LineAction \in RetLines(q) : LineAction) => q = ReturnProc)
  <1> SUFFICES ASSUME TypeOK,
                      NEW p1 \in ProcSet,
                      NEW LA1 \in RetLines(p1), LA1,
                      NEW p2 \in ProcSet,
                      NEW LA2 \in RetLines(p2), LA2,
                      p1 # p2
               PROVE  FALSE
    BY Zenon DEF ReturnProc
  <1>1. pc[p1] # RemainderID
    BY RemDef DEF RetLines, F3, I5, U5, R5
  <1>2. pc'[p1] = RemainderID
    BY DEF RetLines, F3, I5, U5, R5, TypeOK
  <1>3. \A q \in ProcSet : q # p2 => pc[q] = pc'[q]
    BY DEF RetLines, F3, I5, U5, R5, TypeOK
  <1> QED
    BY <1>1, <1>2, <1>3
    
THEOREM LinReturnLine == 
    Inv /\ ReturnAction => S' \in SUBSET Filter(Evolve(S), ReturnProc, ret'[ReturnProc])
  <1> SUFFICES ASSUME Inv,
                      NEW p \in ProcSet,
                      NEW LineAction \in RetLines(p),
                      LineAction
               PROVE  S' \in SUBSET Filter(Evolve(S), ReturnProc, ret'[ReturnProc])
    BY Zenon DEF ReturnAction
  <1> SUFFICES S' \in SUBSET Filter(Evolve(S), p, ret'[p])
    BY UniqueReturner, Zenon DEF Inv
  <1> SUFFICES ASSUME NEW c \in ConfigDomain,
                      c \in S'
               PROVE  c \in Filter(Evolve(S), p, ret'[p])
    BY Zenon DEF S
  <1>1. pc'[p] = RemainderID
    BY DEF RetLines, F3, I5, U5, R5, TypeOK, Inv
  <1>2. c.op[p] = BOT /\ c.arg[p] = BOT /\ c.res[p] = BOT
    BY <1>1, RemDef, SPrimeRewrite, Zenon DEF SPrime
  <1>3. CASE LineAction = F3(p)
    <2> USE <1>3 DEF F3, TypeOK, Inv
    <2> DEFINE c_pred == [state |-> c.state,
                          op    |-> [c.op EXCEPT ![p] = "Find"],
                          arg   |-> [c.arg EXCEPT ![p] = arg[p]],
                          res   |-> [c.res EXCEPT ![p] = r[p]]]
    <2>1. c_pred \in ConfigDomain
      <3>1. c_pred.state \in StateDomain
        BY DEF ConfigDomain
      <3>2. c_pred.op \in [ProcSet -> OpDomain]
        BY DEF ConfigDomain, OpDomain
      <3>3. c_pred.arg \in [ProcSet -> ArgDomain]
        BY DEF ConfigDomain, ArgDomain
      <3>4. c_pred.res \in [ProcSet -> ResDomain]
        BY DEF ConfigDomain, ResDomain
      <3> QED
        BY <3>1, <3>2, <3>3, <3>4 DEF ConfigDomain
    <2>2. c_pred \in S
      <3>1. c_pred.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL]
        <4>1. c_pred.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]])' THEN ValOfKeyInBktAtAddr(k, A[Hash[k]])' ELSE NULL]
          BY Zenon, SPrimeRewrite DEF SPrime
        <4>2. \A k \in KeyDomain : KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
          BY Zenon DEF KeyInBktAtAddr
        <4>3. \A k \in KeyDomain : ValOfKeyInBktAtAddr(k, A[Hash[k]])' = ValOfKeyInBktAtAddr(k, A[Hash[k]])
          <5> SUFFICES ASSUME NEW k \in KeyDomain
                        PROVE  ValOfKeyInBktAtAddr(k, A[Hash[k]])' = ValOfKeyInBktAtAddr(k, A[Hash[k]])
            OBVIOUS
          <5> bkt_arr == MemLocs'[A'[Hash[k]]]
          <5> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
          <5>1. ValOfKeyInBktAtAddr(k, A[Hash[k]])' = bkt_arr[idx].val
            BY DEF ValOfKeyInBktAtAddr
          <5>2. bkt_arr = MemLocs[A[Hash[k]]]
            BY Zenon
          <5> QED
            BY <5>1, <5>2, ZenonT(30) DEF ValOfKeyInBktAtAddr
        <4> QED
          BY <4>1, <4>2, <4>3
      <3>2. ASSUME NEW q \in ProcSet
            PROVE
                CASE pc[q] = RemainderID 
                    -> (c_pred.op[q] = BOT /\ c_pred.arg[q] = BOT /\ c_pred.res[q] = BOT)
                  [] pc[q] = "F1"
                    -> (c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q]))
                  [] pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = NULL)
                  [] pc[q] = "F3"
                    -> (c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q])
                  [] pc[q] \in {"I1", "I3", "I4"}
                    -> (c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q]))
                  [] pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "I5"
                    -> (c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q])
                  [] pc[q] \in {"U1", "U2", "U3", "U4"}
                    -> (c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "U5"
                    -> (c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q])
                  [] pc[q] \in {"R1", "R3", "R4"}
                    -> (c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = NULL)
                  [] pc[q] = "R5"
                    -> (c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q])
        <4> USE <3>2
        <4>1. CASE pc[q] = RemainderID
          <5> SUFFICES c_pred.op[q] = BOT /\ c_pred.arg[q] = BOT /\ c_pred.res[q] = BOT
            BY <4>1, RemDef, Zenon
          <5>1. q # p
            BY <4>1, RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = RemainderID
            BY <4>1, RemDef, Zenon
          <5>4. c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>2. CASE pc[q] = "F1"
          <5> USE <4>2
          <5> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "F1"
            BY RemDef, Zenon
          <5>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>3. CASE pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>3
          <5> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            <6> DEFINE bkt_arr == MemLocs'[bucket'[q]]
            <6> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg'[q].key
            <6>1. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = bkt_arr[idx].val
              BY Zenon DEF ValOfKeyInBktAtAddr
            <6>2. bkt_arr = MemLocs[bucket[q]]
              BY Zenon
            <6>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
              BY Zenon
            <6> QED
              BY <6>1, <6>2, <6>3, Isa DEF ValOfKeyInBktAtAddr
          <5> QED
            BY <5>2, <5>4, <5>5
        <4>4. CASE pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>4
          <5> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = NULL
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>5. CASE pc[q] = "F3"
          <5> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
            BY <4>5, RemDef, Zenon
          <5>1. CASE q = p
            BY <5>1 DEF ConfigDomain
          <5> SUFFICES ASSUME q # p
                        PROVE  c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
            BY <5>1
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            OBVIOUS
          <5>3. pc'[q] = "F3"
            BY <4>5, RemDef, Zenon
          <5>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>6. CASE pc[q] \in {"I1", "I3", "I4"}
          <5> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
            BY <4>6, RemDef, Zenon
          <5>1. q # p
            BY <4>6, RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] \in {"I1", "I3", "I4"}
            BY <4>6, RemDef, Zenon
          <5>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>7. CASE pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>7
          <5> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            <6> DEFINE bkt_arr == MemLocs'[bucket'[q]]
            <6> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg'[q].key
            <6>1. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = bkt_arr[idx].val
              BY Zenon DEF ValOfKeyInBktAtAddr
            <6>2. bkt_arr = MemLocs[bucket[q]]
              BY Zenon
            <6>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
              BY Zenon
            <6> QED
              BY <6>1, <6>2, <6>3, Isa DEF ValOfKeyInBktAtAddr
          <5> QED
            BY <5>2, <5>4, <5>5
        <4>8. CASE pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>8
          <5> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>9. CASE pc[q] = "I5"
          <5> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
            BY <4>9, RemDef, Zenon
          <5>1. q # p
            BY <4>9, RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "I5"
            BY <4>9, RemDef, Zenon
          <5>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>10. CASE pc[q] \in {"U1", "U2", "U3", "U4"}
          <5> USE <4>10
          <5> SUFFICES c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] \in {"U1", "U2", "U3", "U4"}
            BY RemDef, Zenon
          <5>4. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>11. CASE pc[q] = "U5"
          <5> USE <4>11
          <5> SUFFICES c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "U5"
            BY RemDef, Zenon
          <5>4. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>12. CASE pc[q] \in {"R1", "R3", "R4"}
          <5> USE <4>12
          <5> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] \in {"R1", "R3", "R4"}
            BY RemDef, Zenon
          <5>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>13. CASE pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>13
          <5> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>14. CASE pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>14
          <5> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = NULL
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>15. CASE pc[q] = "R5"
          <5> USE <4>15
          <5> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "R5"
            BY RemDef, Zenon
          <5>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4> QED
          BY RemDef, ZenonT(120),
              <4>1, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, 
              <4>10, <4>11, <4>12, <4>13, <4>14, <4>15
          DEF LineIDs
      <3> QED
        BY <2>1, <3>1, <3>2, Zenon DEF S
    <2>3. c_pred \in Evolve(S)
      BY <2>1, <2>2, EmptySeqEvolve
    <2>4. c.op = [c_pred.op EXCEPT ![p] = BOT]
      BY Zenon, <1>2 DEF ConfigDomain
    <2>5. c.arg = [c_pred.arg EXCEPT ![p] = BOT]
      BY Zenon, <1>2 DEF ConfigDomain
    <2>6. c.res = [c_pred.res EXCEPT ![p] = BOT]
      BY Zenon, <1>2 DEF ConfigDomain
    <2>7. c.state = c_pred.state
      OBVIOUS
    <2>8. c_pred.res[p] = ret'[p]
      BY Zenon DEF ConfigDomain
    <2> QED
      BY <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, Zenon DEF Filter
  <1>4. CASE LineAction = I5(p)
    <2> USE <1>4 DEF I5, TypeOK, Inv
    <2> DEFINE c_pred == [state |-> c.state,
                          op    |-> [c.op EXCEPT ![p] = "Insert"],
                          arg   |-> [c.arg EXCEPT ![p] = arg[p]],
                          res   |-> [c.res EXCEPT ![p] = r[p]]]
    <2>1. c_pred \in ConfigDomain
      <3>1. c_pred.state \in StateDomain
        BY DEF ConfigDomain
      <3>2. c_pred.op \in [ProcSet -> OpDomain]
        BY DEF ConfigDomain, OpDomain
      <3>3. c_pred.arg \in [ProcSet -> ArgDomain]
        BY DEF ConfigDomain, ArgDomain
      <3>4. c_pred.res \in [ProcSet -> ResDomain]
        BY DEF ConfigDomain, ResDomain
      <3> QED
        BY <3>1, <3>2, <3>3, <3>4 DEF ConfigDomain
    <2>2. c_pred \in S
      <3>1. c_pred.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL]
        <4>1. c_pred.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]])' THEN ValOfKeyInBktAtAddr(k, A[Hash[k]])' ELSE NULL]
          BY Zenon, SPrimeRewrite DEF SPrime
        <4>2. \A k \in KeyDomain : KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
          BY Zenon DEF KeyInBktAtAddr
        <4>3. \A k \in KeyDomain : ValOfKeyInBktAtAddr(k, A[Hash[k]])' = ValOfKeyInBktAtAddr(k, A[Hash[k]])
          <5> SUFFICES ASSUME NEW k \in KeyDomain
                        PROVE  ValOfKeyInBktAtAddr(k, A[Hash[k]])' = ValOfKeyInBktAtAddr(k, A[Hash[k]])
            OBVIOUS
          <5> bkt_arr == MemLocs'[A'[Hash[k]]]
          <5> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
          <5>1. ValOfKeyInBktAtAddr(k, A[Hash[k]])' = bkt_arr[idx].val
            BY DEF ValOfKeyInBktAtAddr
          <5>2. bkt_arr = MemLocs[A[Hash[k]]]
            BY Zenon
          <5> QED
            BY <5>1, <5>2, ZenonT(30) DEF ValOfKeyInBktAtAddr
        <4> QED
          BY <4>1, <4>2, <4>3
      <3>2. ASSUME NEW q \in ProcSet
            PROVE
                CASE pc[q] = RemainderID 
                    -> (c_pred.op[q] = BOT /\ c_pred.arg[q] = BOT /\ c_pred.res[q] = BOT)
                  [] pc[q] = "F1"
                    -> (c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q]))
                  [] pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = NULL)
                  [] pc[q] = "F3"
                    -> (c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q])
                  [] pc[q] \in {"I1", "I3", "I4"}
                    -> (c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q]))
                  [] pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "I5"
                    -> (c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q])
                  [] pc[q] \in {"U1", "U2", "U3", "U4"}
                    -> (c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "U5"
                    -> (c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q])
                  [] pc[q] \in {"R1", "R3", "R4"}
                    -> (c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = NULL)
                  [] pc[q] = "R5"
                    -> (c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q])
        <4> USE <3>2
        <4>1. CASE pc[q] = RemainderID
          <5> SUFFICES c_pred.op[q] = BOT /\ c_pred.arg[q] = BOT /\ c_pred.res[q] = BOT
            BY <4>1, RemDef, Zenon
          <5>1. q # p
            BY <4>1, RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = RemainderID
            BY <4>1, RemDef, Zenon
          <5>4. c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>2. CASE pc[q] = "F1"
          <5> USE <4>2
          <5> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "F1"
            BY RemDef, Zenon
          <5>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>3. CASE pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>3
          <5> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            <6> DEFINE bkt_arr == MemLocs'[bucket'[q]]
            <6> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg'[q].key
            <6>1. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = bkt_arr[idx].val
              BY Zenon DEF ValOfKeyInBktAtAddr
            <6>2. bkt_arr = MemLocs[bucket[q]]
              BY Zenon
            <6>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
              BY Zenon
            <6> QED
              BY <6>1, <6>2, <6>3, Isa DEF ValOfKeyInBktAtAddr
          <5> QED
            BY <5>2, <5>4, <5>5
        <4>4. CASE pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>4
          <5> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = NULL
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>5. CASE pc[q] = "F3"
          <5> USE <4>5
          <5> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
            BY <4>5, RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "F3"
            BY <4>5, RemDef, Zenon
          <5>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>6. CASE pc[q] \in {"I1", "I3", "I4"}
          <5> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
            BY <4>6, RemDef, Zenon
          <5>1. q # p
            BY <4>6, RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] \in {"I1", "I3", "I4"}
            BY <4>6, RemDef, Zenon
          <5>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>7. CASE pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>7
          <5> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            <6> DEFINE bkt_arr == MemLocs'[bucket'[q]]
            <6> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg'[q].key
            <6>1. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = bkt_arr[idx].val
              BY Zenon DEF ValOfKeyInBktAtAddr
            <6>2. bkt_arr = MemLocs[bucket[q]]
              BY Zenon
            <6>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
              BY Zenon
            <6> QED
              BY <6>1, <6>2, <6>3, Isa DEF ValOfKeyInBktAtAddr
          <5> QED
            BY <5>2, <5>4, <5>5
        <4>8. CASE pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>8
          <5> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>9. CASE pc[q] = "I5"
          <5> USE <4>9
          <5> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
            BY <4>9, RemDef, Zenon
          <5>1. CASE q = p
            BY <5>1 DEF ConfigDomain
          <5> SUFFICES ASSUME q # p
                        PROVE  c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
            BY <5>1
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            OBVIOUS
          <5>3. pc'[q] = "I5"
            BY <4>9, RemDef, Zenon
          <5>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>10. CASE pc[q] \in {"U1", "U2", "U3", "U4"}
          <5> USE <4>10
          <5> SUFFICES c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] \in {"U1", "U2", "U3", "U4"}
            BY RemDef, Zenon
          <5>4. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>11. CASE pc[q] = "U5"
          <5> USE <4>11
          <5> SUFFICES c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "U5"
            BY RemDef, Zenon
          <5>4. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>12. CASE pc[q] \in {"R1", "R3", "R4"}
          <5> USE <4>12
          <5> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] \in {"R1", "R3", "R4"}
            BY RemDef, Zenon
          <5>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>13. CASE pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>13
          <5> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>14. CASE pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>14
          <5> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = NULL
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>15. CASE pc[q] = "R5"
          <5> USE <4>15
          <5> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "R5"
            BY RemDef, Zenon
          <5>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4> QED
          BY RemDef, ZenonT(120),
              <4>1, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, 
              <4>10, <4>11, <4>12, <4>13, <4>14, <4>15
          DEF LineIDs
      <3> QED
        BY <2>1, <3>1, <3>2, Zenon DEF S
    <2>3. c_pred \in Evolve(S)
      BY <2>1, <2>2, EmptySeqEvolve
    <2>4. c.op = [c_pred.op EXCEPT ![p] = BOT]
      BY Zenon, <1>2 DEF ConfigDomain
    <2>5. c.arg = [c_pred.arg EXCEPT ![p] = BOT]
      BY Zenon, <1>2 DEF ConfigDomain
    <2>6. c.res = [c_pred.res EXCEPT ![p] = BOT]
      BY Zenon, <1>2 DEF ConfigDomain
    <2>7. c.state = c_pred.state
      OBVIOUS
    <2>8. c_pred.res[p] = ret'[p]
      BY Zenon DEF ConfigDomain
    <2> QED
      BY <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, Zenon DEF Filter
  <1>5. CASE LineAction = U5(p)
    <2> USE <1>5 DEF U5, TypeOK, Inv
    <2> DEFINE c_pred == [state |-> c.state,
                          op    |-> [c.op EXCEPT ![p] = "Upsert"],
                          arg   |-> [c.arg EXCEPT ![p] = arg[p]],
                          res   |-> [c.res EXCEPT ![p] = r[p]]]
    <2>1. c_pred \in ConfigDomain
      <3>1. c_pred.state \in StateDomain
        BY DEF ConfigDomain
      <3>2. c_pred.op \in [ProcSet -> OpDomain]
        BY DEF ConfigDomain, OpDomain
      <3>3. c_pred.arg \in [ProcSet -> ArgDomain]
        BY DEF ConfigDomain, ArgDomain
      <3>4. c_pred.res \in [ProcSet -> ResDomain]
        BY DEF ConfigDomain, ResDomain
      <3> QED
        BY <3>1, <3>2, <3>3, <3>4 DEF ConfigDomain
    <2>2. c_pred \in S
      <3>1. c_pred.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL]
        <4>1. c_pred.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]])' THEN ValOfKeyInBktAtAddr(k, A[Hash[k]])' ELSE NULL]
          BY Zenon, SPrimeRewrite DEF SPrime
        <4>2. \A k \in KeyDomain : KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
          BY Zenon DEF KeyInBktAtAddr
        <4>3. \A k \in KeyDomain : ValOfKeyInBktAtAddr(k, A[Hash[k]])' = ValOfKeyInBktAtAddr(k, A[Hash[k]])
          <5> SUFFICES ASSUME NEW k \in KeyDomain
                        PROVE  ValOfKeyInBktAtAddr(k, A[Hash[k]])' = ValOfKeyInBktAtAddr(k, A[Hash[k]])
            OBVIOUS
          <5> bkt_arr == MemLocs'[A'[Hash[k]]]
          <5> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
          <5>1. ValOfKeyInBktAtAddr(k, A[Hash[k]])' = bkt_arr[idx].val
            BY DEF ValOfKeyInBktAtAddr
          <5>2. bkt_arr = MemLocs[A[Hash[k]]]
            BY Zenon
          <5> QED
            BY <5>1, <5>2, ZenonT(30) DEF ValOfKeyInBktAtAddr
        <4> QED
          BY <4>1, <4>2, <4>3
      <3>2. ASSUME NEW q \in ProcSet
            PROVE
                CASE pc[q] = RemainderID 
                    -> (c_pred.op[q] = BOT /\ c_pred.arg[q] = BOT /\ c_pred.res[q] = BOT)
                  [] pc[q] = "F1"
                    -> (c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q]))
                  [] pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = NULL)
                  [] pc[q] = "F3"
                    -> (c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q])
                  [] pc[q] \in {"I1", "I3", "I4"}
                    -> (c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q]))
                  [] pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "I5"
                    -> (c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q])
                  [] pc[q] \in {"U1", "U2", "U3", "U4"}
                    -> (c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "U5"
                    -> (c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q])
                  [] pc[q] \in {"R1", "R3", "R4"}
                    -> (c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = NULL)
                  [] pc[q] = "R5"
                    -> (c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q])
        <4> USE <3>2
        <4>1. CASE pc[q] = RemainderID
          <5> SUFFICES c_pred.op[q] = BOT /\ c_pred.arg[q] = BOT /\ c_pred.res[q] = BOT
            BY <4>1, RemDef, Zenon
          <5>1. q # p
            BY <4>1, RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = RemainderID
            BY <4>1, RemDef, Zenon
          <5>4. c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>2. CASE pc[q] = "F1"
          <5> USE <4>2
          <5> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "F1"
            BY RemDef, Zenon
          <5>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>3. CASE pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>3
          <5> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            <6> DEFINE bkt_arr == MemLocs'[bucket'[q]]
            <6> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg'[q].key
            <6>1. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = bkt_arr[idx].val
              BY Zenon DEF ValOfKeyInBktAtAddr
            <6>2. bkt_arr = MemLocs[bucket[q]]
              BY Zenon
            <6>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
              BY Zenon
            <6> QED
              BY <6>1, <6>2, <6>3, Isa DEF ValOfKeyInBktAtAddr
          <5> QED
            BY <5>2, <5>4, <5>5
        <4>4. CASE pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>4
          <5> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = NULL
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>5. CASE pc[q] = "F3"
          <5> USE <4>5
          <5> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
            BY <4>5, RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "F3"
            BY <4>5, RemDef, Zenon
          <5>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>6. CASE pc[q] \in {"I1", "I3", "I4"}
          <5> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
            BY <4>6, RemDef, Zenon
          <5>1. q # p
            BY <4>6, RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] \in {"I1", "I3", "I4"}
            BY <4>6, RemDef, Zenon
          <5>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>7. CASE pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>7
          <5> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            <6> DEFINE bkt_arr == MemLocs'[bucket'[q]]
            <6> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg'[q].key
            <6>1. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = bkt_arr[idx].val
              BY Zenon DEF ValOfKeyInBktAtAddr
            <6>2. bkt_arr = MemLocs[bucket[q]]
              BY Zenon
            <6>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
              BY Zenon
            <6> QED
              BY <6>1, <6>2, <6>3, Isa DEF ValOfKeyInBktAtAddr
          <5> QED
            BY <5>2, <5>4, <5>5
        <4>8. CASE pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>8
          <5> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>9. CASE pc[q] = "I5"
          <5> USE <4>9
          <5> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
            BY <4>9, RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "I5"
            BY <4>9, RemDef, Zenon
          <5>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>10. CASE pc[q] \in {"U1", "U2", "U3", "U4"}
          <5> USE <4>10
          <5> SUFFICES c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] \in {"U1", "U2", "U3", "U4"}
            BY RemDef, Zenon
          <5>4. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>11. CASE pc[q] = "U5"
          <5> USE <4>11
          <5> SUFFICES c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
            BY RemDef, Zenon
          <5>1. CASE q = p
            BY <5>1 DEF ConfigDomain
          <5> SUFFICES ASSUME q # p
                        PROVE  c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
            BY <5>1
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            OBVIOUS
          <5>3. pc'[q] = "U5"
            BY RemDef, Zenon
          <5>4. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>12. CASE pc[q] \in {"R1", "R3", "R4"}
          <5> USE <4>12
          <5> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] \in {"R1", "R3", "R4"}
            BY RemDef, Zenon
          <5>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>13. CASE pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>13
          <5> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>14. CASE pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>14
          <5> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = NULL
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>15. CASE pc[q] = "R5"
          <5> USE <4>15
          <5> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "R5"
            BY RemDef, Zenon
          <5>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4> QED
          BY RemDef, ZenonT(120),
              <4>1, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, 
              <4>10, <4>11, <4>12, <4>13, <4>14, <4>15
          DEF LineIDs
      <3> QED
        BY <2>1, <3>1, <3>2, Zenon DEF S
    <2>3. c_pred \in Evolve(S)
      BY <2>1, <2>2, EmptySeqEvolve
    <2>4. c.op = [c_pred.op EXCEPT ![p] = BOT]
      BY Zenon, <1>2 DEF ConfigDomain
    <2>5. c.arg = [c_pred.arg EXCEPT ![p] = BOT]
      BY Zenon, <1>2 DEF ConfigDomain
    <2>6. c.res = [c_pred.res EXCEPT ![p] = BOT]
      BY Zenon, <1>2 DEF ConfigDomain
    <2>7. c.state = c_pred.state
      OBVIOUS
    <2>8. c_pred.res[p] = ret'[p]
      BY Zenon DEF ConfigDomain
    <2> QED
      BY <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, Zenon DEF Filter
  <1>6. CASE LineAction = R5(p)
    <2> USE <1>6 DEF R5, TypeOK, Inv
    <2> DEFINE c_pred == [state |-> c.state,
                          op    |-> [c.op EXCEPT ![p] = "Remove"],
                          arg   |-> [c.arg EXCEPT ![p] = arg[p]],
                          res   |-> [c.res EXCEPT ![p] = r[p]]]
    <2>1. c_pred \in ConfigDomain
      <3>1. c_pred.state \in StateDomain
        BY DEF ConfigDomain
      <3>2. c_pred.op \in [ProcSet -> OpDomain]
        BY DEF ConfigDomain, OpDomain
      <3>3. c_pred.arg \in [ProcSet -> ArgDomain]
        BY DEF ConfigDomain, ArgDomain
      <3>4. c_pred.res \in [ProcSet -> ResDomain]
        BY DEF ConfigDomain, ResDomain
      <3> QED
        BY <3>1, <3>2, <3>3, <3>4 DEF ConfigDomain
    <2>2. c_pred \in S
      <3>1. c_pred.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL]
        <4>1. c_pred.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]])' THEN ValOfKeyInBktAtAddr(k, A[Hash[k]])' ELSE NULL]
          BY Zenon, SPrimeRewrite DEF SPrime
        <4>2. \A k \in KeyDomain : KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
          BY Zenon DEF KeyInBktAtAddr
        <4>3. \A k \in KeyDomain : ValOfKeyInBktAtAddr(k, A[Hash[k]])' = ValOfKeyInBktAtAddr(k, A[Hash[k]])
          <5> SUFFICES ASSUME NEW k \in KeyDomain
                        PROVE  ValOfKeyInBktAtAddr(k, A[Hash[k]])' = ValOfKeyInBktAtAddr(k, A[Hash[k]])
            OBVIOUS
          <5> bkt_arr == MemLocs'[A'[Hash[k]]]
          <5> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
          <5>1. ValOfKeyInBktAtAddr(k, A[Hash[k]])' = bkt_arr[idx].val
            BY DEF ValOfKeyInBktAtAddr
          <5>2. bkt_arr = MemLocs[A[Hash[k]]]
            BY Zenon
          <5> QED
            BY <5>1, <5>2, ZenonT(30) DEF ValOfKeyInBktAtAddr
        <4> QED
          BY <4>1, <4>2, <4>3
      <3>2. ASSUME NEW q \in ProcSet
            PROVE
                CASE pc[q] = RemainderID 
                    -> (c_pred.op[q] = BOT /\ c_pred.arg[q] = BOT /\ c_pred.res[q] = BOT)
                  [] pc[q] = "F1"
                    -> (c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q]))
                  [] pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = NULL)
                  [] pc[q] = "F3"
                    -> (c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q])
                  [] pc[q] \in {"I1", "I3", "I4"}
                    -> (c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q]))
                  [] pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "I5"
                    -> (c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q])
                  [] pc[q] \in {"U1", "U2", "U3", "U4"}
                    -> (c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "U5"
                    -> (c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q])
                  [] pc[q] \in {"R1", "R3", "R4"}
                    -> (c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = NULL)
                  [] pc[q] = "R5"
                    -> (c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q])
        <4> USE <3>2
        <4>1. CASE pc[q] = RemainderID
          <5> SUFFICES c_pred.op[q] = BOT /\ c_pred.arg[q] = BOT /\ c_pred.res[q] = BOT
            BY <4>1, RemDef, Zenon
          <5>1. q # p
            BY <4>1, RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = RemainderID
            BY <4>1, RemDef, Zenon
          <5>4. c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>2. CASE pc[q] = "F1"
          <5> USE <4>2
          <5> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "F1"
            BY RemDef, Zenon
          <5>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>3. CASE pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>3
          <5> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            <6> DEFINE bkt_arr == MemLocs'[bucket'[q]]
            <6> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg'[q].key
            <6>1. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = bkt_arr[idx].val
              BY Zenon DEF ValOfKeyInBktAtAddr
            <6>2. bkt_arr = MemLocs[bucket[q]]
              BY Zenon
            <6>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
              BY Zenon
            <6> QED
              BY <6>1, <6>2, <6>3, Isa DEF ValOfKeyInBktAtAddr
          <5> QED
            BY <5>2, <5>4, <5>5
        <4>4. CASE pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>4
          <5> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = NULL
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>5. CASE pc[q] = "F3"
          <5> USE <4>5
          <5> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
            BY <4>5, RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "F3"
            BY <4>5, RemDef, Zenon
          <5>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>6. CASE pc[q] \in {"I1", "I3", "I4"}
          <5> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
            BY <4>6, RemDef, Zenon
          <5>1. q # p
            BY <4>6, RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] \in {"I1", "I3", "I4"}
            BY <4>6, RemDef, Zenon
          <5>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>7. CASE pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>7
          <5> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            <6> DEFINE bkt_arr == MemLocs'[bucket'[q]]
            <6> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg'[q].key
            <6>1. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = bkt_arr[idx].val
              BY Zenon DEF ValOfKeyInBktAtAddr
            <6>2. bkt_arr = MemLocs[bucket[q]]
              BY Zenon
            <6>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
              BY Zenon
            <6> QED
              BY <6>1, <6>2, <6>3, Isa DEF ValOfKeyInBktAtAddr
          <5> QED
            BY <5>2, <5>4, <5>5
        <4>8. CASE pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>8
          <5> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>9. CASE pc[q] = "I5"
          <5> USE <4>9
          <5> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
            BY <4>9, RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "I5"
            BY <4>9, RemDef, Zenon
          <5>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>10. CASE pc[q] \in {"U1", "U2", "U3", "U4"}
          <5> USE <4>10
          <5> SUFFICES c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] \in {"U1", "U2", "U3", "U4"}
            BY RemDef, Zenon
          <5>4. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>11. CASE pc[q] = "U5"
          <5> USE <4>11
          <5> SUFFICES c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
            BY RemDef, Zenon
          <5>1. q # p
            BY Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "U5"
            BY RemDef, Zenon
          <5>4. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>12. CASE pc[q] \in {"R1", "R3", "R4"}
          <5> USE <4>12
          <5> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] \in {"R1", "R3", "R4"}
            BY RemDef, Zenon
          <5>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>13. CASE pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>13
          <5> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>14. CASE pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>14
          <5> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = NULL
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>15. CASE pc[q] = "R5"
          <5> USE <4>15
          <5> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
            BY RemDef, Zenon
          <5>1. CASE q = p 
            BY <5>1 DEF ConfigDomain
          <5> SUFFICES ASSUME q # p
                        PROVE  c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
            BY <5>1
          <5>2. q # p
            OBVIOUS
          <5>3. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            OBVIOUS
          <5>4. pc'[q] = "R5"
            BY RemDef, Zenon
          <5>5. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>4, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>3, <5>5
        <4> QED
          BY RemDef, ZenonT(120),
              <4>1, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, 
              <4>10, <4>11, <4>12, <4>13, <4>14, <4>15
          DEF LineIDs
      <3> QED
        BY <2>1, <3>1, <3>2, Zenon DEF S
    <2>3. c_pred \in Evolve(S)
      BY <2>1, <2>2, EmptySeqEvolve
    <2>4. c.op = [c_pred.op EXCEPT ![p] = BOT]
      BY Zenon, <1>2 DEF ConfigDomain
    <2>5. c.arg = [c_pred.arg EXCEPT ![p] = BOT]
      BY Zenon, <1>2 DEF ConfigDomain
    <2>6. c.res = [c_pred.res EXCEPT ![p] = BOT]
      BY Zenon, <1>2 DEF ConfigDomain
    <2>7. c.state = c_pred.state
      OBVIOUS
    <2>8. c_pred.res[p] = ret'[p]
      BY Zenon DEF ConfigDomain
    <2> QED
      BY <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, Zenon DEF Filter
  <1> QED
    BY <1>3, <1>4, <1>5, <1>6, Zenon DEF RetLines
    
THEOREM LinIntermediateLine ==
    Inv /\ IntermAction => S' \in SUBSET Evolve(S)
  <1> SUFFICES ASSUME Inv,
                      NEW p \in ProcSet,
                      NEW LineAction \in IntLines(p),
                      LineAction
               PROVE  S' \in SUBSET Evolve(S)
    BY Zenon DEF IntermAction
  <1>1. CASE LineAction = F1(p)
    <2> USE <1>1 DEF F1
    <2> SUFFICES ASSUME NEW c \in ConfigDomain,
                        c \in S'
                 PROVE  c \in Evolve(S)
      BY Zenon DEF S
    <2> DEFINE c_pred == [state |-> c.state,
                          op    |-> c.op,
                          arg   |-> c.arg,
                          res   |-> [c.res EXCEPT ![p] = BOT]]
    <2>1. c_pred \in ConfigDomain
      <3>1. c_pred.state \in StateDomain
        BY DEF ConfigDomain
      <3>2. c_pred.op \in [ProcSet -> OpDomain]
        BY DEF ConfigDomain
      <3>3. c_pred.arg \in [ProcSet -> ArgDomain]
        BY DEF ConfigDomain
      <3>4. c_pred.res \in [ProcSet -> ResDomain]
        BY DEF ConfigDomain, ResDomain
      <3> QED
        BY <3>1, <3>2, <3>3, <3>4 DEF ConfigDomain
    <2>2. c_pred \in S
      <3>1. c_pred.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) 
                                                    THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) 
                                                    ELSE NULL]
        <4>1. c_pred.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]])'
                                                      THEN ValOfKeyInBktAtAddr(k, A[Hash[k]])'
                                                      ELSE NULL]
          BY SPrimeRewrite, Zenon DEF SPrime
        <4>2. \A k \in KeyDomain : /\ KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
                                    /\ ValOfKeyInBktAtAddr(k, A[Hash[k]]) = ValOfKeyInBktAtAddr(k, A[Hash[k]])'
          <5> SUFFICES ASSUME NEW k \in KeyDomain
                        PROVE  /\ KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
                              /\ ValOfKeyInBktAtAddr(k, A[Hash[k]]) = ValOfKeyInBktAtAddr(k, A[Hash[k]])'
            OBVIOUS
          <5>1. KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
            BY Zenon DEF KeyInBktAtAddr
          <5>2. ValOfKeyInBktAtAddr(k, A[Hash[k]]) = ValOfKeyInBktAtAddr(k, A[Hash[k]])'
            <6> DEFINE bkt_arr == MemLocs'[A'[Hash[k]]]
            <6> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
            <6>1. ValOfKeyInBktAtAddr(k, A[Hash[k]])' = bkt_arr[idx].val
              BY Zenon DEF ValOfKeyInBktAtAddr
            <6>2. bkt_arr = MemLocs[A[Hash[k]]]
              BY Zenon
            <6>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
              BY Zenon
            <6> QED
              BY <6>1, <6>2, <6>3, Isa DEF ValOfKeyInBktAtAddr
          <5>3. QED
            BY <5>1, <5>2
        <4> QED
          BY <4>1, <4>2   
      <3>2. ASSUME NEW q \in ProcSet
            PROVE
                CASE pc[q] = RemainderID 
                    -> (c_pred.op[q] = BOT /\ c_pred.arg[q] = BOT /\ c_pred.res[q] = BOT)
                  [] pc[q] = "F1"
                    -> (c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q]))
                  [] pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = NULL)
                  [] pc[q] = "F3"
                    -> (c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q])
                  [] pc[q] \in {"I1", "I3", "I4"}
                    -> (c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q]))
                  [] pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "I5"
                    -> (c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q])
                  [] pc[q] \in {"U1", "U2", "U3", "U4"}
                    -> (c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "U5"
                    -> (c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q])
                  [] pc[q] \in {"R1", "R3", "R4"}
                    -> (c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = NULL)
                  [] pc[q] = "R5"
                    -> (c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q])
        <4> USE <3>2 DEF TypeOK, Inv
        <4>1. CASE pc[q] = RemainderID
          <5> SUFFICES c_pred.op[q] = BOT /\ c_pred.arg[q] = BOT /\ c_pred.res[q] = BOT
            BY <4>1, RemDef, Zenon
          <5>1. q # p
            BY <4>1, RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = RemainderID
            BY <4>1, RemDef, Zenon
          <5>4. c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>2. CASE pc[q] = "F1"
          <5> USE <4>2
          <5> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
            BY RemDef, Zenon
          <5>1. CASE q = p
            <6> USE <5>1
            <6>1. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = BOT
              BY Zenon DEF ConfigDomain
            <6>2. pc'[q] = "F2"
              BY Zenon
            <6>3. c.op[q] = "Find" /\ c.arg[q] = arg[q]
              BY <6>2, SPrimeRewrite, ZenonT(30), RemDef DEF SPrime
            <6> QED
              BY <6>1, <6>3
          <5> SUFFICES ASSUME q # p
                        PROVE  c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
            BY <5>1
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            OBVIOUS
          <5>3. pc'[q] = "F1"
            BY RemDef, Zenon
          <5>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>3. CASE pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>3
          <5> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            <6> DEFINE bkt_arr == MemLocs'[bucket'[q]]
            <6> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg'[q].key
            <6>1. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = bkt_arr[idx].val
              BY Zenon DEF ValOfKeyInBktAtAddr
            <6>2. bkt_arr = MemLocs[bucket[q]]
              BY Zenon
            <6>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
              BY Zenon
            <6> QED
              BY <6>1, <6>2, <6>3, Isa DEF ValOfKeyInBktAtAddr
          <5> QED
            BY <5>2, <5>4, <5>5
        <4>4. CASE pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>4
          <5> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = NULL
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>5. CASE pc[q] = "F3"
          <5> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
            BY <4>5, RemDef, Zenon
          <5>1. q # p
            BY <4>5, RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "F3"
            BY <4>5, RemDef, Zenon
          <5>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>6. CASE pc[q] \in {"I1", "I3", "I4"}
          <5> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
            BY <4>6, RemDef, Zenon
          <5>1. q # p
            BY <4>6, RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] \in {"I1", "I3", "I4"}
            BY <4>6, RemDef, Zenon
          <5>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>7. CASE pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>7
          <5> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            <6> DEFINE bkt_arr == MemLocs'[bucket'[q]]
            <6> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg'[q].key
            <6>1. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = bkt_arr[idx].val
              BY Zenon DEF ValOfKeyInBktAtAddr
            <6>2. bkt_arr = MemLocs[bucket[q]]
              BY Zenon
            <6>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
              BY Zenon
            <6> QED
              BY <6>1, <6>2, <6>3, Isa DEF ValOfKeyInBktAtAddr
          <5> QED
            BY <5>2, <5>4, <5>5
        <4>8. CASE pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>8
          <5> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>9. CASE pc[q] = "I5"
          <5> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
            BY <4>9, RemDef, Zenon
          <5>1. q # p
            BY <4>9, RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "I5"
            BY <4>9, RemDef, Zenon
          <5>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>10. CASE pc[q] \in {"U1", "U2", "U3", "U4"}
          <5> USE <4>10
          <5> SUFFICES c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] \in {"U1", "U2", "U3", "U4"}
            BY RemDef, Zenon
          <5>4. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>11. CASE pc[q] = "U5"
          <5> USE <4>11
          <5> SUFFICES c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "U5"
            BY RemDef, Zenon
          <5>4. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>12. CASE pc[q] \in {"R1", "R3", "R4"}
          <5> USE <4>12
          <5> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] \in {"R1", "R3", "R4"}
            BY RemDef, Zenon
          <5>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>13. CASE pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>13
          <5> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>14. CASE pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>14
          <5> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = NULL
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4>15. CASE pc[q] = "R5"
          <5> USE <4>15
          <5> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
            BY RemDef, Zenon
          <5>1. q # p
            BY RemDef, Zenon
          <5>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
            BY <5>1
          <5>3. pc'[q] = "R5"
            BY RemDef, Zenon
          <5>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2, <5>4
        <4> QED
          BY RemDef, ZenonT(120),
              <4>1, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, 
              <4>10, <4>11, <4>12, <4>13, <4>14, <4>15
          DEF LineIDs
      <3> QED
        BY <2>1, <3>1, <3>2, Zenon DEF S
    <2>3. Delta(c_pred, p, c)
      <3> USE DEF TypeOK, Inv
      <3>1. c_pred.op[p] = "Find" /\ c_pred.arg[p] = arg[p] /\ c_pred.res[p] = BOT
        BY <2>2, RemDef, Zenon DEF S
      <3>2. c_pred.arg[p] \in ArgsOf("Find")
        BY <3>1, RemDef, Zenon DEF ArgsOf, LineIDtoOp
      <3> SUFFICES c.res = [c_pred.res EXCEPT ![p] = c_pred.state[c_pred.arg[p].key]]
        BY <3>1, <3>2 DEF Delta
      <3> SUFFICES c.res[p] = c_pred.state[c_pred.arg[p].key]
        BY <2>1, Zenon DEF ConfigDomain
      <3>3. KeyInBktAtAddr(arg[p].key, bucket[p])' = KeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]])
        BY Zenon DEF KeyInBktAtAddr
      <3>4. ValOfKeyInBktAtAddr(arg[p].key, bucket[p])' = ValOfKeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]])
        <4> DEFINE bkt_arr == MemLocs'[bucket'[p]]
        <4> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg'[p].key
        <4>1. ValOfKeyInBktAtAddr(arg[p].key, bucket[p])' = bkt_arr[idx].val
          BY Zenon DEF ValOfKeyInBktAtAddr
        <4> DEFINE bkt_arr2 == MemLocs[A[Hash[arg[p].key]]]
        <4> DEFINE idx2 == CHOOSE index \in 1..Len(bkt_arr2) : bkt_arr2[index].key = arg[p].key
        <4>2. ValOfKeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]]) = bkt_arr2[idx2].val
          BY Zenon DEF ValOfKeyInBktAtAddr
        <4>3. bkt_arr = bkt_arr2 /\ idx = idx2
          BY ZenonT(30)
        <4> QED
          BY <4>1, <4>2, <4>3
      <3>5. CASE KeyInBktAtAddr(arg[p].key, bucket[p])'
        <4> USE <3>5
        <4>1. c.res[p] = ValOfKeyInBktAtAddr(arg[p].key, bucket[p])'
          BY RemDef, Zenon DEF S
        <4>2. c.res[p] = ValOfKeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]])
          BY <3>4, <4>1
        <4>3. c_pred.arg[p].key \in KeyDomain /\ c_pred.arg[p] = arg[p]
          BY <3>1, <3>2 DEF ArgsOf
        <4>4. c_pred.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) 
                                                  THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) 
                                                  ELSE NULL]
          BY <2>2, Zenon DEF S
        <4>5. c_pred.state[c_pred.arg[p].key] = IF KeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]]) 
                                                   THEN ValOfKeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]]) 
                                                   ELSE NULL
          BY <4>3, <4>4, Zenon
        <4>6. c_pred.state[c_pred.arg[p].key] = ValOfKeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]]) 
          BY <3>3, <4>5
        <4> QED
          BY <4>2, <4>6
      <3>6. CASE ~KeyInBktAtAddr(arg[p].key, bucket[p])'
        <4> USE <3>6
        <4>1. c.res[p] = NULL
          BY RemDef, Zenon DEF S
        <4>2. c_pred.arg[p].key \in KeyDomain /\ c_pred.arg[p] = arg[p]
          BY <3>1, <3>2 DEF ArgsOf
        <4>3. c_pred.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) 
                                         THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) 
                                         ELSE NULL]
          BY <2>2, Zenon DEF S
        <4>4. c_pred.state[c_pred.arg[p].key] = IF KeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]]) 
                                                   THEN ValOfKeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]]) 
                                                   ELSE NULL
          BY <4>2, <4>3, Zenon
        <4>5. c_pred.state[c_pred.arg[p].key] = NULL 
          BY <3>3, <4>4
        <4> QED
          BY <4>1, <4>5
      <3> QED 
        BY <3>5, <3>6
    <2>4. c \in Evolve(S)
      BY <2>1, <2>2, <2>3, SingleDeltaEvolve
    <2> QED
      BY <2>4
  <1>2. CASE LineAction = F2(p)
    <2> USE <1>2 DEF F2
    <2> SUFFICES ASSUME NEW c \in ConfigDomain,
                        c \in S'
                 PROVE  c \in Evolve(S)
      BY Zenon DEF S
    <2> SUFFICES c \in S
      BY EmptySeqEvolve
    <2>1. c.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL]
      <3>1. c.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]])' THEN ValOfKeyInBktAtAddr(k, A[Hash[k]])' ELSE NULL]
        BY Zenon, SPrimeRewrite DEF SPrime
      <3>2. \A k \in KeyDomain : KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
        BY Zenon DEF KeyInBktAtAddr
      <3>3. \A k \in KeyDomain : ValOfKeyInBktAtAddr(k, A[Hash[k]])' = ValOfKeyInBktAtAddr(k, A[Hash[k]])
        <4> SUFFICES ASSUME NEW k \in KeyDomain
                     PROVE  ValOfKeyInBktAtAddr(k, A[Hash[k]])' = ValOfKeyInBktAtAddr(k, A[Hash[k]])
          OBVIOUS
        <4> bkt_arr == MemLocs'[A'[Hash[k]]]
        <4> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
        <4>1. ValOfKeyInBktAtAddr(k, A[Hash[k]])' = bkt_arr[idx].val
          BY DEF ValOfKeyInBktAtAddr
        <4>2. bkt_arr = MemLocs[A[Hash[k]]]
          BY Zenon
        <4> QED
          BY <4>1, <4>2, ZenonT(30) DEF ValOfKeyInBktAtAddr
      <3> QED
        BY <3>1, <3>2, <3>3
    <2>2. ASSUME NEW q \in ProcSet
          PROVE
              CASE pc[q] = RemainderID 
                  -> (c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT)
                [] pc[q] = "F1"
                  -> (c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                [] pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                  -> (c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q]))
                [] pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                  -> (c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL)
                [] pc[q] = "F3"
                  -> (c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q])
                [] pc[q] \in {"I1", "I3", "I4"}
                  -> (c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                [] pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                  -> (c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q]))
                [] pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                  -> (c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                [] pc[q] = "I5"
                  -> (c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q])
                [] pc[q] \in {"U1", "U2", "U3", "U4"}
                  -> (c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                [] pc[q] = "U5"
                  -> (c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q])
                [] pc[q] \in {"R1", "R3", "R4"}
                  -> (c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                [] pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                  -> (c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                [] pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                  -> (c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL)
                [] pc[q] = "R5"
                  -> (c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q])
      <3> USE <2>2 DEF TypeOK, Inv
      <3>1. \A k \in KeyDomain : KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, bucket[q])'
        BY Zenon DEF KeyInBktAtAddr
      <3>2. \A k \in KeyDomain : ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, bucket[q])
        <4> SUFFICES ASSUME NEW k \in KeyDomain
                      PROVE  ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, bucket[q])
          OBVIOUS
        <4> bkt_arr == MemLocs'[bucket'[q]]
        <4> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
        <4>1. ValOfKeyInBktAtAddr(k, bucket[q])' = bkt_arr[idx].val
          BY DEF ValOfKeyInBktAtAddr
        <4>2. bkt_arr = MemLocs[bucket[q]]
          BY Zenon
        <4> QED
          BY <4>1, <4>2, ZenonT(30) DEF ValOfKeyInBktAtAddr
      <3>3. CASE pc[q] = RemainderID
        <4> USE <3>3
        <4> SUFFICES c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
          BY RemDef, Zenon
        <4>1. pc'[q] = RemainderID
          BY RemDef, Zenon
        <4>2. c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
          BY <4>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2
      <3>4. CASE pc[q] = "F1"
        <4> USE <3>4
        <4> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY RemDef, Zenon
        <4>1. pc'[q] = "F1"
          BY RemDef, Zenon
        <4>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY <4>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2
      <3>5. CASE pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
        <4> USE <3>5
        <4> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
          BY RemDef, Zenon
        <4>1. CASE q = p
          <5> USE <4>1
          <5>1. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r'[q]
            BY SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            BY <5>1, Zenon
          <5> QED
            BY <5>2
        <4> SUFFICES ASSUME q # p
                     PROVE  c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
          BY <4>1
        <4>2. pc'[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
          BY RemDef, Zenon DEF KeyInBktAtAddr
        <4>3. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
          BY <4>2,  SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4>4. arg[q].key = arg'[q].key /\ arg[q].key \in KeyDomain
          BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
        <4>5. c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
          BY <4>3, <4>4, <3>2
        <4> QED
          BY <4>3, <4>5
      <3>6. CASE pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
        <4> USE <3>6
        <4> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
          BY RemDef, Zenon
        <4>1. CASE q = p
          <5> USE <4>1
          <5>1. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r'[q]
            BY SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
            BY <5>1, Zenon
          <5> QED
            BY <5>2
        <4> SUFFICES ASSUME q # p
                    PROVE  c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
          BY <4>1
        <4>2. pc'[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
          BY RemDef, Zenon DEF KeyInBktAtAddr
        <4>3. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
          BY <4>2,  SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>3
      <3>7. CASE pc[q] = "F3"
        <4> USE <3>7
        <4> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
          BY RemDef, Zenon
        <4>1. pc'[q] = "F3"
          BY RemDef, Zenon
        <4>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
          BY <4>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2 
      <3>8. CASE pc[q] \in {"I1", "I3", "I4"}
        <4> USE <3>8
        <4> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY RemDef, Zenon
        <4>1. pc'[q] \in {"I1", "I3", "I4"}
          BY RemDef, Zenon
        <4>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY <4>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2 
      <3>9. CASE pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
        <4> USE <3>9
        <4> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
          BY RemDef, Zenon
        <4>2. pc'[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
          BY RemDef, Zenon DEF KeyInBktAtAddr
        <4>3. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
          BY <4>2,  SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4>4. arg[q].key = arg'[q].key /\ arg[q].key \in KeyDomain
          BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
        <4>5. c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
          BY <4>3, <4>4, <3>2
        <4> QED
          BY <4>3, <4>5
      <3>10. CASE pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
        <4> USE <3>10
        <4> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY RemDef, Zenon
        <4>1. pc'[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
          BY RemDef, Zenon DEF KeyInBktAtAddr
        <4>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY <4>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2 
      <3>11. CASE pc[q] = "I5"
        <4> USE <3>11
        <4> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
          BY RemDef, Zenon
        <4>1. pc'[q] = "I5"
          BY RemDef, Zenon 
        <4>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
          BY <4>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2 
      <3>12. CASE pc[q] \in {"U1", "U2", "U3", "U4"}
        <4> USE <3>12
        <4> SUFFICES c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY RemDef, Zenon
        <4>1. pc'[q] \in {"U1", "U2", "U3", "U4"}
          BY RemDef, Zenon
        <4>2. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY <4>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2
      <3>13. CASE pc[q] = "U5" 
        <4> USE <3>13
        <4> SUFFICES c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
          BY RemDef, Zenon
        <4>1. pc'[q] = "U5"
          BY RemDef, Zenon
        <4>2. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
          BY <4>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2
      <3>14. CASE pc[q] \in {"R1", "R3", "R4"}
        <4> USE <3>14
        <4> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY RemDef, Zenon
        <4>1. pc'[q] \in {"R1", "R3", "R4"}
          BY RemDef, Zenon
        <4>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY <4>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2
      <3>15. CASE pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
        <4> USE <3>15
        <4> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY RemDef, Zenon
        <4>1. pc'[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
          BY RemDef, Zenon DEF KeyInBktAtAddr
        <4>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY <4>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2
      <3>16. CASE pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
        <4> USE <3>16
        <4> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
          BY RemDef, Zenon
        <4>1. pc'[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
          BY RemDef, Zenon DEF KeyInBktAtAddr
        <4>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
          BY <4>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2
      <3>17. CASE pc[q] = "R5"
        <4> USE <3>17
        <4> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
          BY RemDef, Zenon
        <4>1. pc'[q] = "R5" 
          BY RemDef, Zenon
        <4>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
          BY <4>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2
      <3> QED
          BY RemDef, ZenonT(120),
              <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9, <3>10, <3>11, 
              <3>12, <3>13, <3>14, <3>15, <3>16, <3>17
          DEF LineIDs
    <2> QED
      BY <2>1, <2>2, Zenon DEF S
  <1>3. CASE LineAction = I1(p)
    <2> USE <1>3 DEF I1
    <2> SUFFICES ASSUME NEW c \in ConfigDomain,
                        c \in S'
                 PROVE  c \in Evolve(S)
      BY Zenon DEF S
    <2>1. CASE ~KeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]])
      <3> USE <2>1 DEF TypeOK, Inv
      <3> SUFFICES c \in S
        BY EmptySeqEvolve
      <3>1. \A k \in KeyDomain : KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
        BY Zenon, HashDef DEF KeyInBktAtAddr
      <3>2. \A k \in KeyDomain : ValOfKeyInBktAtAddr(k, A[Hash[k]]) = ValOfKeyInBktAtAddr(k, A[Hash[k]])'
        <4> SUFFICES ASSUME NEW k \in KeyDomain
                     PROVE  ValOfKeyInBktAtAddr(k, A[Hash[k]]) = ValOfKeyInBktAtAddr(k, A[Hash[k]])'
          OBVIOUS
        <4> DEFINE bkt_arr == MemLocs'[A'[Hash[k]]]
        <4> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
        <4>1. ValOfKeyInBktAtAddr(k, A[Hash[k]])' = bkt_arr[idx].val
          BY Zenon DEF ValOfKeyInBktAtAddr
        <4>2. bkt_arr = MemLocs[A[Hash[k]]] /\ A'[Hash[k]] = A[Hash[k]]
          BY Zenon
        <4> QED
          BY <4>1, <4>2 DEF ValOfKeyInBktAtAddr
      <3>3. c.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) 
                                              THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) 
                                              ELSE NULL]
        <4>1. c.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]])' THEN ValOfKeyInBktAtAddr(k, A[Hash[k]])' ELSE NULL]
          BY SPrimeRewrite, Zenon DEF SPrime
        <4> QED
          BY <3>1, <3>2, <4>1
      <3>4. ASSUME NEW q \in ProcSet
            PROVE  
              CASE pc[q] = RemainderID 
                    -> (c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT)
                [] pc[q] = "F1"
                  -> (c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                [] pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                  -> (c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q]))
                [] pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                  -> (c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL)
                [] pc[q] = "F3"
                  -> (c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q])
                [] pc[q] \in {"I1", "I3", "I4"}
                  -> (c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                [] pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                  -> (c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q]))
                [] pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                  -> (c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                [] pc[q] = "I5"
                  -> (c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q])
                [] pc[q] \in {"U1", "U2", "U3", "U4"}
                  -> (c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                [] pc[q] = "U5"
                  -> (c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q])
                [] pc[q] \in {"R1", "R3", "R4"}
                  -> (c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                [] pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                  -> (c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                [] pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                  -> (c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL)
                [] pc[q] = "R5"
                  -> (c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q])
        <4> USE <3>4
        <4>1. CASE pc[q] = RemainderID
          <5> USE <4>1
          <5> SUFFICES c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. pc'[q] = RemainderID
            BY RemDef, Zenon
          <5>2. c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>2. CASE pc[q] = "F1"
          <5> USE <4>2
          <5> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. pc'[q] = "F1"
            BY RemDef, Zenon
          <5>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2    
        <4>3. CASE pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>3
          <5> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            BY RemDef, Zenon
          <5>1. pc'[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <5>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5>3. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            <6> DEFINE bkt_arr == MemLocs'[bucket'[q]]
            <6> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg'[q].key
            <6>1. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = bkt_arr[idx].val
              BY Zenon DEF ValOfKeyInBktAtAddr
            <6>2. bkt_arr = MemLocs[bucket[q]]
              BY Zenon
            <6>3. arg'[q].key = arg[q].key
              BY Zenon
            <6> QED
              BY <6>1, <6>2, <6>3, Isa DEF ValOfKeyInBktAtAddr
          <5> QED
            BY <5>2, <5>3
        <4>4. CASE pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>4
          <5> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
            BY RemDef, Zenon
          <5>1. pc'[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
            BY <5>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>5. CASE pc[q] = "F3"
          <5> USE <4>5
          <5> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY RemDef, Zenon
          <5>1. pc'[q] = "F3"
            BY RemDef, Zenon
          <5>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2 
        <4>6. CASE pc[q] \in {"I1", "I3", "I4"}
          <5> USE <4>6
          <5> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. CASE p = q
            <6> USE <5>1
            <6>1. arg[q].key = arg'[q].key /\ bucket'[q] = A[Hash[arg[q].key]]
              BY Zenon
            <6>2. pc'[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
              BY <6>1, Zenon DEF KeyInBktAtAddr
            <6>3. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
              BY <6>2, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>3
          <5> SUFFICES ASSUME p # q
                        PROVE  c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>1
          <5>2. pc'[q] \in {"I1", "I3", "I4"}
            BY RemDef, Zenon
          <5>3. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>2, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>3 
        <4>7. CASE pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>7
          <5> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            BY RemDef, Zenon
          <5>1. pc'[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <5>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5>3. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            <6> DEFINE bkt_arr == MemLocs'[bucket'[q]]
            <6> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg'[q].key
            <6>1. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = bkt_arr[idx].val
              BY Zenon DEF ValOfKeyInBktAtAddr
            <6>2. bkt_arr = MemLocs[bucket[q]]
              BY Zenon
            <6>3. arg'[q].key = arg[q].key
              BY Zenon
            <6> QED
              BY <6>1, <6>2, <6>3, Isa DEF ValOfKeyInBktAtAddr
          <5> QED
            BY <5>2, <5>3
        <4>8. CASE pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>8
          <5> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. pc'[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>9. CASE pc[q] = "I5"
          <5> USE <4>9
          <5> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY RemDef, Zenon
          <5>1. pc'[q] = "I5"
            BY RemDef, Zenon
          <5>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2 
        <4>10. CASE pc[q] \in {"U1", "U2", "U3", "U4"}
          <5> USE <4>10
          <5> SUFFICES c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. pc'[q] \in {"U1", "U2", "U3", "U4"}
            BY RemDef, Zenon
          <5>2. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2 
        <4>11. CASE pc[q] = "U5" 
          <5> USE <4>11
          <5> SUFFICES c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY RemDef, Zenon
          <5>1. pc'[q] = "U5"
            BY RemDef, Zenon
          <5>2. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2 
        <4>12. CASE pc[q] \in {"R1", "R3", "R4"}
          <5> USE <4>12
          <5> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. pc'[q] \in {"R1", "R3", "R4"}
            BY RemDef, Zenon
          <5>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2 
        <4>13. CASE pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>13
          <5> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. pc'[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>14. CASE pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>14
          <5> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
            BY RemDef, Zenon
          <5>1. pc'[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
            BY <5>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>15. CASE pc[q] = "R5"
          <5> USE <4>15
          <5> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY RemDef, Zenon
          <5>1. pc'[q] = "R5"
            BY RemDef, Zenon
          <5>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2 
        <4> QED
          BY RemDef, ZenonT(120),
              <4>1, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, 
              <4>10, <4>11, <4>12, <4>13, <4>14, <4>15
          DEF LineIDs
      <3> QED
        BY <3>3, <3>4, Zenon DEF S
    <2>2. CASE KeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]])
      <3> USE <2>2 DEF TypeOK, Inv
      <3> DEFINE c_pred == [state |-> c.state,
                            op    |-> c.op,
                            arg   |-> c.arg,
                            res   |-> [c.res EXCEPT ![p] = BOT]]
      <3>1. c_pred \in ConfigDomain
        <4>1. c_pred.state \in StateDomain
          BY DEF ConfigDomain
        <4>2. c_pred.op \in [ProcSet -> OpDomain]
          BY DEF ConfigDomain
        <4>3. c_pred.arg \in [ProcSet -> ArgDomain]
          BY DEF ConfigDomain
        <4>4. c_pred.res \in [ProcSet -> ResDomain]
          BY DEF ConfigDomain, ResDomain
        <4> QED
          BY <4>1, <4>2, <4>3, <4>4 DEF ConfigDomain
      <3>2. c_pred \in S
        <4>1. c_pred.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL]
          <5>1. c_pred.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]])'
                                                        THEN ValOfKeyInBktAtAddr(k, A[Hash[k]])'
                                                        ELSE NULL]
            BY SPrimeRewrite, Zenon DEF SPrime
          <5>2. \A k \in KeyDomain : /\ KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
                                      /\ ValOfKeyInBktAtAddr(k, A[Hash[k]]) = ValOfKeyInBktAtAddr(k, A[Hash[k]])'
            <6> SUFFICES ASSUME NEW k \in KeyDomain
                          PROVE  /\ KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
                                /\ ValOfKeyInBktAtAddr(k, A[Hash[k]]) = ValOfKeyInBktAtAddr(k, A[Hash[k]])'
              OBVIOUS
            <6>1. KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
              BY Zenon DEF KeyInBktAtAddr
            <6>2. ValOfKeyInBktAtAddr(k, A[Hash[k]]) = ValOfKeyInBktAtAddr(k, A[Hash[k]])'
              <7> DEFINE bkt_arr == MemLocs'[A'[Hash[k]]]
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
              <7>1. ValOfKeyInBktAtAddr(k, A[Hash[k]])' = bkt_arr[idx].val
                BY Zenon DEF ValOfKeyInBktAtAddr
              <7>2. bkt_arr = MemLocs[A[Hash[k]]]
                BY Zenon
              <7>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
                BY Zenon
              <7> QED
                BY <7>1, <7>2, <7>3, Isa DEF ValOfKeyInBktAtAddr
            <6>3. QED
              BY <6>1, <6>2
          <5> QED
            BY <5>1, <5>2 
        <4>2. ASSUME NEW q \in ProcSet
              PROVE
                CASE pc[q] = RemainderID 
                    -> (c_pred.op[q] = BOT /\ c_pred.arg[q] = BOT /\ c_pred.res[q] = BOT)
                  [] pc[q] = "F1"
                    -> (c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q]))
                  [] pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = NULL)
                  [] pc[q] = "F3"
                    -> (c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q])
                  [] pc[q] \in {"I1", "I3", "I4"}
                    -> (c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q]))
                  [] pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "I5"
                    -> (c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q])
                  [] pc[q] \in {"U1", "U2", "U3", "U4"}
                    -> (c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "U5"
                    -> (c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q])
                  [] pc[q] \in {"R1", "R3", "R4"}
                    -> (c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = NULL)
                  [] pc[q] = "R5"
                    -> (c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q])
          <5> USE <4>2
          <5>1. CASE pc[q] = RemainderID
            <6> USE <5>1
            <6> SUFFICES c_pred.op[q] = BOT /\ c_pred.arg[q] = BOT /\ c_pred.res[q] = BOT
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] = RemainderID
              BY RemDef, Zenon
            <6>4. c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4
          <5>2. CASE pc[q] = "F1"
            <6> USE <5>2
            <6> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] = "F1"
              BY RemDef, Zenon
            <6>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4
          <5>3. CASE pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
            <6> USE <5>3
            <6> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
              BY RemDef, Zenon DEF KeyInBktAtAddr
            <6>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
              <7> DEFINE bkt_arr == MemLocs'[bucket'[q]]
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg'[q].key
              <7>1. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = bkt_arr[idx].val
                BY Zenon DEF ValOfKeyInBktAtAddr
              <7>2. bkt_arr = MemLocs[bucket[q]]
                BY Zenon
              <7>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
                BY Zenon
              <7> QED
                BY <7>1, <7>2, <7>3, Isa DEF ValOfKeyInBktAtAddr
            <6> QED
              BY <6>2, <6>4, <6>5
          <5>4. CASE pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
            <6> USE <5>4
            <6> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = NULL
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
              BY RemDef, Zenon DEF KeyInBktAtAddr
            <6>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4
          <5>5. CASE pc[q] = "F3" 
            <6> USE <5>5
            <6> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] = "F3"
              BY RemDef, Zenon
            <6>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4
          <5>6. CASE pc[q] \in {"I1", "I3", "I4"}
            <6> USE <5>6
            <6> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
              BY RemDef, Zenon
            <6>A. CASE p = q
              <7> USE <6>A
              <7>1. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = BOT
                BY <3>1 DEF ConfigDomain
              <7>2. pc'[q] = "I2"
                BY Zenon
              <7>3. c.op[q] = "Insert" /\ c.arg[p] = arg[q]
                BY <7>2, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>1, <7>3
            <6> SUFFICES ASSUME p # q
                          PROVE  c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
              BY <6>A
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              OBVIOUS
            <6>3. pc'[q] \in {"I1", "I3", "I4"}
              BY RemDef, Zenon
            <6>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4
          <5>7. CASE pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
            <6> USE <5>7
            <6> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
              BY RemDef, Zenon DEF KeyInBktAtAddr
            <6>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
              <7> DEFINE bkt_arr == MemLocs'[bucket'[q]]
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg'[q].key
              <7>1. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = bkt_arr[idx].val
                BY Zenon DEF ValOfKeyInBktAtAddr
              <7>2. bkt_arr = MemLocs[bucket[q]]
                BY Zenon
              <7>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
                BY Zenon
              <7> QED
                BY <7>1, <7>2, <7>3, Isa DEF ValOfKeyInBktAtAddr
            <6> QED
              BY <6>2, <6>4, <6>5
          <5>8. CASE pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
            <6> USE <5>8
            <6> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
              BY RemDef, Zenon DEF KeyInBktAtAddr
            <6>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4
          <5>9. CASE pc[q] = "I5"
            <6> USE <5>9
            <6> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] = "I5"
              BY RemDef, Zenon
            <6>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4
          <5>10. CASE pc[q] \in {"U1", "U2", "U3", "U4"}
            <6> USE <5>10
            <6> SUFFICES c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] \in {"U1", "U2", "U3", "U4"}
              BY RemDef, Zenon
            <6>4. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4
          <5>11. CASE pc[q] = "U5" 
            <6> USE <5>11
            <6> SUFFICES c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] = "U5"
              BY RemDef, Zenon
            <6>4. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4
          <5>12. CASE pc[q] \in {"R1", "R3", "R4"}
            <6> USE <5>12
            <6> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] \in {"R1", "R3", "R4"}
              BY RemDef, Zenon
            <6>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4
          <5>13. CASE pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q]) 
            <6> USE <5>13
            <6> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
              BY RemDef, Zenon DEF KeyInBktAtAddr
            <6>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4              
          <5>14. CASE pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
            <6> USE <5>14
            <6> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = NULL
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
              BY RemDef, Zenon DEF KeyInBktAtAddr
            <6>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4    
          <5>15. CASE pc[q] = "R5"
            <6> USE <5>15
            <6> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] = "R5"
              BY RemDef, Zenon
            <6>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4
          <5> QED
              BY RemDef, ZenonT(120),
                  <5>1, <5>2, <5>3, <5>4, <5>5, <5>6, <5>7, <5>8, <5>9, 
                  <5>10, <5>11, <5>12, <5>13, <5>14, <5>15
              DEF LineIDs
        <4> QED
          BY <3>1, <4>1, <4>2, Zenon DEF S
      <3>3. Delta(c_pred, p, c)
        <4>1. c_pred.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL]
          BY <3>1, <3>2, Zenon DEF S
        <4>2. c_pred.op[p] = "Insert" /\ c_pred.arg[p] = arg[p] /\ c_pred.res[p] = BOT
          BY <3>1, <3>2, Zenon, RemDef DEF S
        <4>3. arg[p] \in ArgsOf("Insert") /\ arg[p].key \in KeyDomain
          BY RemDef, Zenon DEF ArgsOf, LineIDtoOp 
        <4>4. c_pred.state[c_pred.arg[p].key] = ValOfKeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]])
          BY <4>1, <4>2, <4>3, Zenon
        <4>5. ValOfKeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]]) \in ValDomain
          <5> DEFINE bkt_arr == MemLocs[A[Hash[arg[p].key]]]
          <5>1. A[Hash[arg[p].key]] # NULL
            BY DEF KeyInBktAtAddr
          <5>2. bkt_arr \in Seq([key: KeyDomain, val: ValDomain])
            BY HashDef, <4>3, <5>1, Zenon
          <5> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[p].key
          <5>3. idx \in 1..Len(bkt_arr)
            BY Zenon DEF KeyInBktAtAddr
          <5>4. bkt_arr[idx] \in [key: KeyDomain, val: ValDomain]
            BY Zenon, ElementOfSeq, <5>2, <5>3
          <5>5. bkt_arr[idx].val \in ValDomain
            BY Zenon, <5>4
          <5>6. ValOfKeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]]) = bkt_arr[idx].val
            BY DEF ValOfKeyInBktAtAddr
          <5> QED
            BY Zenon, <5>5, <5>6
        <4>6. ValOfKeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]]) # NULL
          BY <4>5, NULLDef
        <4> SUFFICES c.res = [c_pred.res EXCEPT ![p] = c_pred.state[c_pred.arg[p].key]]
          BY <4>2, <4>3, <4>4, <4>6, Zenon DEF Delta
        <4> SUFFICES c.res[p] = c_pred.state[c_pred.arg[p].key]
          BY <3>2, Zenon DEF ConfigDomain, S
        <4>7. pc'[p] = "I2" /\ KeyInBktAtAddr(arg[p].key, bucket[p])'
          BY Zenon DEF KeyInBktAtAddr
        <4>8. c.res[p] = ValOfKeyInBktAtAddr(arg[p].key, bucket[p])'
          BY <4>7, SPrimeRewrite, RemDef, Zenon DEF SPrime
        <4>9. ValOfKeyInBktAtAddr(arg[p].key, bucket[p])' = ValOfKeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]])
          <5> DEFINE bkt_arr == MemLocs'[bucket'[p]]
          <5> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg'[p].key
          <5>1. ValOfKeyInBktAtAddr(arg[p].key, bucket[p])' = bkt_arr[idx].val
            BY Zenon DEF ValOfKeyInBktAtAddr
          <5> DEFINE bkt_arr2 == MemLocs[A[Hash[arg[p].key]]]
          <5> DEFINE idx2 == CHOOSE index \in 1..Len(bkt_arr2) : bkt_arr2[index].key = arg[p].key
          <5>2. ValOfKeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]]) = bkt_arr2[idx2].val
            BY Zenon DEF ValOfKeyInBktAtAddr
          <5>3. bkt_arr = bkt_arr2 /\ idx = idx2
            BY ZenonT(30)
          <5> QED
            BY <5>1, <5>2, <5>3, Zenon
        <4> QED
          BY <4>8, <4>9, <4>4, Zenon
      <3> QED
        BY <3>1, <3>2, <3>3, SingleDeltaEvolve
    <2> QED
      BY <2>1, <2>2
  <1>4. CASE LineAction = I2(p)
    <2> USE <1>4 DEF I2
    <2> SUFFICES ASSUME NEW c \in ConfigDomain,
                        c \in S'
                 PROVE  c \in Evolve(S)
      BY Zenon DEF S
    <2> SUFFICES c \in S
      BY EmptySeqEvolve
    <2>1. c.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL]
      <3>1. c.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]])' THEN ValOfKeyInBktAtAddr(k, A[Hash[k]])' ELSE NULL]
        BY Zenon, SPrimeRewrite DEF SPrime
      <3>2. \A k \in KeyDomain : KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
        BY Zenon DEF KeyInBktAtAddr
      <3>3. \A k \in KeyDomain : ValOfKeyInBktAtAddr(k, A[Hash[k]])' = ValOfKeyInBktAtAddr(k, A[Hash[k]])
        <4> SUFFICES ASSUME NEW k \in KeyDomain
                      PROVE  ValOfKeyInBktAtAddr(k, A[Hash[k]])' = ValOfKeyInBktAtAddr(k, A[Hash[k]])
          OBVIOUS
        <4> bkt_arr == MemLocs'[A'[Hash[k]]]
        <4> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
        <4>1. ValOfKeyInBktAtAddr(k, A[Hash[k]])' = bkt_arr[idx].val
          BY DEF ValOfKeyInBktAtAddr
        <4>2. bkt_arr = MemLocs[A[Hash[k]]]
          BY Zenon
        <4> QED
          BY <4>1, <4>2, ZenonT(30) DEF ValOfKeyInBktAtAddr
      <3> QED
        BY <3>1, <3>2, <3>3
    <2>2. ASSUME NEW q \in ProcSet
          PROVE
              CASE pc[q] = RemainderID 
                  -> (c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT)
                [] pc[q] = "F1"
                  -> (c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                [] pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                  -> (c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q]))
                [] pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                  -> (c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL)
                [] pc[q] = "F3"
                  -> (c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q])
                [] pc[q] \in {"I1", "I3", "I4"}
                  -> (c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                [] pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                  -> (c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q]))
                [] pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                  -> (c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                [] pc[q] = "I5"
                  -> (c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q])
                [] pc[q] \in {"U1", "U2", "U3", "U4"}
                  -> (c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                [] pc[q] = "U5"
                  -> (c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q])
                [] pc[q] \in {"R1", "R3", "R4"}
                  -> (c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                [] pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                  -> (c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                [] pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                  -> (c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL)
                [] pc[q] = "R5"
                  -> (c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q])
      <3> USE <2>2 DEF TypeOK, Inv
      <3>1. \A k \in KeyDomain : KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, bucket[q])'
        BY Zenon DEF KeyInBktAtAddr
      <3>2. \A k \in KeyDomain : ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, bucket[q])
        <4> SUFFICES ASSUME NEW k \in KeyDomain
                      PROVE  ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, bucket[q])
          OBVIOUS
        <4> bkt_arr == MemLocs'[bucket'[q]]
        <4> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
        <4>1. ValOfKeyInBktAtAddr(k, bucket[q])' = bkt_arr[idx].val
          BY DEF ValOfKeyInBktAtAddr
        <4>2. bkt_arr = MemLocs[bucket[q]]
          BY Zenon
        <4> QED
          BY <4>1, <4>2, ZenonT(30) DEF ValOfKeyInBktAtAddr
      <3>3. CASE pc[q] = RemainderID
        <4> USE <3>3
        <4> SUFFICES c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
          BY RemDef, Zenon
        <4>1. pc'[q] = RemainderID
          BY RemDef, Zenon
        <4>2. c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
          BY <4>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2
      <3>4. CASE pc[q] = "F1"
        <4> USE <3>4
        <4> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY RemDef, Zenon
        <4>1. pc'[q] = "F1"
          BY RemDef, Zenon
        <4>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY <4>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2
      <3>5. CASE pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
        <4> USE <3>5
        <4> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
          BY RemDef, Zenon
        <4>1. pc'[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
          BY RemDef, Zenon DEF KeyInBktAtAddr
        <4>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
          BY <4>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4>3. arg[q].key = arg'[q].key /\ arg[q].key \in KeyDomain
          BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
        <4>4. c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
          BY <4>2, <4>3, <3>2
        <4> QED
          BY <4>2, <4>4
      <3>6. CASE pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
        <4> USE <3>6
        <4> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
          BY RemDef, Zenon
        <4>1. CASE q = p
          <5> USE <4>1
          <5>1. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r'[q]
            BY SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
            BY <5>1, Zenon
          <5> QED
            BY <5>2
        <4> SUFFICES ASSUME q # p
                      PROVE  c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
          BY <4>1
        <4>2. pc'[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
          BY RemDef, Zenon DEF KeyInBktAtAddr
        <4>3. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
          BY <4>2,  SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>3
      <3>7. CASE pc[q] = "F3"
        <4> USE <3>7
        <4> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
          BY RemDef, Zenon
        <4>1. pc'[q] = "F3"
          BY RemDef, Zenon
        <4>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
          BY <4>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2 
      <3>8. CASE pc[q] \in {"I1", "I3", "I4"}
        <4> USE <3>8
        <4> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY RemDef, Zenon
        <4>1. pc'[q] \in {"I1", "I3", "I4"}
          BY RemDef, Zenon
        <4>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY <4>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2 
      <3>9. CASE pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
        <4> USE <3>9
        <4> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
          BY RemDef, Zenon
        <4>1. CASE p = q
          <5> USE <4>1
          <5>1. c.op[p] = "Insert" /\ c.arg[p] = arg[p] /\ c.res[p] = r'[p]
            BY SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5>2. r'[p] = ValOfKeyInBktAtAddr(arg[p].key, bucket[p])
            BY Zenon
          <5> QED
            BY <5>1, <5>2
        <4> SUFFICES ASSUME p # q
                      PROVE  c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
          BY <4>1
        <4>2. pc'[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
          BY RemDef, Zenon DEF KeyInBktAtAddr
        <4>3. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
          BY <4>2,  SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4>4. arg[q].key = arg'[q].key /\ arg[q].key \in KeyDomain
          BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
        <4>5. c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
          BY <4>3, <4>4, <3>2
        <4> QED
          BY <4>3, <4>5
      <3>10. CASE pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
        <4> USE <3>10
        <4> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY RemDef, Zenon
        <4>1. CASE p = q
          <5> USE <4>1
          <5>1. c.op[p] = "Insert" /\ c.arg[p] = arg[p] /\ c.res[p] = BOT
            BY SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>1
        <4> SUFFICES ASSUME p # q
                      PROVE  c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY <4>1
        <4>2. pc'[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
          BY RemDef, Zenon DEF KeyInBktAtAddr
        <4>3. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY <4>2, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>3 
      <3>11. CASE pc[q] = "I5"
        <4> USE <3>11
        <4> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
          BY RemDef, Zenon
        <4>1. pc'[q] = "I5"
          BY RemDef, Zenon 
        <4>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
          BY <4>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2 
      <3>12. CASE pc[q] \in {"U1", "U2", "U3", "U4"}
        <4> USE <3>12
        <4> SUFFICES c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY RemDef, Zenon
        <4>1. pc'[q] \in {"U1", "U2", "U3", "U4"}
          BY RemDef, Zenon
        <4>2. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY <4>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2
      <3>13. CASE pc[q] = "U5" 
        <4> USE <3>13
        <4> SUFFICES c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
          BY RemDef, Zenon
        <4>1. pc'[q] = "U5"
          BY RemDef, Zenon
        <4>2. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
          BY <4>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2
      <3>14. CASE pc[q] \in {"R1", "R3", "R4"}
        <4> USE <3>14
        <4> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY RemDef, Zenon
        <4>1. pc'[q] \in {"R1", "R3", "R4"}
          BY RemDef, Zenon
        <4>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY <4>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2
      <3>15. CASE pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
        <4> USE <3>15
        <4> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY RemDef, Zenon
        <4>1. pc'[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
          BY RemDef, Zenon DEF KeyInBktAtAddr
        <4>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY <4>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2
      <3>16. CASE pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
        <4> USE <3>16
        <4> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
          BY RemDef, Zenon
        <4>1. pc'[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
          BY RemDef, Zenon DEF KeyInBktAtAddr
        <4>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
          BY <4>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2
      <3>17. CASE pc[q] = "R5"
        <4> USE <3>17
        <4> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
          BY RemDef, Zenon
        <4>1. pc'[q] = "R5" 
          BY RemDef, Zenon
        <4>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
          BY <4>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2
      <3> QED
          BY RemDef, ZenonT(120),
              <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9, <3>10, <3>11, 
              <3>12, <3>13, <3>14, <3>15, <3>16, <3>17
          DEF LineIDs
    <2> QED
      BY <2>1, <2>2, Zenon DEF S
  <1>5. CASE LineAction = I3(p)
    <2> USE <1>5 DEF I3, TypeOK, Inv
    <2> SUFFICES ASSUME NEW c \in ConfigDomain,
                        c \in S'
                 PROVE  c \in Evolve(S)
      BY Zenon DEF S
    <2> SUFFICES c \in S
      BY EmptySeqEvolve
    <2>1. CASE bucket[p] = NULL
      <3> PICK addr \in Addrs : 
                    /\ addr \notin AllocAddrs
                    /\ AllocAddrs' = AllocAddrs \cup {addr}
                    /\ newbkt' = [newbkt EXCEPT ![p] = addr]
                    /\ MemLocs' = [MemLocs EXCEPT ![addr] = <<arg[p]>>]
        BY <2>1, Zenon
      <3>1. c.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL]
        <4>1. c.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]])' THEN ValOfKeyInBktAtAddr(k, A[Hash[k]])' ELSE NULL]
          BY Zenon, SPrimeRewrite DEF SPrime
        <4>2. \A k \in KeyDomain : KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
          <5> SUFFICES ASSUME NEW k \in KeyDomain
                        PROVE  KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
            OBVIOUS
          <5>1. A'[Hash[k]] = A[Hash[k]]
            BY Zenon
          <5>2. CASE A[Hash[k]] = NULL
            BY <5>1, <5>2 DEF KeyInBktAtAddr
          <5> SUFFICES ASSUME A[Hash[k]] # NULL
                        PROVE  KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
            BY <5>2
          <5>3. A[Hash[k]] \in AllocAddrs
            BY HashDef, Zenon
          <5>4. A[Hash[k]] # addr
            BY NULLDef, <5>3
          <5>5. \A a \in Addrs : a # addr => MemLocs'[a] = MemLocs[a]
            BY Zenon
          <5>6. MemLocs'[A'[Hash[k]]] = MemLocs[A[Hash[k]]]
            BY <5>1, <5>4, <5>5
          <5> QED
            BY <5>6, Zenon DEF KeyInBktAtAddr
        <4>3. \A k \in KeyDomain : KeyInBktAtAddr(k, A[Hash[k]]) => (ValOfKeyInBktAtAddr(k, A[Hash[k]]) = ValOfKeyInBktAtAddr(k, A[Hash[k]])')
          <5> SUFFICES ASSUME NEW k \in KeyDomain,
                              NEW bkt_arr,
                              A[Hash[k]] # NULL,
                              bkt_arr = MemLocs[A[Hash[k]]],
                              \E index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
                        PROVE  ValOfKeyInBktAtAddr(k, A[Hash[k]]) = ValOfKeyInBktAtAddr(k, A[Hash[k]])'
            BY Zenon DEF KeyInBktAtAddr
          <5>1. A'[Hash[k]] = A[Hash[k]]
            BY Zenon
          <5>2. A[Hash[k]] \in AllocAddrs
            BY HashDef, Zenon
          <5>3. A[Hash[k]] # addr
            BY NULLDef, <5>2
          <5>4. \A a \in Addrs : a # addr => MemLocs'[a] = MemLocs[a]
            BY Zenon
          <5>5. MemLocs'[A'[Hash[k]]] = MemLocs[A[Hash[k]]]
            BY <5>1, <5>3, <5>4
          <5> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
          <5>6. ValOfKeyInBktAtAddr(k, A[Hash[k]]) = bkt_arr[idx].val
            BY Zenon DEF ValOfKeyInBktAtAddr
          <5>7. ValOfKeyInBktAtAddr(k, A[Hash[k]])' = bkt_arr[idx].val
            BY Isa, <5>5 DEF ValOfKeyInBktAtAddr
          <5> QED
            BY <5>6, <5>7, Zenon
        <4> QED
          BY <4>1, <4>2, <4>3, Zenon
      <3>2. ASSUME NEW q \in ProcSet
              PROVE
                  CASE pc[q] = RemainderID 
                      -> (c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT)
                    [] pc[q] = "F1"
                      -> (c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                    [] pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                      -> (c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q]))
                    [] pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                      -> (c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL)
                    [] pc[q] = "F3"
                      -> (c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q])
                    [] pc[q] \in {"I1", "I3", "I4"}
                      -> (c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                    [] pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                      -> (c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q]))
                    [] pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                      -> (c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                    [] pc[q] = "I5"
                      -> (c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q])
                    [] pc[q] \in {"U1", "U2", "U3", "U4"}
                      -> (c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                    [] pc[q] = "U5"
                      -> (c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q])
                    [] pc[q] \in {"R1", "R3", "R4"}
                      -> (c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                    [] pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                      -> (c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                    [] pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                      -> (c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL)
                    [] pc[q] = "R5"
                      -> (c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q])
        <4> USE <3>2
        <4>1. KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
          <5>1. bucket[q] = bucket'[q]
            BY Zenon
          <5>2. CASE bucket[q] = NULL
            BY <5>1, <5>2, Zenon DEF KeyInBktAtAddr
          <5> SUFFICES ASSUME bucket[q] # NULL
                        PROVE  KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <5>2
          <5>3. bucket[q] \in AllocAddrs
            BY NULLDef, Zenon
          <5>4. bucket[q] # addr
            BY <5>3
          <5>5. \A a \in Addrs : a # addr => MemLocs'[a] = MemLocs[a]
            BY Zenon
          <5>6. MemLocs'[bucket'[q]] = MemLocs[bucket[q]]
            BY <5>1, <5>4, <5>5
          <5> QED
            BY <5>6, Zenon DEF KeyInBktAtAddr
        <4>2. KeyInBktAtAddr(arg[q].key, bucket[q]) => (ValOfKeyInBktAtAddr(arg[q].key, bucket[q]) = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])')
          <5> SUFFICES ASSUME NEW bkt_arr,
                              bkt_arr = MemLocs[bucket[q]],
                              bucket[q] # NULL,
                              \E index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
                        PROVE  ValOfKeyInBktAtAddr(arg[q].key, bucket[q]) = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
            BY Zenon DEF KeyInBktAtAddr
          <5>1. bucket[q] = bucket'[q]
            BY Zenon
          <5>2. bucket[q] \in AllocAddrs
            BY NULLDef, Zenon
          <5>3. bucket[q] # addr
            BY <5>2
          <5>4. \A a \in Addrs : a # addr => MemLocs'[a] = MemLocs[a]
            BY Zenon
          <5>5. MemLocs'[bucket'[q]] = MemLocs[bucket[q]]
            BY <5>1, <5>3, <5>4 
          <5> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
          <5>6. ValOfKeyInBktAtAddr(arg[q].key, bucket[q]) = bkt_arr[idx].val
            BY Zenon DEF ValOfKeyInBktAtAddr
          <5>7. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = bkt_arr[idx].val
            BY Isa, <5>5 DEF ValOfKeyInBktAtAddr
          <5> QED
            BY <5>6, <5>7, Zenon
        <4>3. CASE pc[q] = RemainderID
          <5> USE <4>3
          <5> SUFFICES c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. pc'[q] = RemainderID
            BY RemDef, Zenon
          <5>2. c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>4. CASE pc[q] = "F1"
          <5> USE <4>4
          <5> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. pc'[q] = "F1"
            BY RemDef, Zenon
          <5>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2  
        <4>5. CASE pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>5
          <5> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            BY RemDef, Zenon
          <5>1. pc'[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <4>1, RemDef, Zenon DEF KeyInBktAtAddr
          <5>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <5>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5>3. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            BY <4>2, Zenon
          <5> QED
            BY <5>2, <5>3
        <4>6. CASE pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>6
          <5> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
            BY RemDef, Zenon
          <5>1. pc'[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <4>1, RemDef, Zenon DEF KeyInBktAtAddr
          <5>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
            BY <5>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>7. CASE pc[q] = "F3" 
          <5> USE <4>7
          <5> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY RemDef, Zenon
          <5>1. pc'[q] = "F3"
            BY RemDef, Zenon
          <5>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>8. CASE pc[q] \in {"I1", "I3", "I4"}
          <5> USE <4>8
          <5> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. CASE p = q
            <6> USE <5>1
            <6>1. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
              BY SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>1
          <5> SUFFICES ASSUME p # q
                        PROVE  c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>1
          <5>2. pc'[q] \in {"I1", "I3", "I4"}
            BY RemDef, Zenon
          <5>3. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>2,  SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>3
        <4>9. CASE pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>9
          <5> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            BY RemDef, Zenon
          <5>1. pc'[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <4>1, RemDef, Zenon DEF KeyInBktAtAddr
          <5>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <5>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5>3. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            BY <4>2, Zenon
          <5> QED
            BY <5>2, <5>3
        <4>10. CASE pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>10
          <5> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. pc'[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <4>1, RemDef, Zenon DEF KeyInBktAtAddr
          <5>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>11. CASE pc[q] = "I5"
          <5> USE <4>11
          <5> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY RemDef, Zenon
          <5>1. pc'[q] = "I5"
            BY RemDef, Zenon
          <5>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>12. CASE pc[q] \in {"U1", "U2", "U3", "U4"}
          <5> USE <4>12
          <5> SUFFICES c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. pc'[q] \in {"U1", "U2", "U3", "U4"}
            BY RemDef, Zenon
          <5>2. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>13. CASE pc[q] = "U5" 
          <5> USE <4>13
          <5> SUFFICES c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY RemDef, Zenon
          <5>1. pc'[q] = "U5"
            BY RemDef, Zenon
          <5>2. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>14. CASE pc[q] \in {"R1", "R3", "R4"}
          <5> USE <4>14
          <5> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. pc'[q] \in {"R1", "R3", "R4"}
            BY RemDef, Zenon
          <5>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>15. CASE pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>15
          <5> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. pc'[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <4>1, RemDef, Zenon DEF KeyInBktAtAddr
          <5>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>16. CASE pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>16
          <5> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
            BY RemDef, Zenon
          <5>1. pc'[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <4>1, RemDef, Zenon DEF KeyInBktAtAddr
          <5>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
            BY <5>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>17. CASE pc[q] = "R5"
          <5> USE <4>17
          <5> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY RemDef, Zenon
          <5>1. pc'[q] = "R5"
            BY RemDef, Zenon
          <5>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4> QED
            BY RemDef, ZenonT(120),
                <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, <4>10, <4>11, 
                <4>12, <4>13, <4>14, <4>15, <4>16, <4>17
            DEF LineIDs
      <3> QED
        BY <3>1, <3>2, Zenon DEF S
    <2>2. CASE bucket[p] # NULL
      <3> PICK addr \in Addrs : 
                    /\ addr \notin AllocAddrs
                    /\ AllocAddrs' = AllocAddrs \cup {addr}
                    /\ newbkt' = [newbkt EXCEPT ![p] = addr]
                    /\ MemLocs' = [MemLocs EXCEPT ![addr] = Append(MemLocs[bucket[p]], arg[p])]
        BY <2>2, Zenon
      <3>1. c.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL]
        <4>1. c.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]])' THEN ValOfKeyInBktAtAddr(k, A[Hash[k]])' ELSE NULL]
          BY Zenon, SPrimeRewrite DEF SPrime
        <4>2. \A k \in KeyDomain : KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
          <5> SUFFICES ASSUME NEW k \in KeyDomain
                        PROVE  KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
            OBVIOUS
          <5>1. A'[Hash[k]] = A[Hash[k]]
            BY Zenon
          <5>2. CASE A[Hash[k]] = NULL
            BY <5>1, <5>2 DEF KeyInBktAtAddr
          <5> SUFFICES ASSUME A[Hash[k]] # NULL
                        PROVE  KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
            BY <5>2
          <5>3. A[Hash[k]] \in AllocAddrs
            BY HashDef, Zenon
          <5>4. A[Hash[k]] # addr
            BY NULLDef, <5>3
          <5>5. \A a \in Addrs : a # addr => MemLocs'[a] = MemLocs[a]
            BY Zenon
          <5>6. MemLocs'[A'[Hash[k]]] = MemLocs[A[Hash[k]]]
            BY <5>1, <5>4, <5>5
          <5> QED
            BY <5>6, Zenon DEF KeyInBktAtAddr
        <4>3. \A k \in KeyDomain : KeyInBktAtAddr(k, A[Hash[k]]) => (ValOfKeyInBktAtAddr(k, A[Hash[k]]) = ValOfKeyInBktAtAddr(k, A[Hash[k]])')
          <5> SUFFICES ASSUME NEW k \in KeyDomain,
                              NEW bkt_arr,
                              A[Hash[k]] # NULL,
                              bkt_arr = MemLocs[A[Hash[k]]],
                              \E index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
                        PROVE  ValOfKeyInBktAtAddr(k, A[Hash[k]]) = ValOfKeyInBktAtAddr(k, A[Hash[k]])'
            BY Zenon DEF KeyInBktAtAddr
          <5>1. A'[Hash[k]] = A[Hash[k]]
            BY Zenon
          <5>2. A[Hash[k]] \in AllocAddrs
            BY HashDef, Zenon
          <5>3. A[Hash[k]] # addr
            BY NULLDef, <5>2
          <5>4. \A a \in Addrs : a # addr => MemLocs'[a] = MemLocs[a]
            BY Zenon
          <5>5. MemLocs'[A'[Hash[k]]] = MemLocs[A[Hash[k]]]
            BY <5>1, <5>3, <5>4
          <5> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
          <5>6. ValOfKeyInBktAtAddr(k, A[Hash[k]]) = bkt_arr[idx].val
            BY Zenon DEF ValOfKeyInBktAtAddr
          <5>7. ValOfKeyInBktAtAddr(k, A[Hash[k]])' = bkt_arr[idx].val
            BY Isa, <5>5 DEF ValOfKeyInBktAtAddr
          <5> QED
            BY <5>6, <5>7, Zenon
        <4> QED
          BY <4>1, <4>2, <4>3, Zenon
      <3>2. ASSUME NEW q \in ProcSet
              PROVE
                  CASE pc[q] = RemainderID 
                      -> (c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT)
                    [] pc[q] = "F1"
                      -> (c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                    [] pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                      -> (c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q]))
                    [] pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                      -> (c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL)
                    [] pc[q] = "F3"
                      -> (c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q])
                    [] pc[q] \in {"I1", "I3", "I4"}
                      -> (c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                    [] pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                      -> (c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q]))
                    [] pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                      -> (c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                    [] pc[q] = "I5"
                      -> (c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q])
                    [] pc[q] \in {"U1", "U2", "U3", "U4"}
                      -> (c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                    [] pc[q] = "U5"
                      -> (c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q])
                    [] pc[q] \in {"R1", "R3", "R4"}
                      -> (c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                    [] pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                      -> (c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                    [] pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                      -> (c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL)
                    [] pc[q] = "R5"
                      -> (c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q])
        <4> USE <3>2
        <4>A. KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
          <5>1. bucket[q] = bucket'[q]
            BY Zenon
          <5>2. CASE bucket[q] = NULL
            BY <5>1, <5>2, Zenon DEF KeyInBktAtAddr
          <5> SUFFICES ASSUME bucket[q] # NULL
                        PROVE  KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <5>2
          <5>3. bucket[q] \in AllocAddrs
            BY NULLDef, Zenon
          <5>4. bucket[q] # addr
            BY <5>3
          <5>5. \A a \in Addrs : a # addr => MemLocs'[a] = MemLocs[a]
            BY Zenon
          <5>6. MemLocs'[bucket'[q]] = MemLocs[bucket[q]]
            BY <5>1, <5>4, <5>5
          <5> QED
            BY <5>6, Zenon DEF KeyInBktAtAddr
        <4>B. KeyInBktAtAddr(arg[q].key, bucket[q]) => (ValOfKeyInBktAtAddr(arg[q].key, bucket[q]) = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])')
          <5> SUFFICES ASSUME NEW bkt_arr,
                              bkt_arr = MemLocs[bucket[q]],
                              bucket[q] # NULL,
                              \E index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
                        PROVE  ValOfKeyInBktAtAddr(arg[q].key, bucket[q]) = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
            BY Zenon DEF KeyInBktAtAddr
          <5>1. bucket[q] = bucket'[q]
            BY Zenon
          <5>2. bucket[q] \in AllocAddrs
            BY NULLDef, Zenon
          <5>3. bucket[q] # addr
            BY <5>2
          <5>4. \A a \in Addrs : a # addr => MemLocs'[a] = MemLocs[a]
            BY Zenon
          <5>5. MemLocs'[bucket'[q]] = MemLocs[bucket[q]]
            BY <5>1, <5>3, <5>4 
          <5> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
          <5>6. ValOfKeyInBktAtAddr(arg[q].key, bucket[q]) = bkt_arr[idx].val
            BY Zenon DEF ValOfKeyInBktAtAddr
          <5>7. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = bkt_arr[idx].val
            BY Isa, <5>5 DEF ValOfKeyInBktAtAddr
          <5> QED
            BY <5>6, <5>7, Zenon
        <4>1. CASE pc[q] = RemainderID
          <5> USE <4>1
          <5> SUFFICES c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. pc'[q] = RemainderID
            BY RemDef, Zenon
          <5>2. c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>2. CASE pc[q] = "F1"
          <5> USE <4>2
          <5> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. pc'[q] = "F1"
            BY RemDef, Zenon
          <5>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2  
        <4>3. CASE pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>3
          <5> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            BY RemDef, Zenon
          <5>1. pc'[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <4>A, RemDef, Zenon DEF KeyInBktAtAddr
          <5>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <5>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5>3. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            BY <4>B, Zenon
          <5> QED
            BY <5>2, <5>3
        <4>4. CASE pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>4
          <5> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
            BY RemDef, Zenon
          <5>1. pc'[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <4>A, RemDef, Zenon DEF KeyInBktAtAddr
          <5>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
            BY <5>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>5. CASE pc[q] = "F3" 
          <5> USE <4>5
          <5> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY RemDef, Zenon
          <5>1. pc'[q] = "F3"
            BY RemDef, Zenon
          <5>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>6. CASE pc[q] \in {"I1", "I3", "I4"}
          <5> USE <4>6
          <5> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. CASE p = q
            <6> USE <5>1
            <6>1. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
              BY SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>1
          <5> SUFFICES ASSUME p # q
                        PROVE  c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>1
          <5>2. pc'[q] \in {"I1", "I3", "I4"}
            BY RemDef, Zenon
          <5>3. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>2,  SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>3
        <4>7. CASE pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>7
          <5> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            BY RemDef, Zenon
          <5>1. pc'[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <4>A, RemDef, Zenon DEF KeyInBktAtAddr
          <5>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <5>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5>3. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            BY <4>B, Zenon
          <5> QED
            BY <5>2, <5>3
        <4>8. CASE pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>8
          <5> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. pc'[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <4>A, RemDef, Zenon DEF KeyInBktAtAddr
          <5>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>9. CASE pc[q] = "I5"
          <5> USE <4>9
          <5> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY RemDef, Zenon
          <5>1. pc'[q] = "I5"
            BY RemDef, Zenon
          <5>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>10. CASE pc[q] \in {"U1", "U2", "U3", "U4"}
          <5> USE <4>10
          <5> SUFFICES c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. pc'[q] \in {"U1", "U2", "U3", "U4"}
            BY RemDef, Zenon
          <5>2. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>11. CASE pc[q] = "U5" 
          <5> USE <4>11
          <5> SUFFICES c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY RemDef, Zenon
          <5>1. pc'[q] = "U5"
            BY RemDef, Zenon
          <5>2. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>12. CASE pc[q] \in {"R1", "R3", "R4"}
          <5> USE <4>12
          <5> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. pc'[q] \in {"R1", "R3", "R4"}
            BY RemDef, Zenon
          <5>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>13. CASE pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>13
          <5> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. pc'[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <4>A, RemDef, Zenon DEF KeyInBktAtAddr
          <5>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>14. CASE pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>14
          <5> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
            BY RemDef, Zenon
          <5>1. pc'[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <4>A, RemDef, Zenon DEF KeyInBktAtAddr
          <5>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
            BY <5>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>15. CASE pc[q] = "R5"
          <5> USE <4>15
          <5> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY RemDef, Zenon
          <5>1. pc'[q] = "R5"
            BY RemDef, Zenon
          <5>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4> QED
            BY RemDef, ZenonT(120),
                <4>1, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, 
                <4>10, <4>11, <4>12, <4>13, <4>14, <4>15
            DEF LineIDs
      <3> QED
        BY <3>1, <3>2, Zenon DEF S
    <2> QED
      BY <2>1, <2>2
  <1>6. CASE LineAction = I4(p)
    <2> USE <1>6 DEF I4, TypeOK, Inv
    <2> SUFFICES ASSUME NEW c \in ConfigDomain,
                        c \in S'
                 PROVE  c \in Evolve(S)
      BY Zenon DEF S
    <2>1. CASE A[Hash[arg[p].key]] = bucket[p]
      <3> USE <2>1
      <3> DEFINE c_pred == [state |-> [c.state EXCEPT ![arg[p].key] = NULL],
                            op    |-> c.op,
                            arg   |-> c.arg,
                            res   |-> [c.res EXCEPT ![p] = BOT]]
      <3>1. c_pred \in ConfigDomain
        <4>1. c_pred.state \in StateDomain
          BY Zenon DEF ConfigDomain, StateDomain
        <4>2. c_pred.op \in [ProcSet -> OpDomain]
          BY DEF ConfigDomain
        <4>3. c_pred.arg \in [ProcSet -> ArgDomain]
          BY DEF ConfigDomain
        <4>4. c_pred.res \in [ProcSet -> ResDomain]
          BY DEF ConfigDomain, ResDomain
        <4> QED
          BY <4>1, <4>2, <4>3, <4>4 DEF ConfigDomain
      <3>2. c_pred \in S
        <4>1. c_pred.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL]
          <5> SUFFICES ASSUME NEW k \in KeyDomain
                        PROVE  c_pred.state[k] = IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL
            BY Zenon, <3>1 DEF StateDomain, ConfigDomain
          <5>1. CASE k = arg[p].key
            <6> USE <5>1
            <6>1. ~KeyInBktAtAddr(k, A[Hash[k]])
              BY Zenon DEF BktInv
            <6>2. c_pred.state[k] = NULL
              BY Zenon DEF ConfigDomain, StateDomain
            <6> QED
              BY <6>1, <6>2
          <5>2. CASE k # arg[p].key /\ Hash[k] # Hash[arg[p].key]
            <6> USE <5>2
            <6>1. c.state = [key \in KeyDomain |-> IF KeyInBktAtAddr(key, A[Hash[key]])' THEN ValOfKeyInBktAtAddr(key, A[Hash[key]])' ELSE NULL]
              BY SPrimeRewrite, Zenon DEF SPrime
            <6>2. A'[Hash[k]] = A[Hash[k]]
              BY HashDef, Zenon
            <6>3. KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
              BY <6>2, Zenon DEF KeyInBktAtAddr
            <6>4. ValOfKeyInBktAtAddr(k, A[Hash[k]]) = ValOfKeyInBktAtAddr(k, A[Hash[k]])'
              <7> DEFINE bkt_arr == MemLocs'[A'[Hash[k]]]
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
              <7>1. ValOfKeyInBktAtAddr(k, A[Hash[k]])' = bkt_arr[idx].val
                BY Zenon DEF ValOfKeyInBktAtAddr
              <7>2. bkt_arr = MemLocs[A[Hash[k]]]
                BY Zenon, <6>2
              <7>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
                BY Zenon
              <7>4. ValOfKeyInBktAtAddr(k, A[Hash[k]]) = MemLocs[A[Hash[k]]][CHOOSE index \in 1..Len(MemLocs[A[Hash[k]]]) : MemLocs[A[Hash[k]]][index].key = k].val
                BY Zenon DEF ValOfKeyInBktAtAddr
              <7>5. ValOfKeyInBktAtAddr(k, A[Hash[k]]) = bkt_arr[idx].val
                BY ZenonT(90), <7>2, <7>3, <7>4
              <7> QED
                BY Zenon, <7>1, <7>5
            <6> QED
              BY <6>1, <6>3, <6>4
          <5>3. CASE k # arg[p].key /\ Hash[k] = Hash[arg[p].key]
            <6> USE <5>3
            <6>1. c.state = [key \in KeyDomain |-> IF KeyInBktAtAddr(key, A[Hash[key]])' 
                                                      THEN ValOfKeyInBktAtAddr(key, A[Hash[key]])' 
                                                      ELSE NULL]
              BY SPrimeRewrite, Zenon DEF SPrime
            <6>2. c_pred.state[k] = IF KeyInBktAtAddr(k, A[Hash[k]])' 
                                        THEN ValOfKeyInBktAtAddr(k, A[Hash[k]])' 
                                        ELSE NULL
              BY <6>1
            <6>3. MemLocs' = MemLocs
              BY Zenon
            <6>4. bucket[p] = A[Hash[k]]
              BY Zenon
            <6>5. arg[p].key \in KeyDomain
              BY RemDef, Zenon DEF ArgsOf, LineIDtoOp
            <6>6. newbkt[p] = A'[Hash[k]]
              BY Zenon, <6>5, HashDef
            <6>7. KeyInBktAtAddr(k, A[Hash[k]])' = KeyInBktAtAddr(k, newbkt[p])
              BY <6>6, Zenon DEF KeyInBktAtAddr
            <6>8. ValOfKeyInBktAtAddr(k, A[Hash[k]])' = ValOfKeyInBktAtAddr(k, newbkt[p])
              BY <6>6, Zenon DEF ValOfKeyInBktAtAddr
            <6>9. c_pred.state[k] = IF KeyInBktAtAddr(k, newbkt[p]) THEN ValOfKeyInBktAtAddr(k, newbkt[p]) ELSE NULL
              BY <6>2, <6>7, <6>8, Zenon
            <6>10. /\ KeyInBktAtAddr(k, bucket[p]) = KeyInBktAtAddr(k, newbkt[p])
                   /\ KeyInBktAtAddr(k, bucket[p]) => (ValOfKeyInBktAtAddr(k, bucket[p]) = ValOfKeyInBktAtAddr(k, newbkt[p]))
              BY Zenon DEF NewBktInv
            <6>11. c_pred.state[k] = IF KeyInBktAtAddr(k, bucket[p]) THEN ValOfKeyInBktAtAddr(k, bucket[p]) ELSE NULL
              BY <6>9, <6>10, Zenon
            <6>12. c_pred.state[k] = IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL
              BY <6>11, <6>6, Zenon
            <6> QED
              BY <6>12, Zenon
          <5> QED
            BY <5>1, <5>2, <5>3
        <4>2. ASSUME NEW q \in ProcSet
              PROVE
                CASE pc[q] = RemainderID 
                    -> (c_pred.op[q] = BOT /\ c_pred.arg[q] = BOT /\ c_pred.res[q] = BOT)
                  [] pc[q] = "F1"
                    -> (c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q]))
                  [] pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = NULL)
                  [] pc[q] = "F3"
                    -> (c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q])
                  [] pc[q] \in {"I1", "I3", "I4"}
                    -> (c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q]))
                  [] pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "I5"
                    -> (c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q])
                  [] pc[q] \in {"U1", "U2", "U3", "U4"}
                    -> (c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "U5"
                    -> (c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q])
                  [] pc[q] \in {"R1", "R3", "R4"}
                    -> (c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = NULL)
                  [] pc[q] = "R5"
                    -> (c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q])
          <5> USE <4>2
          <5>1. CASE pc[q] = RemainderID
            <6> USE <5>1
            <6> SUFFICES c_pred.op[q] = BOT /\ c_pred.arg[q] = BOT /\ c_pred.res[q] = BOT
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] = RemainderID
              BY RemDef, Zenon
            <6>4. c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4
          <5>2. CASE pc[q] = "F1"
            <6> USE <5>2
            <6> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] = "F1"
              BY RemDef, Zenon
            <6>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4
          <5>3. CASE pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
            <6> USE <5>3
            <6> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
              BY RemDef, Zenon DEF KeyInBktAtAddr
            <6>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
              <7> DEFINE bkt_arr == MemLocs'[bucket'[q]]
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg'[q].key
              <7>1. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = bkt_arr[idx].val
                BY Zenon DEF ValOfKeyInBktAtAddr
              <7>2. bkt_arr = MemLocs[bucket[q]]
                BY Zenon
              <7>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
                BY Zenon
              <7> QED
                BY <7>1, <7>2, <7>3, Isa DEF ValOfKeyInBktAtAddr
            <6> QED
              BY <6>2, <6>4, <6>5
          <5>4. CASE pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
            <6> USE <5>4
            <6> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = NULL
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
              BY RemDef, Zenon DEF KeyInBktAtAddr
            <6>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4
          <5>5. CASE pc[q] = "F3"
            <6> USE <5>5
            <6> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] = "F3"
              BY RemDef, Zenon
            <6>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4 
          <5>6. CASE pc[q] \in {"I1", "I3", "I4"}
            <6> USE <5>6
            <6> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
              BY RemDef, Zenon
            <6>A. CASE p = q
              <7> USE <6>A
              <7>1. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = BOT
                BY <3>1 DEF ConfigDomain
              <7>2. pc'[q] = "I5"
                BY Zenon
              <7>3. c.op[q] = "Insert" /\ c.arg[p] = arg[q]
                BY <7>2, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>1, <7>3
            <6> SUFFICES ASSUME p # q
                          PROVE  c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
              BY <6>A
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              OBVIOUS
            <6>3. pc'[q] \in {"I1", "I3", "I4"}
              BY RemDef, Zenon
            <6>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4
          <5>7. CASE pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
            <6> USE <5>7
            <6> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
              BY RemDef, Zenon DEF KeyInBktAtAddr
            <6>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
              <7> DEFINE bkt_arr == MemLocs'[bucket'[q]]
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg'[q].key
              <7>1. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = bkt_arr[idx].val
                BY Zenon DEF ValOfKeyInBktAtAddr
              <7>2. bkt_arr = MemLocs[bucket[q]]
                BY Zenon
              <7>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
                BY Zenon
              <7> QED
                BY <7>1, <7>2, <7>3, Isa DEF ValOfKeyInBktAtAddr
            <6> QED
              BY <6>2, <6>4, <6>5
          <5>8. CASE pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
            <6> USE <5>8
            <6> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
              BY RemDef, Zenon DEF KeyInBktAtAddr
            <6>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4
          <5>9. CASE pc[q] = "I5"
            <6> USE <5>9
            <6> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] = "I5"
              BY RemDef, Zenon
            <6>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4
          <5>10. CASE pc[q] \in {"U1", "U2", "U3", "U4"}
            <6> USE <5>10
            <6> SUFFICES c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] \in {"U1", "U2", "U3", "U4"}
              BY RemDef, Zenon
            <6>4. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4
          <5>11. CASE pc[q] = "U5" 
            <6> USE <5>11
            <6> SUFFICES c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] = "U5"
              BY RemDef, Zenon
            <6>4. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4
          <5>12. CASE pc[q] \in {"R1", "R3", "R4"}
            <6> USE <5>12
            <6> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] \in {"R1", "R3", "R4"}
              BY RemDef, Zenon
            <6>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4
          <5>13. CASE pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q]) 
            <6> USE <5>13
            <6> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
              BY RemDef, Zenon DEF KeyInBktAtAddr
            <6>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4              
          <5>14. CASE pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
            <6> USE <5>14
            <6> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = NULL
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
              BY RemDef, Zenon DEF KeyInBktAtAddr
            <6>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4    
          <5>15. CASE pc[q] = "R5"
            <6> USE <5>15
            <6> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] = "R5"
              BY RemDef, Zenon
            <6>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4
          <5> QED
              BY RemDef, ZenonT(120),
                  <5>1, <5>2, <5>3, <5>4, <5>5, <5>6, <5>7, <5>8, <5>9, 
                  <5>10, <5>11, <5>12, <5>13, <5>14, <5>15
              DEF LineIDs 
        <4> QED
          BY <3>1, <4>1, <4>2, Zenon DEF S
      <3>3. Delta(c_pred, p, c)
        <4>1. c_pred.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL]
          BY <3>1, <3>2, Zenon DEF S
        <4>2. c_pred.op[p] = "Insert" /\ c_pred.arg[p] = arg[p] /\ c_pred.res[p] = BOT
          BY <3>1, <3>2, Zenon, RemDef DEF S
        <4>3. arg[p] \in ArgsOf("Insert") /\ arg[p].key \in KeyDomain
          BY RemDef, Zenon DEF ArgsOf, LineIDtoOp 
        <4>4. c_pred.state[c_pred.arg[p].key] = NULL
          BY <4>1, <4>2, <4>3, Zenon DEF BktInv
        <4> SUFFICES /\ c.state = [c_pred.state EXCEPT ![arg[p].key] = arg[p].val]
                     /\ c.res = [c_pred.res EXCEPT ![p] = NULL]
          BY <4>2, <4>3, <4>4, Zenon DEF Delta
        <4> SUFFICES /\ c.state[arg[p].key] = arg[p].val
                     /\ c.res[p] = NULL
          BY <3>2, <4>3, ZenonT(60) DEF ConfigDomain, StateDomain
        <4>5. c.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]])' THEN ValOfKeyInBktAtAddr(k, A[Hash[k]])' ELSE NULL]
          BY SPrimeRewrite, Zenon DEF SPrime
        <4>6. c.state[arg[p].key] = IF KeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]])' THEN ValOfKeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]])' ELSE NULL
          BY <4>5, <4>3, Zenon
        <4>7. newbkt[p] = A'[Hash[arg[p].key]]
          BY Zenon, HashDef, <4>3
        <4>8. MemLocs[A'[Hash[arg[p].key]]] = MemLocs[newbkt[p]]
          BY Zenon, <4>7
        <4>9. KeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]])' = KeyInBktAtAddr(arg[p].key, newbkt[p])
          BY Zenon, <4>7 DEF KeyInBktAtAddr
        <4>10. ValOfKeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]])' = 
          MemLocs[A'[Hash[arg[p].key]]][CHOOSE index \in 1..Len(MemLocs[A'[Hash[arg[p].key]]]) : MemLocs[A'[Hash[arg[p].key]]][index].key = arg[p].key].val
          BY Zenon DEF ValOfKeyInBktAtAddr
        <4>11. ValOfKeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]])' = 
          MemLocs[newbkt[p]][CHOOSE index \in 1..Len(MemLocs[newbkt[p]]) : MemLocs[newbkt[p]][index].key = arg[p].key].val
          BY <4>10, <4>8
        <4>12. ValOfKeyInBktAtAddr(arg[p].key, newbkt[p]) = 
          MemLocs[newbkt[p]][CHOOSE index \in 1..Len(MemLocs[newbkt[p]]) : MemLocs[newbkt[p]][index].key = arg[p].key].val
          BY Zenon DEF ValOfKeyInBktAtAddr
        <4>13. ValOfKeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]])' = ValOfKeyInBktAtAddr(arg[p].key, newbkt[p])
          BY <4>11, <4>12, Zenon
        <4>14. c.state[arg[p].key] = IF KeyInBktAtAddr(arg[p].key, newbkt[p]) THEN ValOfKeyInBktAtAddr(arg[p].key, newbkt[p]) ELSE NULL
          BY <4>6, <4>9, <4>13, Zenon
        <4>15. c.state[arg[p].key] = arg[p].val
          BY <4>14, Zenon DEF NewBktInv
        <4>16. pc'[p] = "I5"
          BY Zenon
        <4>17. c.res[p] = r'[p]
          BY <4>16, SPrimeRewrite, RemDef, Zenon DEF SPrime
        <4>18. c.res[p] = NULL
          BY <4>17, Zenon DEF BktInv
        <4> QED
          BY <4>18, <4>15
      <3> QED
        BY <3>1, <3>2, <3>3, SingleDeltaEvolve
    <2>2. CASE A[Hash[arg[p].key]] # bucket[p]
      <3> USE <2>2
      <3> SUFFICES c \in S
        BY EmptySeqEvolve
      <3>1. c.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL]
        <4>1. c.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]])' THEN ValOfKeyInBktAtAddr(k, A[Hash[k]])' ELSE NULL]
          BY Zenon, SPrimeRewrite DEF SPrime
        <4>2. \A k \in KeyDomain : KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
          BY Zenon DEF KeyInBktAtAddr
        <4>3. \A k \in KeyDomain : ValOfKeyInBktAtAddr(k, A[Hash[k]])' = ValOfKeyInBktAtAddr(k, A[Hash[k]])
          <5> SUFFICES ASSUME NEW k \in KeyDomain
                        PROVE  ValOfKeyInBktAtAddr(k, A[Hash[k]])' = ValOfKeyInBktAtAddr(k, A[Hash[k]])
            OBVIOUS
          <5> bkt_arr == MemLocs'[A'[Hash[k]]]
          <5> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
          <5>1. ValOfKeyInBktAtAddr(k, A[Hash[k]])' = bkt_arr[idx].val
            BY DEF ValOfKeyInBktAtAddr
          <5>2. bkt_arr = MemLocs[A[Hash[k]]]
            BY Zenon
          <5> QED
            BY <5>1, <5>2, ZenonT(30) DEF ValOfKeyInBktAtAddr
        <4> QED
          BY <4>1, <4>2, <4>3
      <3>2. ASSUME NEW q \in ProcSet
            PROVE
                CASE pc[q] = RemainderID 
                    -> (c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT)
                  [] pc[q] = "F1"
                    -> (c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                  [] pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q]))
                  [] pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL)
                  [] pc[q] = "F3"
                    -> (c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q])
                  [] pc[q] \in {"I1", "I3", "I4"}
                    -> (c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                  [] pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q]))
                  [] pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                  [] pc[q] = "I5"
                    -> (c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q])
                  [] pc[q] \in {"U1", "U2", "U3", "U4"}
                    -> (c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                  [] pc[q] = "U5"
                    -> (c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q])
                  [] pc[q] \in {"R1", "R3", "R4"}
                    -> (c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                  [] pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                  [] pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL)
                  [] pc[q] = "R5"
                    -> (c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q])
        <4> USE <3>2
        <4>A. \A k \in KeyDomain : KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, bucket[q])'
          BY Zenon DEF KeyInBktAtAddr
        <4>B. \A k \in KeyDomain : ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, bucket[q])
          <5> SUFFICES ASSUME NEW k \in KeyDomain
                        PROVE  ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, bucket[q])
            OBVIOUS
          <5> bkt_arr == MemLocs'[bucket'[q]]
          <5> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
          <5>1. ValOfKeyInBktAtAddr(k, bucket[q])' = bkt_arr[idx].val
            BY DEF ValOfKeyInBktAtAddr
          <5>2. bkt_arr = MemLocs[bucket[q]]
            BY Zenon
          <5> QED
            BY <5>1, <5>2, ZenonT(30) DEF ValOfKeyInBktAtAddr
        <4>1. CASE pc[q] = RemainderID
          <5> USE <4>1
          <5> SUFFICES c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. pc'[q] = RemainderID
            BY RemDef, Zenon
          <5>2. c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>2. CASE pc[q] = "F1"
          <5> USE <4>2
          <5> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. pc'[q] = "F1"
            BY RemDef, Zenon
          <5>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>3. CASE pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>3
          <5> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            BY RemDef, Zenon
          <5>1. pc'[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <5>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5>3. arg[q].key = arg'[q].key /\ arg[q].key \in KeyDomain
            BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
          <5>4. c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            BY <5>2, <5>3, <4>B
          <5> QED
            BY <5>2, <5>4
        <4>4. CASE pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>4
          <5> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
            BY RemDef, Zenon
          <5>2. pc'[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>3. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
            BY <5>2,  SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>3
        <4>5. CASE pc[q] = "F3"
          <5> USE <4>5
          <5> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY RemDef, Zenon
          <5>1. pc'[q] = "F3"
            BY RemDef, Zenon
          <5>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2 
        <4>6. CASE pc[q] \in {"I1", "I3", "I4"}
          <5> USE <4>6
          <5> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. pc'[q] \in {"I1", "I3", "I4"}
            BY RemDef, Zenon
          <5>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2 
        <4>7. CASE pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>7
          <5> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            BY RemDef, Zenon
          <5>1. CASE p = q
            <6> USE <5>1
            <6>1. c.op[p] = "Insert" /\ c.arg[p] = arg[p] /\ c.res[p] = r'[p]
              BY SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6>2. r'[p] = ValOfKeyInBktAtAddr(arg[p].key, bucket[p])
              BY Zenon
            <6> QED
              BY <6>1, <6>2
          <5> SUFFICES ASSUME p # q
                        PROVE  c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            BY <5>1
          <5>2. pc'[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>3. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <5>2,  SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5>4. arg[q].key = arg'[q].key /\ arg[q].key \in KeyDomain
            BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
          <5>5. c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            BY <5>3, <5>4, <4>B
          <5> QED
            BY <5>3, <5>5
        <4>8. CASE pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>8
          <5> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. CASE p = q
            <6> USE <5>1
            <6>1. c.op[p] = "Insert" /\ c.arg[p] = arg[p] /\ c.res[p] = BOT
              BY SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>1
          <5> SUFFICES ASSUME p # q
                        PROVE  c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>1
          <5>2. pc'[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>3. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>2, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>3 
        <4>9. CASE pc[q] = "I5"
          <5> USE <4>9
          <5> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY RemDef, Zenon
          <5>1. pc'[q] = "I5"
            BY RemDef, Zenon 
          <5>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2 
        <4>10. CASE pc[q] \in {"U1", "U2", "U3", "U4"}
          <5> USE <4>10
          <5> SUFFICES c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. pc'[q] \in {"U1", "U2", "U3", "U4"}
            BY RemDef, Zenon
          <5>2. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>11. CASE pc[q] = "U5" 
          <5> USE <4>11
          <5> SUFFICES c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY RemDef, Zenon
          <5>1. pc'[q] = "U5"
            BY RemDef, Zenon
          <5>2. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>12. CASE pc[q] \in {"R1", "R3", "R4"}
          <5> USE <4>12
          <5> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. pc'[q] \in {"R1", "R3", "R4"}
            BY RemDef, Zenon
          <5>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>13. CASE pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>13
          <5> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. pc'[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>14. CASE pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>14
          <5> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
            BY RemDef, Zenon
          <5>1. pc'[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>15. CASE pc[q] = "R5"
          <5> USE <4>15
          <5> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY RemDef, Zenon
          <5>1. pc'[q] = "R5" 
            BY RemDef, Zenon
          <5>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4> QED
            BY RemDef, ZenonT(120),
                <4>1, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, 
                <4>10, <4>11, <4>12, <4>13, <4>14, <4>15
            DEF LineIDs
      <3> QED
        BY <3>1, <3>2, Zenon DEF S
    <2> QED
      BY <2>1, <2>2
  <1>7. CASE LineAction = U1(p)
    <2> USE <1>7 DEF U1, TypeOK, Inv
    <2> SUFFICES ASSUME NEW c \in ConfigDomain,
                        c \in S'
                 PROVE  c \in Evolve(S)
      BY Zenon DEF S
    <2> SUFFICES c \in S
      BY EmptySeqEvolve
    <2>1. c.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL]
      <3>1. c.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]])' THEN ValOfKeyInBktAtAddr(k, A[Hash[k]])' ELSE NULL]
        BY Zenon, SPrimeRewrite DEF SPrime
      <3>2. \A k \in KeyDomain : KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
        BY Zenon DEF KeyInBktAtAddr
      <3>3. \A k \in KeyDomain : ValOfKeyInBktAtAddr(k, A[Hash[k]])' = ValOfKeyInBktAtAddr(k, A[Hash[k]])
        <4> SUFFICES ASSUME NEW k \in KeyDomain
                      PROVE  ValOfKeyInBktAtAddr(k, A[Hash[k]])' = ValOfKeyInBktAtAddr(k, A[Hash[k]])
          OBVIOUS
        <4> bkt_arr == MemLocs'[A'[Hash[k]]]
        <4> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
        <4>1. ValOfKeyInBktAtAddr(k, A[Hash[k]])' = bkt_arr[idx].val
          BY DEF ValOfKeyInBktAtAddr
        <4>2. bkt_arr = MemLocs[A[Hash[k]]]
          BY Zenon
        <4> QED
          BY <4>1, <4>2, ZenonT(30) DEF ValOfKeyInBktAtAddr
      <3> QED
        BY <3>1, <3>2, <3>3
    <2>2. ASSUME NEW q \in ProcSet
          PROVE
              CASE pc[q] = RemainderID 
                  -> (c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT)
                [] pc[q] = "F1"
                  -> (c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                [] pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                  -> (c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q]))
                [] pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                  -> (c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL)
                [] pc[q] = "F3"
                  -> (c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q])
                [] pc[q] \in {"I1", "I3", "I4"}
                  -> (c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                [] pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                  -> (c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q]))
                [] pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                  -> (c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                [] pc[q] = "I5"
                  -> (c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q])
                [] pc[q] \in {"U1", "U2", "U3", "U4"}
                  -> (c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                [] pc[q] = "U5"
                  -> (c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q])
                [] pc[q] \in {"R1", "R3", "R4"}
                  -> (c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                [] pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                  -> (c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                [] pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                  -> (c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL)
                [] pc[q] = "R5"
                  -> (c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q])
      <3> USE <2>2
      <3>A. q # p => \A k \in KeyDomain : KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, bucket[q])'
        BY Zenon DEF KeyInBktAtAddr
      <3>B. q # p => \A k \in KeyDomain : ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, bucket[q])
        <4> SUFFICES ASSUME NEW k \in KeyDomain, q # p
                     PROVE  ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, bucket[q])
          OBVIOUS
        <4> bkt_arr == MemLocs'[bucket'[q]]
        <4> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
        <4>1. ValOfKeyInBktAtAddr(k, bucket[q])' = bkt_arr[idx].val
          BY DEF ValOfKeyInBktAtAddr
        <4>2. bkt_arr = MemLocs[bucket[q]]
          BY Zenon
        <4> QED
          BY <4>1, <4>2, ZenonT(30) DEF ValOfKeyInBktAtAddr
      <3>1. CASE pc[q] = RemainderID
        <4> USE <3>1
        <4> SUFFICES c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
          BY RemDef, Zenon
        <4>1. pc'[q] = RemainderID
          BY RemDef, Zenon
        <4>2. c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
          BY <4>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2
      <3>2. CASE pc[q] = "F1"
        <4> USE <3>2
        <4> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY RemDef, Zenon
        <4>1. pc'[q] = "F1"
          BY RemDef, Zenon
        <4>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY <4>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2
      <3>3. CASE pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
        <4> USE <3>3
        <4> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
          BY RemDef, Zenon
        <4>1. pc'[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
          BY RemDef, Zenon DEF KeyInBktAtAddr
        <4>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
          BY <4>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4>3. arg[q].key = arg'[q].key /\ arg[q].key \in KeyDomain
          BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
        <4>4. c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
          BY <4>2, <4>3, <3>B
        <4> QED
          BY <4>2, <4>4
      <3>4. CASE pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
        <4> USE <3>4
        <4> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
          BY RemDef, Zenon
        <4>2. pc'[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
          BY RemDef, Zenon DEF KeyInBktAtAddr
        <4>3. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
          BY <4>2,  SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>3
      <3>5. CASE pc[q] = "F3"
        <4> USE <3>5
        <4> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
          BY RemDef, Zenon
        <4>1. pc'[q] = "F3"
          BY RemDef, Zenon
        <4>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
          BY <4>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2 
      <3>6. CASE pc[q] \in {"I1", "I3", "I4"}
        <4> USE <3>6
        <4> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY RemDef, Zenon
        <4>1. pc'[q] \in {"I1", "I3", "I4"}
          BY RemDef, Zenon
        <4>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY <4>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2 
      <3>7. CASE pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
        <4> USE <3>7
        <4> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
          BY RemDef, Zenon
        <4>1. CASE p = q
          <5> USE <4>1
          <5>1. c.op[p] = "Insert" /\ c.arg[p] = arg[p] /\ c.res[p] = r'[p]
            BY SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5>2. r'[p] = ValOfKeyInBktAtAddr(arg[p].key, bucket[p])
            BY Zenon
          <5> QED
            BY <5>1, <5>2
        <4> SUFFICES ASSUME p # q
                      PROVE  c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
          BY <4>1
        <4>2. pc'[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
          BY RemDef, Zenon DEF KeyInBktAtAddr
        <4>3. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
          BY <4>2,  SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4>4. arg[q].key = arg'[q].key /\ arg[q].key \in KeyDomain
          BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
        <4>5. c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
          BY <4>3, <4>4, <3>B
        <4> QED
          BY <4>3, <4>5
      <3>8. CASE pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
        <4> USE <3>8
        <4> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY RemDef, Zenon
        <4>1. CASE p = q
          <5> USE <4>1
          <5>1. c.op[p] = "Insert" /\ c.arg[p] = arg[p] /\ c.res[p] = BOT
            BY SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>1
        <4> SUFFICES ASSUME p # q
                      PROVE  c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY <4>1
        <4>2. pc'[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
          BY RemDef, Zenon DEF KeyInBktAtAddr
        <4>3. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY <4>2, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>3 
      <3>9. CASE pc[q] = "I5"
        <4> USE <3>9
        <4> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
          BY RemDef, Zenon
        <4>1. pc'[q] = "I5"
          BY RemDef, Zenon 
        <4>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
          BY <4>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2 
      <3>10. CASE pc[q] \in {"U1", "U2", "U3", "U4"}
        <4> USE <3>10
        <4> SUFFICES c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY RemDef, Zenon
        <4>1. pc'[q] \in {"U1", "U2", "U3", "U4"}
          BY RemDef, Zenon
        <4>2. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY <4>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2
      <3>11. CASE pc[q] = "U5" 
        <4> USE <3>11
        <4> SUFFICES c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
          BY RemDef, Zenon
        <4>1. pc'[q] = "U5"
          BY RemDef, Zenon
        <4>2. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
          BY <4>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2
      <3>12. CASE pc[q] \in {"R1", "R3", "R4"}
        <4> USE <3>12
        <4> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY RemDef, Zenon
        <4>1. pc'[q] \in {"R1", "R3", "R4"}
          BY RemDef, Zenon
        <4>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY <4>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2
      <3>13. CASE pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
        <4> USE <3>13
        <4> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY RemDef, Zenon
        <4>1. pc'[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
          BY RemDef, Zenon DEF KeyInBktAtAddr
        <4>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY <4>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2
      <3>14. CASE pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
        <4> USE <3>14
        <4> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
          BY RemDef, Zenon
        <4>1. pc'[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
          BY RemDef, Zenon DEF KeyInBktAtAddr
        <4>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
          BY <4>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2
      <3>15. CASE pc[q] = "R5"
        <4> USE <3>15
        <4> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
          BY RemDef, Zenon
        <4>1. pc'[q] = "R5" 
          BY RemDef, Zenon
        <4>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
          BY <4>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2
      <3> QED
          BY RemDef, ZenonT(120),
              <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9, 
              <3>10, <3>11, <3>12, <3>13, <3>14, <3>15
          DEF LineIDs
    <2> QED
      BY <2>1, <2>2, Zenon DEF S
  <1>8. CASE LineAction = U2(p)
    <2> USE <1>8 DEF U2, TypeOK, Inv
    <2> SUFFICES ASSUME NEW c \in ConfigDomain,
                        c \in S'
                 PROVE  c \in Evolve(S)
      BY Zenon DEF S
    <2> SUFFICES c \in S
      BY EmptySeqEvolve
    <2>1. c.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL]
      <3>1. c.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]])' THEN ValOfKeyInBktAtAddr(k, A[Hash[k]])' ELSE NULL]
        BY Zenon, SPrimeRewrite DEF SPrime
      <3>2. \A k \in KeyDomain : KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
        BY Zenon DEF KeyInBktAtAddr
      <3>3. \A k \in KeyDomain : ValOfKeyInBktAtAddr(k, A[Hash[k]])' = ValOfKeyInBktAtAddr(k, A[Hash[k]])
        <4> SUFFICES ASSUME NEW k \in KeyDomain
                      PROVE  ValOfKeyInBktAtAddr(k, A[Hash[k]])' = ValOfKeyInBktAtAddr(k, A[Hash[k]])
          OBVIOUS
        <4> bkt_arr == MemLocs'[A'[Hash[k]]]
        <4> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
        <4>1. ValOfKeyInBktAtAddr(k, A[Hash[k]])' = bkt_arr[idx].val
          BY DEF ValOfKeyInBktAtAddr
        <4>2. bkt_arr = MemLocs[A[Hash[k]]]
          BY Zenon
        <4> QED
          BY <4>1, <4>2, ZenonT(30) DEF ValOfKeyInBktAtAddr
      <3> QED
        BY <3>1, <3>2, <3>3
    <2>2. ASSUME NEW q \in ProcSet
          PROVE
              CASE pc[q] = RemainderID 
                  -> (c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT)
                [] pc[q] = "F1"
                  -> (c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                [] pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                  -> (c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q]))
                [] pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                  -> (c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL)
                [] pc[q] = "F3"
                  -> (c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q])
                [] pc[q] \in {"I1", "I3", "I4"}
                  -> (c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                [] pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                  -> (c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q]))
                [] pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                  -> (c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                [] pc[q] = "I5"
                  -> (c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q])
                [] pc[q] \in {"U1", "U2", "U3", "U4"}
                  -> (c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                [] pc[q] = "U5"
                  -> (c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q])
                [] pc[q] \in {"R1", "R3", "R4"}
                  -> (c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                [] pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                  -> (c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                [] pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                  -> (c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL)
                [] pc[q] = "R5"
                  -> (c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q])
      <3> USE <2>2
      <3>A. \A k \in KeyDomain : KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, bucket[q])'
        BY Zenon DEF KeyInBktAtAddr
      <3>B. \A k \in KeyDomain : ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, bucket[q])
        <4> SUFFICES ASSUME NEW k \in KeyDomain
                      PROVE  ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, bucket[q])
          OBVIOUS
        <4> bkt_arr == MemLocs'[bucket'[q]]
        <4> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
        <4>1. ValOfKeyInBktAtAddr(k, bucket[q])' = bkt_arr[idx].val
          BY DEF ValOfKeyInBktAtAddr
        <4>2. bkt_arr = MemLocs[bucket[q]]
          BY Zenon
        <4> QED
          BY <4>1, <4>2, ZenonT(30) DEF ValOfKeyInBktAtAddr
      <3>1. CASE pc[q] = RemainderID
        <4> USE <3>1
        <4> SUFFICES c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
          BY RemDef, Zenon
        <4>1. pc'[q] = RemainderID
          BY RemDef, Zenon
        <4>2. c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
          BY <4>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2
      <3>2. CASE pc[q] = "F1"
        <4> USE <3>2
        <4> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY RemDef, Zenon
        <4>1. pc'[q] = "F1"
          BY RemDef, Zenon
        <4>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY <4>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2
      <3>3. CASE pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
        <4> USE <3>3
        <4> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
          BY RemDef, Zenon
        <4>1. CASE q = p
          <5> USE <4>1
          <5>1. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r'[q]
            BY SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            BY <5>1, Zenon
          <5> QED
            BY <5>2
        <4> SUFFICES ASSUME q # p
                      PROVE  c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
          BY <4>1
        <4>2. pc'[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
          BY RemDef, Zenon DEF KeyInBktAtAddr
        <4>3. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
          BY <4>2,  SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4>4. arg[q].key = arg'[q].key /\ arg[q].key \in KeyDomain
          BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
        <4>5. c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
          BY <4>3, <4>4, <3>B
        <4> QED
          BY <4>3, <4>5
      <3>4. CASE pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
        <4> USE <3>4
        <4> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
          BY RemDef, Zenon
        <4>1. CASE q = p
          <5> USE <4>1
          <5>1. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r'[q]
            BY SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
            BY <5>1, Zenon
          <5> QED
            BY <5>2
        <4> SUFFICES ASSUME q # p
                      PROVE  c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
          BY <4>1
        <4>2. pc'[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
          BY RemDef, Zenon DEF KeyInBktAtAddr
        <4>3. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
          BY <4>2,  SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>3
      <3>5. CASE pc[q] = "F3"
        <4> USE <3>5
        <4> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
          BY RemDef, Zenon
        <4>1. pc'[q] = "F3"
          BY RemDef, Zenon
        <4>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
          BY <4>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2 
      <3>6. CASE pc[q] \in {"I1", "I3", "I4"}
        <4> USE <3>6
        <4> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY RemDef, Zenon
        <4>1. pc'[q] \in {"I1", "I3", "I4"}
          BY RemDef, Zenon
        <4>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY <4>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2 
      <3>7. CASE pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
        <4> USE <3>7
        <4> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
          BY RemDef, Zenon
        <4>2. pc'[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
          BY RemDef, Zenon DEF KeyInBktAtAddr
        <4>3. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
          BY <4>2,  SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4>4. arg[q].key = arg'[q].key /\ arg[q].key \in KeyDomain
          BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
        <4>5. c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
          BY <4>3, <4>4, <3>B
        <4> QED
          BY <4>3, <4>5
      <3>8. CASE pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
        <4> USE <3>8
        <4> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY RemDef, Zenon
        <4>1. pc'[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
          BY RemDef, Zenon DEF KeyInBktAtAddr
        <4>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY <4>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2 
      <3>9. CASE pc[q] = "I5"
        <4> USE <3>9
        <4> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
          BY RemDef, Zenon
        <4>1. pc'[q] = "I5"
          BY RemDef, Zenon 
        <4>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
          BY <4>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2 
      <3>10. CASE pc[q] \in {"U1", "U2", "U3", "U4"}
        <4> USE <3>10
        <4> SUFFICES c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY RemDef, Zenon
        <4>1. pc'[q] \in {"U1", "U2", "U3", "U4"}
          BY RemDef, Zenon
        <4>2. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY <4>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2
      <3>11. CASE pc[q] = "U5" 
        <4> USE <3>11
        <4> SUFFICES c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
          BY RemDef, Zenon
        <4>1. pc'[q] = "U5"
          BY RemDef, Zenon
        <4>2. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
          BY <4>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2
      <3>12. CASE pc[q] \in {"R1", "R3", "R4"}
        <4> USE <3>12
        <4> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY RemDef, Zenon
        <4>1. pc'[q] \in {"R1", "R3", "R4"}
          BY RemDef, Zenon
        <4>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY <4>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2
      <3>13. CASE pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
        <4> USE <3>13
        <4> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY RemDef, Zenon
        <4>1. pc'[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
          BY RemDef, Zenon DEF KeyInBktAtAddr
        <4>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY <4>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2
      <3>14. CASE pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
        <4> USE <3>14
        <4> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
          BY RemDef, Zenon
        <4>1. pc'[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
          BY RemDef, Zenon DEF KeyInBktAtAddr
        <4>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
          BY <4>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2
      <3>15. CASE pc[q] = "R5"
        <4> USE <3>15
        <4> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
          BY RemDef, Zenon
        <4>1. pc'[q] = "R5" 
          BY RemDef, Zenon
        <4>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
          BY <4>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2
      <3> QED
          BY RemDef, ZenonT(120),
              <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9, 
              <3>10, <3>11, <3>12, <3>13, <3>14, <3>15
          DEF LineIDs
    <2> QED
      BY <2>1, <2>2, Zenon DEF S
  <1>9. CASE LineAction = U3(p)
    <2> USE <1>9 DEF TypeOK, Inv
    <2> SUFFICES ASSUME NEW c \in ConfigDomain,
                        c \in S'
                 PROVE  c \in Evolve(S)
      BY Zenon DEF S
    <2> SUFFICES c \in S
      BY EmptySeqEvolve
    <2>1. CASE bucket[p] = NULL
      <3> PICK addr \in Addrs : 
                    /\ addr \notin AllocAddrs
                    /\ AllocAddrs' = AllocAddrs \cup {addr}
                    /\ newbkt' = [newbkt EXCEPT ![p] = addr]
                    /\ MemLocs' = [MemLocs EXCEPT ![addr] = <<arg[p]>>]
        BY <2>1, Zenon DEF U3
      <3> /\ pc[p] = "U3"
          /\ pc' = [pc EXCEPT ![p] = "U4"]
          /\ UNCHANGED <<A, bucket, r, arg, ret>>
        BY Zenon DEF U3
      <3>1. c.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL]
        <4>1. c.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]])' THEN ValOfKeyInBktAtAddr(k, A[Hash[k]])' ELSE NULL]
          BY Zenon, SPrimeRewrite DEF SPrime
        <4>2. \A k \in KeyDomain : KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
          <5> SUFFICES ASSUME NEW k \in KeyDomain
                        PROVE  KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
            OBVIOUS
          <5>1. A'[Hash[k]] = A[Hash[k]]
            BY Zenon
          <5>2. CASE A[Hash[k]] = NULL
            BY <5>1, <5>2 DEF KeyInBktAtAddr
          <5> SUFFICES ASSUME A[Hash[k]] # NULL
                        PROVE  KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
            BY <5>2
          <5>3. A[Hash[k]] \in AllocAddrs
            BY HashDef, Zenon
          <5>4. A[Hash[k]] # addr
            BY NULLDef, <5>3
          <5>5. \A a \in Addrs : a # addr => MemLocs'[a] = MemLocs[a]
            BY Zenon
          <5>6. MemLocs'[A'[Hash[k]]] = MemLocs[A[Hash[k]]]
            BY <5>1, <5>4, <5>5
          <5> QED
            BY <5>6, Zenon DEF KeyInBktAtAddr
        <4>3. \A k \in KeyDomain : KeyInBktAtAddr(k, A[Hash[k]]) => (ValOfKeyInBktAtAddr(k, A[Hash[k]]) = ValOfKeyInBktAtAddr(k, A[Hash[k]])')
          <5> SUFFICES ASSUME NEW k \in KeyDomain,
                              NEW bkt_arr,
                              A[Hash[k]] # NULL,
                              bkt_arr = MemLocs[A[Hash[k]]],
                              \E index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
                        PROVE  ValOfKeyInBktAtAddr(k, A[Hash[k]]) = ValOfKeyInBktAtAddr(k, A[Hash[k]])'
            BY Zenon DEF KeyInBktAtAddr
          <5>1. A'[Hash[k]] = A[Hash[k]]
            BY Zenon
          <5>2. A[Hash[k]] \in AllocAddrs
            BY HashDef, Zenon
          <5>3. A[Hash[k]] # addr
            BY NULLDef, <5>2
          <5>4. \A a \in Addrs : a # addr => MemLocs'[a] = MemLocs[a]
            BY Zenon
          <5>5. MemLocs'[A'[Hash[k]]] = MemLocs[A[Hash[k]]]
            BY <5>1, <5>3, <5>4
          <5> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
          <5>6. ValOfKeyInBktAtAddr(k, A[Hash[k]]) = bkt_arr[idx].val
            BY Zenon DEF ValOfKeyInBktAtAddr
          <5>7. ValOfKeyInBktAtAddr(k, A[Hash[k]])' = bkt_arr[idx].val
            BY Isa, <5>5 DEF ValOfKeyInBktAtAddr
          <5> QED
            BY <5>6, <5>7, Zenon
        <4> QED
          BY <4>1, <4>2, <4>3, Zenon
      <3>2. ASSUME NEW q \in ProcSet
              PROVE
                  CASE pc[q] = RemainderID 
                      -> (c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT)
                    [] pc[q] = "F1"
                      -> (c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                    [] pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                      -> (c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q]))
                    [] pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                      -> (c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL)
                    [] pc[q] = "F3"
                      -> (c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q])
                    [] pc[q] \in {"I1", "I3", "I4"}
                      -> (c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                    [] pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                      -> (c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q]))
                    [] pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                      -> (c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                    [] pc[q] = "I5"
                      -> (c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q])
                    [] pc[q] \in {"U1", "U2", "U3", "U4"}
                      -> (c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                    [] pc[q] = "U5"
                      -> (c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q])
                    [] pc[q] \in {"R1", "R3", "R4"}
                      -> (c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                    [] pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                      -> (c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                    [] pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                      -> (c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL)
                    [] pc[q] = "R5"
                      -> (c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q])
        <4> USE <3>2
        <4>A. KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
          <5>1. bucket[q] = bucket'[q]
            BY Zenon
          <5>2. CASE bucket[q] = NULL
            BY <5>1, <5>2, Zenon DEF KeyInBktAtAddr
          <5> SUFFICES ASSUME bucket[q] # NULL
                        PROVE  KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <5>2
          <5>3. bucket[q] \in AllocAddrs
            BY NULLDef, Zenon
          <5>4. bucket[q] # addr
            BY <5>3
          <5>5. \A a \in Addrs : a # addr => MemLocs'[a] = MemLocs[a]
            BY Zenon
          <5>6. MemLocs'[bucket'[q]] = MemLocs[bucket[q]]
            BY <5>1, <5>4, <5>5
          <5> QED
            BY <5>6, Zenon DEF KeyInBktAtAddr
        <4>B. KeyInBktAtAddr(arg[q].key, bucket[q]) => (ValOfKeyInBktAtAddr(arg[q].key, bucket[q]) = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])')
          <5> SUFFICES ASSUME NEW bkt_arr,
                              bkt_arr = MemLocs[bucket[q]],
                              bucket[q] # NULL,
                              \E index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
                        PROVE  ValOfKeyInBktAtAddr(arg[q].key, bucket[q]) = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
            BY Zenon DEF KeyInBktAtAddr
          <5>1. bucket[q] = bucket'[q]
            BY Zenon
          <5>2. bucket[q] \in AllocAddrs
            BY NULLDef, Zenon
          <5>3. bucket[q] # addr
            BY <5>2
          <5>4. \A a \in Addrs : a # addr => MemLocs'[a] = MemLocs[a]
            BY Zenon
          <5>5. MemLocs'[bucket'[q]] = MemLocs[bucket[q]]
            BY <5>1, <5>3, <5>4 
          <5> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
          <5>6. ValOfKeyInBktAtAddr(arg[q].key, bucket[q]) = bkt_arr[idx].val
            BY Zenon DEF ValOfKeyInBktAtAddr
          <5>7. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = bkt_arr[idx].val
            BY Isa, <5>5 DEF ValOfKeyInBktAtAddr
          <5> QED
            BY <5>6, <5>7, Zenon
        <4>1. CASE pc[q] = RemainderID
          <5> USE <4>1
          <5> SUFFICES c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. pc'[q] = RemainderID
            BY RemDef, Zenon
          <5>2. c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>2. CASE pc[q] = "F1"
          <5> USE <4>2
          <5> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. pc'[q] = "F1"
            BY RemDef, Zenon
          <5>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2  
        <4>3. CASE pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>3
          <5> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            BY RemDef, Zenon
          <5>1. pc'[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <4>A, RemDef, Zenon DEF KeyInBktAtAddr
          <5>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <5>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5>3. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            BY <4>B, Zenon
          <5> QED
            BY <5>2, <5>3
        <4>4. CASE pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>4
          <5> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
            BY RemDef, Zenon
          <5>1. pc'[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <4>A, RemDef, Zenon DEF KeyInBktAtAddr
          <5>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
            BY <5>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>5. CASE pc[q] = "F3" 
          <5> USE <4>5
          <5> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY RemDef, Zenon
          <5>1. pc'[q] = "F3"
            BY RemDef, Zenon
          <5>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>6. CASE pc[q] \in {"I1", "I3", "I4"}
          <5> USE <4>6
          <5> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>2. pc'[q] \in {"I1", "I3", "I4"}
            BY RemDef, Zenon
          <5>3. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>2,  SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>3
        <4>7. CASE pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>7
          <5> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            BY RemDef, Zenon
          <5>1. pc'[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <4>A, RemDef, Zenon DEF KeyInBktAtAddr
          <5>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <5>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5>3. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            BY <4>B, Zenon
          <5> QED
            BY <5>2, <5>3
        <4>8. CASE pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>8
          <5> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. pc'[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <4>A, RemDef, Zenon DEF KeyInBktAtAddr
          <5>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>9. CASE pc[q] = "I5"
          <5> USE <4>9
          <5> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY RemDef, Zenon
          <5>1. pc'[q] = "I5"
            BY RemDef, Zenon
          <5>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>10. CASE pc[q] \in {"U1", "U2", "U3", "U4"}
          <5> USE <4>10
          <5> SUFFICES c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. pc'[q] \in {"U1", "U2", "U3", "U4"}
            BY RemDef, Zenon
          <5>2. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>11. CASE pc[q] = "U5" 
          <5> USE <4>11
          <5> SUFFICES c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY RemDef, Zenon
          <5>1. pc'[q] = "U5"
            BY RemDef, Zenon
          <5>2. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>12. CASE pc[q] \in {"R1", "R3", "R4"}
          <5> USE <4>12
          <5> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. pc'[q] \in {"R1", "R3", "R4"}
            BY RemDef, Zenon
          <5>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>13. CASE pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>13
          <5> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. pc'[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <4>A, RemDef, Zenon DEF KeyInBktAtAddr
          <5>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>14. CASE pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>14
          <5> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
            BY RemDef, Zenon
          <5>1. pc'[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <4>A, RemDef, Zenon DEF KeyInBktAtAddr
          <5>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
            BY <5>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>15. CASE pc[q] = "R5"
          <5> USE <4>15
          <5> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY RemDef, Zenon
          <5>1. pc'[q] = "R5"
            BY RemDef, Zenon
          <5>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4> QED
            BY RemDef, ZenonT(120),
                <4>1, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, 
                <4>10, <4>11, <4>12, <4>13, <4>14, <4>15
            DEF LineIDs
      <3> QED
        BY <3>1, <3>2, Zenon DEF S
    <2>2. CASE bucket[p] # NULL /\ r[p] = NULL
      <3> PICK addr \in Addrs : 
                    /\ addr \notin AllocAddrs
                    /\ AllocAddrs' = AllocAddrs \cup {addr}
                    /\ newbkt' = [newbkt EXCEPT ![p] = addr]
                    /\ MemLocs' = [MemLocs EXCEPT ![addr] = Append(MemLocs[bucket[p]], arg[p])]
        BY <2>2, Zenon DEF U3
      <3> /\ pc[p] = "U3"
          /\ pc' = [pc EXCEPT ![p] = "U4"]
          /\ UNCHANGED <<A, bucket, r, arg, ret>>
        BY Zenon DEF U3
      <3>1. c.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL]
        <4>1. c.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]])' THEN ValOfKeyInBktAtAddr(k, A[Hash[k]])' ELSE NULL]
          BY Zenon, SPrimeRewrite DEF SPrime
        <4>2. \A k \in KeyDomain : KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
          <5> SUFFICES ASSUME NEW k \in KeyDomain
                        PROVE  KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
            OBVIOUS
          <5>1. A'[Hash[k]] = A[Hash[k]]
            BY Zenon
          <5>2. CASE A[Hash[k]] = NULL
            BY <5>1, <5>2 DEF KeyInBktAtAddr
          <5> SUFFICES ASSUME A[Hash[k]] # NULL
                        PROVE  KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
            BY <5>2
          <5>3. A[Hash[k]] \in AllocAddrs
            BY HashDef, Zenon
          <5>4. A[Hash[k]] # addr
            BY NULLDef, <5>3
          <5>5. \A a \in Addrs : a # addr => MemLocs'[a] = MemLocs[a]
            BY Zenon
          <5>6. MemLocs'[A'[Hash[k]]] = MemLocs[A[Hash[k]]]
            BY <5>1, <5>4, <5>5
          <5> QED
            BY <5>6, Zenon DEF KeyInBktAtAddr
        <4>3. \A k \in KeyDomain : KeyInBktAtAddr(k, A[Hash[k]]) => (ValOfKeyInBktAtAddr(k, A[Hash[k]]) = ValOfKeyInBktAtAddr(k, A[Hash[k]])')
          <5> SUFFICES ASSUME NEW k \in KeyDomain,
                              NEW bkt_arr,
                              A[Hash[k]] # NULL,
                              bkt_arr = MemLocs[A[Hash[k]]],
                              \E index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
                        PROVE  ValOfKeyInBktAtAddr(k, A[Hash[k]]) = ValOfKeyInBktAtAddr(k, A[Hash[k]])'
            BY Zenon DEF KeyInBktAtAddr
          <5>1. A'[Hash[k]] = A[Hash[k]]
            BY Zenon
          <5>2. A[Hash[k]] \in AllocAddrs
            BY HashDef, Zenon
          <5>3. A[Hash[k]] # addr
            BY NULLDef, <5>2
          <5>4. \A a \in Addrs : a # addr => MemLocs'[a] = MemLocs[a]
            BY Zenon
          <5>5. MemLocs'[A'[Hash[k]]] = MemLocs[A[Hash[k]]]
            BY <5>1, <5>3, <5>4
          <5> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
          <5>6. ValOfKeyInBktAtAddr(k, A[Hash[k]]) = bkt_arr[idx].val
            BY Zenon DEF ValOfKeyInBktAtAddr
          <5>7. ValOfKeyInBktAtAddr(k, A[Hash[k]])' = bkt_arr[idx].val
            BY Isa, <5>5 DEF ValOfKeyInBktAtAddr
          <5> QED
            BY <5>6, <5>7, Zenon
        <4> QED
          BY <4>1, <4>2, <4>3, Zenon
      <3>2. ASSUME NEW q \in ProcSet
              PROVE
                  CASE pc[q] = RemainderID 
                      -> (c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT)
                    [] pc[q] = "F1"
                      -> (c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                    [] pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                      -> (c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q]))
                    [] pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                      -> (c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL)
                    [] pc[q] = "F3"
                      -> (c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q])
                    [] pc[q] \in {"I1", "I3", "I4"}
                      -> (c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                    [] pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                      -> (c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q]))
                    [] pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                      -> (c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                    [] pc[q] = "I5"
                      -> (c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q])
                    [] pc[q] \in {"U1", "U2", "U3", "U4"}
                      -> (c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                    [] pc[q] = "U5"
                      -> (c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q])
                    [] pc[q] \in {"R1", "R3", "R4"}
                      -> (c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                    [] pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                      -> (c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                    [] pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                      -> (c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL)
                    [] pc[q] = "R5"
                      -> (c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q])
        <4> USE <3>2
        <4>A. KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
          <5>1. bucket[q] = bucket'[q]
            BY Zenon
          <5>2. CASE bucket[q] = NULL
            BY <5>1, <5>2, Zenon DEF KeyInBktAtAddr
          <5> SUFFICES ASSUME bucket[q] # NULL
                        PROVE  KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <5>2
          <5>3. bucket[q] \in AllocAddrs
            BY NULLDef, Zenon
          <5>4. bucket[q] # addr
            BY <5>3
          <5>5. \A a \in Addrs : a # addr => MemLocs'[a] = MemLocs[a]
            BY Zenon
          <5>6. MemLocs'[bucket'[q]] = MemLocs[bucket[q]]
            BY <5>1, <5>4, <5>5
          <5> QED
            BY <5>6, Zenon DEF KeyInBktAtAddr
        <4>B. KeyInBktAtAddr(arg[q].key, bucket[q]) => (ValOfKeyInBktAtAddr(arg[q].key, bucket[q]) = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])')
          <5> SUFFICES ASSUME NEW bkt_arr,
                              bkt_arr = MemLocs[bucket[q]],
                              bucket[q] # NULL,
                              \E index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
                        PROVE  ValOfKeyInBktAtAddr(arg[q].key, bucket[q]) = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
            BY Zenon DEF KeyInBktAtAddr
          <5>1. bucket[q] = bucket'[q]
            BY Zenon
          <5>2. bucket[q] \in AllocAddrs
            BY NULLDef, Zenon
          <5>3. bucket[q] # addr
            BY <5>2
          <5>4. \A a \in Addrs : a # addr => MemLocs'[a] = MemLocs[a]
            BY Zenon
          <5>5. MemLocs'[bucket'[q]] = MemLocs[bucket[q]]
            BY <5>1, <5>3, <5>4 
          <5> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
          <5>6. ValOfKeyInBktAtAddr(arg[q].key, bucket[q]) = bkt_arr[idx].val
            BY Zenon DEF ValOfKeyInBktAtAddr
          <5>7. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = bkt_arr[idx].val
            BY Isa, <5>5 DEF ValOfKeyInBktAtAddr
          <5> QED
            BY <5>6, <5>7, Zenon
        <4>1. CASE pc[q] = RemainderID
          <5> USE <4>1
          <5> SUFFICES c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. pc'[q] = RemainderID
            BY RemDef, Zenon
          <5>2. c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>2. CASE pc[q] = "F1"
          <5> USE <4>2
          <5> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. pc'[q] = "F1"
            BY RemDef, Zenon
          <5>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2  
        <4>3. CASE pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>3
          <5> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            BY RemDef, Zenon
          <5>1. pc'[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <4>A, RemDef, Zenon DEF KeyInBktAtAddr
          <5>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <5>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5>3. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            BY <4>B, Zenon
          <5> QED
            BY <5>2, <5>3
        <4>4. CASE pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>4
          <5> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
            BY RemDef, Zenon
          <5>1. pc'[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <4>A, RemDef, Zenon DEF KeyInBktAtAddr
          <5>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
            BY <5>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>5. CASE pc[q] = "F3" 
          <5> USE <4>5
          <5> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY RemDef, Zenon
          <5>1. pc'[q] = "F3"
            BY RemDef, Zenon
          <5>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>6. CASE pc[q] \in {"I1", "I3", "I4"}
          <5> USE <4>6
          <5> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>2. pc'[q] \in {"I1", "I3", "I4"}
            BY RemDef, Zenon
          <5>3. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>2,  SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>3
        <4>7. CASE pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>7
          <5> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            BY RemDef, Zenon
          <5>1. pc'[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <4>A, RemDef, Zenon DEF KeyInBktAtAddr
          <5>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <5>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5>3. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            BY <4>B, Zenon
          <5> QED
            BY <5>2, <5>3
        <4>8. CASE pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>8
          <5> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. pc'[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <4>A, RemDef, Zenon DEF KeyInBktAtAddr
          <5>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>9. CASE pc[q] = "I5"
          <5> USE <4>9
          <5> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY RemDef, Zenon
          <5>1. pc'[q] = "I5"
            BY RemDef, Zenon
          <5>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>10. CASE pc[q] \in {"U1", "U2", "U3", "U4"}
          <5> USE <4>10
          <5> SUFFICES c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. pc'[q] \in {"U1", "U2", "U3", "U4"}
            BY RemDef, Zenon
          <5>2. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>11. CASE pc[q] = "U5" 
          <5> USE <4>11
          <5> SUFFICES c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY RemDef, Zenon
          <5>1. pc'[q] = "U5"
            BY RemDef, Zenon
          <5>2. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>12. CASE pc[q] \in {"R1", "R3", "R4"}
          <5> USE <4>12
          <5> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. pc'[q] \in {"R1", "R3", "R4"}
            BY RemDef, Zenon
          <5>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>13. CASE pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>13
          <5> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. pc'[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <4>A, RemDef, Zenon DEF KeyInBktAtAddr
          <5>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>14. CASE pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>14
          <5> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
            BY RemDef, Zenon
          <5>1. pc'[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <4>A, RemDef, Zenon DEF KeyInBktAtAddr
          <5>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
            BY <5>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>15. CASE pc[q] = "R5"
          <5> USE <4>15
          <5> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY RemDef, Zenon
          <5>1. pc'[q] = "R5"
            BY RemDef, Zenon
          <5>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4> QED
            BY RemDef, ZenonT(120),
                <4>1, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, 
                <4>10, <4>11, <4>12, <4>13, <4>14, <4>15
            DEF LineIDs
      <3> QED
        BY <3>1, <3>2, Zenon DEF S
    <2>3. CASE bucket[p] # NULL /\ r[p] # NULL
      <3> /\ pc[p] = "U3"
          /\ pc' = [pc EXCEPT ![p] = "U4"]
          /\ UNCHANGED <<A, bucket, r, arg, ret>>
        BY Zenon DEF U3
      <3>1. KeyInBktAtAddr(arg[p].key, bucket[p])
        BY <2>3 DEF BktInv
      <3>2. PICK i \in 1..Len(MemLocs[bucket[p]]) : MemLocs[bucket[p]][i].key = arg[p].key
        BY Zenon, <3>1 DEF KeyInBktAtAddr
      <3>3. i = CHOOSE index \in 1..Len(MemLocs[bucket[p]]) : MemLocs[bucket[p]][index].key = arg[p].key
        BY <3>2
      <3>4. i = IdxInBktAtAddr(arg[p].key, bucket[p])
        BY Zenon, <3>3 DEF IdxInBktAtAddr
      <3> PICK addr \in Addrs : 
                    /\ addr \notin AllocAddrs
                    /\ AllocAddrs' = AllocAddrs \cup {addr}
                    /\ newbkt' = [newbkt EXCEPT ![p] = addr]
                    /\ MemLocs' = [MemLocs EXCEPT ![addr] = [MemLocs[bucket[p]] EXCEPT ![i] = arg[p]]]
        BY <2>3, <3>4, Zenon DEF U3
      <3> /\ i \in 1..Len(MemLocs[bucket[p]]) 
          /\ MemLocs[bucket[p]][i].key = arg[p].key
        BY <3>2
      <3>5. c.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL]
        <4>1. c.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]])' THEN ValOfKeyInBktAtAddr(k, A[Hash[k]])' ELSE NULL]
          BY Zenon, SPrimeRewrite DEF SPrime
        <4>2. \A k \in KeyDomain : KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
          <5> SUFFICES ASSUME NEW k \in KeyDomain
                        PROVE  KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
            OBVIOUS
          <5>1. A'[Hash[k]] = A[Hash[k]]
            BY Zenon
          <5>2. CASE A[Hash[k]] = NULL
            BY <5>1, <5>2 DEF KeyInBktAtAddr
          <5> SUFFICES ASSUME A[Hash[k]] # NULL
                        PROVE  KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
            BY <5>2
          <5>3. A[Hash[k]] \in AllocAddrs
            BY HashDef, Zenon
          <5>4. A[Hash[k]] # addr
            BY NULLDef, <5>3
          <5>5. \A a \in Addrs : a # addr => MemLocs'[a] = MemLocs[a]
            BY Zenon
          <5>6. MemLocs'[A'[Hash[k]]] = MemLocs[A[Hash[k]]]
            BY <5>1, <5>4, <5>5
          <5> QED
            BY <5>6, Zenon DEF KeyInBktAtAddr
        <4>3. \A k \in KeyDomain : KeyInBktAtAddr(k, A[Hash[k]]) => (ValOfKeyInBktAtAddr(k, A[Hash[k]]) = ValOfKeyInBktAtAddr(k, A[Hash[k]])')
          <5> SUFFICES ASSUME NEW k \in KeyDomain,
                              NEW bkt_arr,
                              A[Hash[k]] # NULL,
                              bkt_arr = MemLocs[A[Hash[k]]],
                              \E index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
                        PROVE  ValOfKeyInBktAtAddr(k, A[Hash[k]]) = ValOfKeyInBktAtAddr(k, A[Hash[k]])'
            BY Zenon DEF KeyInBktAtAddr
          <5>1. A'[Hash[k]] = A[Hash[k]]
            BY Zenon
          <5>2. A[Hash[k]] \in AllocAddrs
            BY HashDef, Zenon
          <5>3. A[Hash[k]] # addr
            BY NULLDef, <5>2
          <5>4. \A a \in Addrs : a # addr => MemLocs'[a] = MemLocs[a]
            BY Zenon
          <5>5. MemLocs'[A'[Hash[k]]] = MemLocs[A[Hash[k]]]
            BY <5>1, <5>3, <5>4
          <5> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
          <5>6. ValOfKeyInBktAtAddr(k, A[Hash[k]]) = bkt_arr[idx].val
            BY Zenon DEF ValOfKeyInBktAtAddr
          <5>7. ValOfKeyInBktAtAddr(k, A[Hash[k]])' = bkt_arr[idx].val
            BY Isa, <5>5 DEF ValOfKeyInBktAtAddr
          <5> QED
            BY <5>6, <5>7, Zenon
        <4> QED
          BY <4>1, <4>2, <4>3, Zenon
      <3>6. ASSUME NEW q \in ProcSet
              PROVE
                  CASE pc[q] = RemainderID 
                      -> (c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT)
                    [] pc[q] = "F1"
                      -> (c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                    [] pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                      -> (c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q]))
                    [] pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                      -> (c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL)
                    [] pc[q] = "F3"
                      -> (c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q])
                    [] pc[q] \in {"I1", "I3", "I4"}
                      -> (c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                    [] pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                      -> (c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q]))
                    [] pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                      -> (c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                    [] pc[q] = "I5"
                      -> (c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q])
                    [] pc[q] \in {"U1", "U2", "U3", "U4"}
                      -> (c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                    [] pc[q] = "U5"
                      -> (c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q])
                    [] pc[q] \in {"R1", "R3", "R4"}
                      -> (c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                    [] pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                      -> (c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                    [] pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                      -> (c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL)
                    [] pc[q] = "R5"
                      -> (c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q])
        <4> USE <3>6
        <4>A. KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
          <5>1. bucket[q] = bucket'[q]
            BY Zenon
          <5>2. CASE bucket[q] = NULL
            BY <5>1, <5>2, Zenon DEF KeyInBktAtAddr
          <5> SUFFICES ASSUME bucket[q] # NULL
                        PROVE  KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <5>2
          <5>3. bucket[q] \in AllocAddrs
            BY NULLDef, Zenon
          <5>4. bucket[q] # addr
            BY <5>3
          <5>5. \A a \in Addrs : a # addr => MemLocs'[a] = MemLocs[a]
            BY Zenon
          <5>6. MemLocs'[bucket'[q]] = MemLocs[bucket[q]]
            BY <5>1, <5>4, <5>5
          <5> QED
            BY <5>6, Zenon DEF KeyInBktAtAddr
        <4>B. KeyInBktAtAddr(arg[q].key, bucket[q]) => (ValOfKeyInBktAtAddr(arg[q].key, bucket[q]) = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])')
          <5> SUFFICES ASSUME NEW bkt_arr,
                              bkt_arr = MemLocs[bucket[q]],
                              bucket[q] # NULL,
                              \E index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
                        PROVE  ValOfKeyInBktAtAddr(arg[q].key, bucket[q]) = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
            BY Zenon DEF KeyInBktAtAddr
          <5>1. bucket[q] = bucket'[q]
            BY Zenon
          <5>2. bucket[q] \in AllocAddrs
            BY NULLDef, Zenon
          <5>3. bucket[q] # addr
            BY <5>2
          <5>4. \A a \in Addrs : a # addr => MemLocs'[a] = MemLocs[a]
            BY Zenon
          <5>5. MemLocs'[bucket'[q]] = MemLocs[bucket[q]]
            BY <5>1, <5>3, <5>4 
          <5> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
          <5>6. ValOfKeyInBktAtAddr(arg[q].key, bucket[q]) = bkt_arr[idx].val
            BY Zenon DEF ValOfKeyInBktAtAddr
          <5>7. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = bkt_arr[idx].val
            BY Isa, <5>5 DEF ValOfKeyInBktAtAddr
          <5> QED
            BY <5>6, <5>7, Zenon
        <4>1. CASE pc[q] = RemainderID
          <5> USE <4>1
          <5> SUFFICES c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. pc'[q] = RemainderID
            BY RemDef, Zenon
          <5>2. c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>2. CASE pc[q] = "F1"
          <5> USE <4>2
          <5> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. pc'[q] = "F1"
            BY RemDef, Zenon
          <5>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2  
        <4>3. CASE pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>3
          <5> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            BY RemDef, Zenon
          <5>1. pc'[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <4>A, RemDef, Zenon DEF KeyInBktAtAddr
          <5>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <5>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5>3. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            BY <4>B, Zenon
          <5> QED
            BY <5>2, <5>3
        <4>4. CASE pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>4
          <5> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
            BY RemDef, Zenon
          <5>1. pc'[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <4>A, RemDef, Zenon DEF KeyInBktAtAddr
          <5>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
            BY <5>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>5. CASE pc[q] = "F3" 
          <5> USE <4>5
          <5> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY RemDef, Zenon
          <5>1. pc'[q] = "F3"
            BY RemDef, Zenon
          <5>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>6. CASE pc[q] \in {"I1", "I3", "I4"}
          <5> USE <4>6
          <5> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>2. pc'[q] \in {"I1", "I3", "I4"}
            BY RemDef, Zenon
          <5>3. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>2,  SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>3
        <4>7. CASE pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>7
          <5> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            BY RemDef, Zenon
          <5>1. pc'[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <4>A, RemDef, Zenon DEF KeyInBktAtAddr
          <5>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <5>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5>3. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            BY <4>B, Zenon
          <5> QED
            BY <5>2, <5>3
        <4>8. CASE pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>8
          <5> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. pc'[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <4>A, RemDef, Zenon DEF KeyInBktAtAddr
          <5>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>9. CASE pc[q] = "I5"
          <5> USE <4>9
          <5> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY RemDef, Zenon
          <5>1. pc'[q] = "I5"
            BY RemDef, Zenon
          <5>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>10. CASE pc[q] \in {"U1", "U2", "U3", "U4"}
          <5> USE <4>10
          <5> SUFFICES c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. pc'[q] \in {"U1", "U2", "U3", "U4"}
            BY RemDef, Zenon
          <5>2. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>11. CASE pc[q] = "U5" 
          <5> USE <4>11
          <5> SUFFICES c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY RemDef, Zenon
          <5>1. pc'[q] = "U5"
            BY RemDef, Zenon
          <5>2. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>12. CASE pc[q] \in {"R1", "R3", "R4"}
          <5> USE <4>12
          <5> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. pc'[q] \in {"R1", "R3", "R4"}
            BY RemDef, Zenon
          <5>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>13. CASE pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>13
          <5> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. pc'[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <4>A, RemDef, Zenon DEF KeyInBktAtAddr
          <5>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>14. CASE pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>14
          <5> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
            BY RemDef, Zenon
          <5>1. pc'[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <4>A, RemDef, Zenon DEF KeyInBktAtAddr
          <5>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
            BY <5>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>15. CASE pc[q] = "R5"
          <5> USE <4>15
          <5> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY RemDef, Zenon
          <5>1. pc'[q] = "R5"
            BY RemDef, Zenon
          <5>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4> QED
            BY RemDef, ZenonT(120),
                <4>1, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, 
                <4>10, <4>11, <4>12, <4>13, <4>14, <4>15
            DEF LineIDs
      <3> QED
        BY <3>5, <3>6, Zenon DEF S
    <2> QED
      BY <2>1, <2>2, <2>3
  <1>10. CASE LineAction = U4(p)
    <2> USE <1>10 DEF U4, TypeOK, Inv
    <2> SUFFICES ASSUME NEW c \in ConfigDomain,
                        c \in S'
                 PROVE  c \in Evolve(S)
      BY Zenon DEF S
    <2>1. CASE A[Hash[arg[p].key]] = bucket[p]
      <3> USE <2>1
      <3> c_pred == [state |-> [c.state EXCEPT ![arg[p].key] = 
                                IF KeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]]) THEN ValOfKeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]]) ELSE NULL],
                     op    |-> c.op,
                     arg   |-> c.arg,
                     res   |-> [c.res EXCEPT ![p] = BOT]]
      <3>1. c_pred \in ConfigDomain
        <4>1. c_pred.state \in StateDomain
          <5>1. arg[p].key \in KeyDomain
            BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
          <5>2. CASE ~KeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]])
            BY <5>1, <5>2 DEF StateDomain, ConfigDomain
          <5> SUFFICES ASSUME KeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]])
                        PROVE  ValOfKeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]]) \in ValDomain
            BY <5>1, <5>2 DEF StateDomain, ConfigDomain
          <5>3. PICK idx \in 1..Len(MemLocs[A[Hash[arg[p].key]]]) : MemLocs[A[Hash[arg[p].key]]][idx].key = arg[p].key
            BY Zenon DEF KeyInBktAtAddr
          <5>4. idx = CHOOSE index \in 1..Len(MemLocs[A[Hash[arg[p].key]]]) : MemLocs[A[Hash[arg[p].key]]][index].key = arg[p].key
            BY <5>3
          <5>5. ValOfKeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]]) = MemLocs[A[Hash[arg[p].key]]][idx].val
            BY Zenon, <5>4 DEF ValOfKeyInBktAtAddr
          <5>6. A[Hash[arg[p].key]] # NULL
            BY Zenon DEF KeyInBktAtAddr
          <5>7. MemLocs[A[Hash[arg[p].key]]] \in Seq([key: KeyDomain, val: ValDomain])
            BY Zenon, HashDef, NULLDef, <5>6
          <5>8. MemLocs[A[Hash[arg[p].key]]][idx] \in [key: KeyDomain, val: ValDomain]
            BY Zenon, <5>3, <5>7, ElementOfSeq
          <5>9. MemLocs[A[Hash[arg[p].key]]][idx].val \in ValDomain
            BY <5>8
          <5> QED
            BY <5>5, <5>9
        <4>2. c_pred.op \in [ProcSet -> OpDomain]
          BY DEF ConfigDomain
        <4>3. c_pred.arg \in [ProcSet -> ArgDomain]
          BY DEF ConfigDomain
        <4>4. c_pred.res \in [ProcSet -> ResDomain]
          BY DEF ConfigDomain, ResDomain
        <4> QED
          BY <4>1, <4>2, <4>3, <4>4 DEF ConfigDomain
      <3>2. c_pred \in S
        <4>1. c_pred.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL]
          <5> SUFFICES ASSUME NEW k \in KeyDomain
                        PROVE  c_pred.state[k] = IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL
            BY Zenon, <3>1 DEF StateDomain, ConfigDomain
          <5>1. CASE k = arg[p].key
            <6>1. arg[p].key \in KeyDomain
              BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
            <6> QED
              BY <5>1, <6>1, Zenon DEF StateDomain, ConfigDomain
          <5>2. CASE k # arg[p].key /\ Hash[k] # Hash[arg[p].key]
            <6> USE <5>2
            <6>1. c.state = [key \in KeyDomain |-> IF KeyInBktAtAddr(key, A[Hash[key]])' THEN ValOfKeyInBktAtAddr(key, A[Hash[key]])' ELSE NULL]
              BY SPrimeRewrite, Zenon DEF SPrime
            <6>2. A'[Hash[k]] = A[Hash[k]]
              BY HashDef, Zenon
            <6>3. KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
              BY <6>2, Zenon DEF KeyInBktAtAddr
            <6>4. ValOfKeyInBktAtAddr(k, A[Hash[k]]) = ValOfKeyInBktAtAddr(k, A[Hash[k]])'
              <7> DEFINE bkt_arr == MemLocs'[A'[Hash[k]]]
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
              <7>1. ValOfKeyInBktAtAddr(k, A[Hash[k]])' = bkt_arr[idx].val
                BY Zenon DEF ValOfKeyInBktAtAddr
              <7>2. bkt_arr = MemLocs[A[Hash[k]]]
                BY Zenon, <6>2
              <7>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
                BY Zenon
              <7>4. ValOfKeyInBktAtAddr(k, A[Hash[k]]) = MemLocs[A[Hash[k]]][CHOOSE index \in 1..Len(MemLocs[A[Hash[k]]]) : MemLocs[A[Hash[k]]][index].key = k].val
                BY Zenon DEF ValOfKeyInBktAtAddr
              <7>5. ValOfKeyInBktAtAddr(k, A[Hash[k]]) = bkt_arr[idx].val
                BY ZenonT(90), <7>2, <7>3, <7>4
              <7> QED
                BY Zenon, <7>1, <7>5
            <6> QED
              BY <6>1, <6>3, <6>4
          <5>3. CASE k # arg[p].key /\ Hash[k] = Hash[arg[p].key]
            <6> USE <5>3
            <6>1. c.state = [key \in KeyDomain |-> IF KeyInBktAtAddr(key, A[Hash[key]])' 
                                                      THEN ValOfKeyInBktAtAddr(key, A[Hash[key]])' 
                                                      ELSE NULL]
              BY SPrimeRewrite, Zenon DEF SPrime
            <6>2. c_pred.state[k] = IF KeyInBktAtAddr(k, A[Hash[k]])' 
                                        THEN ValOfKeyInBktAtAddr(k, A[Hash[k]])' 
                                        ELSE NULL
              BY <6>1
            <6>3. MemLocs' = MemLocs
              BY Zenon
            <6>4. bucket[p] = A[Hash[k]]
              BY Zenon
            <6>5. arg[p].key \in KeyDomain
              BY RemDef, Zenon DEF ArgsOf, LineIDtoOp
            <6>6. newbkt[p] = A'[Hash[k]]
              BY Zenon, <6>5, HashDef
            <6>7. KeyInBktAtAddr(k, A[Hash[k]])' = KeyInBktAtAddr(k, newbkt[p])
              BY <6>6, Zenon DEF KeyInBktAtAddr
            <6>8. ValOfKeyInBktAtAddr(k, A[Hash[k]])' = ValOfKeyInBktAtAddr(k, newbkt[p])
              BY <6>6, Zenon DEF ValOfKeyInBktAtAddr
            <6>9. c_pred.state[k] = IF KeyInBktAtAddr(k, newbkt[p]) THEN ValOfKeyInBktAtAddr(k, newbkt[p]) ELSE NULL
              BY <6>2, <6>7, <6>8, Zenon
            <6>10. /\ KeyInBktAtAddr(k, bucket[p]) = KeyInBktAtAddr(k, newbkt[p])
                   /\ KeyInBktAtAddr(k, bucket[p]) => (ValOfKeyInBktAtAddr(k, bucket[p]) = ValOfKeyInBktAtAddr(k, newbkt[p]))
              BY Zenon DEF NewBktInv
            <6>11. c_pred.state[k] = IF KeyInBktAtAddr(k, bucket[p]) THEN ValOfKeyInBktAtAddr(k, bucket[p]) ELSE NULL
              BY <6>9, <6>10, Zenon
            <6>12. c_pred.state[k] = IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL
              BY <6>11, <6>6, Zenon
            <6> QED
              BY <6>12, Zenon
          <5> QED
            BY <5>1, <5>2, <5>3
        <4>2. ASSUME NEW q \in ProcSet
              PROVE
                CASE pc[q] = RemainderID 
                    -> (c_pred.op[q] = BOT /\ c_pred.arg[q] = BOT /\ c_pred.res[q] = BOT)
                  [] pc[q] = "F1"
                    -> (c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q]))
                  [] pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = NULL)
                  [] pc[q] = "F3"
                    -> (c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q])
                  [] pc[q] \in {"I1", "I3", "I4"}
                    -> (c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q]))
                  [] pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "I5"
                    -> (c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q])
                  [] pc[q] \in {"U1", "U2", "U3", "U4"}
                    -> (c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "U5"
                    -> (c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q])
                  [] pc[q] \in {"R1", "R3", "R4"}
                    -> (c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = NULL)
                  [] pc[q] = "R5"
                    -> (c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q])
          <5> USE <4>2
          <5>1. CASE pc[q] = RemainderID
            <6> USE <5>1
            <6> SUFFICES c_pred.op[q] = BOT /\ c_pred.arg[q] = BOT /\ c_pred.res[q] = BOT
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] = RemainderID
              BY RemDef, Zenon
            <6>4. c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4
          <5>2. CASE pc[q] = "F1"
            <6> USE <5>2
            <6> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] = "F1"
              BY RemDef, Zenon
            <6>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4
          <5>3. CASE pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
            <6> USE <5>3
            <6> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
              BY RemDef, Zenon DEF KeyInBktAtAddr
            <6>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
              <7> DEFINE bkt_arr == MemLocs'[bucket'[q]]
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg'[q].key
              <7>1. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = bkt_arr[idx].val
                BY Zenon DEF ValOfKeyInBktAtAddr
              <7>2. bkt_arr = MemLocs[bucket[q]]
                BY Zenon
              <7>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
                BY Zenon
              <7> QED
                BY <7>1, <7>2, <7>3, Isa DEF ValOfKeyInBktAtAddr
            <6> QED
              BY <6>2, <6>4, <6>5
          <5>4. CASE pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
            <6> USE <5>4
            <6> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = NULL
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
              BY RemDef, Zenon DEF KeyInBktAtAddr
            <6>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4
          <5>5. CASE pc[q] = "F3"
            <6> USE <5>5
            <6> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] = "F3"
              BY RemDef, Zenon
            <6>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4 
          <5>6. CASE pc[q] \in {"I1", "I3", "I4"}
            <6> USE <5>6
            <6> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
              BY RemDef, Zenon
            <6>A. CASE p = q
              <7> USE <6>A
              <7>1. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = BOT
                BY <3>1 DEF ConfigDomain
              <7>2. pc'[q] = "I5"
                BY Zenon
              <7>3. c.op[q] = "Insert" /\ c.arg[p] = arg[q]
                BY <7>2, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>1, <7>3
            <6> SUFFICES ASSUME p # q
                          PROVE  c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
              BY <6>A
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              OBVIOUS
            <6>3. pc'[q] \in {"I1", "I3", "I4"}
              BY RemDef, Zenon
            <6>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4
          <5>7. CASE pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
            <6> USE <5>7
            <6> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
              BY RemDef, Zenon DEF KeyInBktAtAddr
            <6>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
              <7> DEFINE bkt_arr == MemLocs'[bucket'[q]]
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg'[q].key
              <7>1. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = bkt_arr[idx].val
                BY Zenon DEF ValOfKeyInBktAtAddr
              <7>2. bkt_arr = MemLocs[bucket[q]]
                BY Zenon
              <7>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
                BY Zenon
              <7> QED
                BY <7>1, <7>2, <7>3, Isa DEF ValOfKeyInBktAtAddr
            <6> QED
              BY <6>2, <6>4, <6>5
          <5>8. CASE pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
            <6> USE <5>8
            <6> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
              BY RemDef, Zenon DEF KeyInBktAtAddr
            <6>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4
          <5>9. CASE pc[q] = "I5"
            <6> USE <5>9
            <6> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] = "I5"
              BY RemDef, Zenon
            <6>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4
          <5>10. CASE pc[q] \in {"U1", "U2", "U3", "U4"}
            <6> USE <5>10
            <6> SUFFICES c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
              BY RemDef, Zenon
            <6>1. CASE q = p
              <7> USE <6>1
              <7>1. pc'[q] = "U5"
                BY Zenon
              <7>2. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r'[q]
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7>3. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = BOT
                BY DEF ConfigDomain 
              <7> QED
                BY <7>2, <7>3
            <6> SUFFICES ASSUME q # p
                          PROVE  c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
              BY <6>1
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              OBVIOUS
            <6>3. pc'[q] \in {"U1", "U2", "U3", "U4"}
              BY RemDef, Zenon
            <6>4. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4
          <5>11. CASE pc[q] = "U5" 
            <6> USE <5>11
            <6> SUFFICES c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] = "U5"
              BY RemDef, Zenon
            <6>4. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4
          <5>12. CASE pc[q] \in {"R1", "R3", "R4"}
            <6> USE <5>12
            <6> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] \in {"R1", "R3", "R4"}
              BY RemDef, Zenon
            <6>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4
          <5>13. CASE pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q]) 
            <6> USE <5>13
            <6> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
              BY RemDef, Zenon DEF KeyInBktAtAddr
            <6>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4              
          <5>14. CASE pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
            <6> USE <5>14
            <6> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = NULL
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
              BY RemDef, Zenon DEF KeyInBktAtAddr
            <6>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4    
          <5>15. CASE pc[q] = "R5"
            <6> USE <5>15
            <6> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] = "R5"
              BY RemDef, Zenon
            <6>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4
          <5> QED
              BY RemDef, ZenonT(120),
                  <5>1, <5>2, <5>3, <5>4, <5>5, <5>6, <5>7, <5>8, <5>9, 
                  <5>10, <5>11, <5>12, <5>13, <5>14, <5>15
              DEF LineIDs 
        <4> QED
          BY <3>1, <4>1, <4>2, Zenon DEF S
      <3>3. Delta(c_pred, p, c)
        <4>1. c_pred.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL]
          BY <3>1, <3>2, Zenon DEF S
        <4>2. c_pred.op[p] = "Upsert" /\ c_pred.arg[p] = arg[p] /\ c_pred.res[p] = BOT
          BY <3>1, <3>2, Zenon, RemDef DEF S
        <4>3. arg[p] \in ArgsOf("Upsert") /\ arg[p].key \in KeyDomain
          BY RemDef, Zenon DEF ArgsOf, LineIDtoOp 
        <4> SUFFICES /\ c.state = [c_pred.state EXCEPT ![arg[p].key] = arg[p].val]
                      /\ c.res = [c_pred.res EXCEPT ![p] = c_pred.state[arg[p].key]]
          BY <4>2, <4>3, Zenon DEF Delta
        <4> SUFFICES /\ c.state[arg[p].key] = arg[p].val
                      /\ c.res[p] = IF KeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]]) 
                                      THEN ValOfKeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]]) 
                                      ELSE NULL
          BY <3>2, <4>3, ZenonT(60) DEF ConfigDomain, StateDomain
        <4>4. c.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]])' THEN ValOfKeyInBktAtAddr(k, A[Hash[k]])' ELSE NULL]
          BY SPrimeRewrite, Zenon DEF SPrime
        <4>5. c.state[arg[p].key] = IF KeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]])' THEN ValOfKeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]])' ELSE NULL
          BY <4>4, <4>3, Zenon
        <4>6. newbkt[p] = A'[Hash[arg[p].key]]
          BY Zenon, HashDef, <4>3
        <4>7. MemLocs[A'[Hash[arg[p].key]]] = MemLocs[newbkt[p]]
          BY Zenon, <4>6
        <4>8. KeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]])' = KeyInBktAtAddr(arg[p].key, newbkt[p])
          BY Zenon, <4>6 DEF KeyInBktAtAddr
        <4>9. ValOfKeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]])' = 
          MemLocs[A'[Hash[arg[p].key]]][CHOOSE index \in 1..Len(MemLocs[A'[Hash[arg[p].key]]]) : MemLocs[A'[Hash[arg[p].key]]][index].key = arg[p].key].val
          BY Zenon DEF ValOfKeyInBktAtAddr
        <4>10. ValOfKeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]])' = 
          MemLocs[newbkt[p]][CHOOSE index \in 1..Len(MemLocs[newbkt[p]]) : MemLocs[newbkt[p]][index].key = arg[p].key].val
          BY <4>9, <4>7
        <4>11. ValOfKeyInBktAtAddr(arg[p].key, newbkt[p]) = 
          MemLocs[newbkt[p]][CHOOSE index \in 1..Len(MemLocs[newbkt[p]]) : MemLocs[newbkt[p]][index].key = arg[p].key].val
          BY Zenon DEF ValOfKeyInBktAtAddr
        <4>12. ValOfKeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]])' = ValOfKeyInBktAtAddr(arg[p].key, newbkt[p])
          BY <4>10, <4>11, Zenon
        <4>13. c.state[arg[p].key] = IF KeyInBktAtAddr(arg[p].key, newbkt[p]) THEN ValOfKeyInBktAtAddr(arg[p].key, newbkt[p]) ELSE NULL
          BY <4>5, <4>8, <4>12, Zenon
        <4>14. c.state[arg[p].key] = arg[p].val
          BY <4>13, Zenon DEF NewBktInv
        <4>15. pc'[p] = "U5"
          BY Zenon
        <4>16. c.res[p] = r'[p]
          BY <4>15, SPrimeRewrite, RemDef, Zenon DEF SPrime
        <4>17. c.res[p] = IF KeyInBktAtAddr(arg[p].key, bucket[p]) THEN ValOfKeyInBktAtAddr(arg[p].key, bucket[p]) ELSE NULL
          BY <4>16, Zenon DEF BktInv
        <4>18. c.res[p] = IF KeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]]) THEN ValOfKeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]]) ELSE NULL
          BY <4>17, Zenon
        <4> QED
          BY <4>18, <4>14
      <3> QED
        BY <3>1, <3>2, <3>3, SingleDeltaEvolve
    <2>2. CASE A[Hash[arg[p].key]] # bucket[p]
      <3> USE <2>2
      <3> SUFFICES c \in S
        BY EmptySeqEvolve
      <3>1. c.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL]
        <4>1. c.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]])' THEN ValOfKeyInBktAtAddr(k, A[Hash[k]])' ELSE NULL]
          BY Zenon, SPrimeRewrite DEF SPrime
        <4>2. \A k \in KeyDomain : KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
          BY Zenon DEF KeyInBktAtAddr
        <4>3. \A k \in KeyDomain : ValOfKeyInBktAtAddr(k, A[Hash[k]])' = ValOfKeyInBktAtAddr(k, A[Hash[k]])
          <5> SUFFICES ASSUME NEW k \in KeyDomain
                        PROVE  ValOfKeyInBktAtAddr(k, A[Hash[k]])' = ValOfKeyInBktAtAddr(k, A[Hash[k]])
            OBVIOUS
          <5> bkt_arr == MemLocs'[A'[Hash[k]]]
          <5> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
          <5>1. ValOfKeyInBktAtAddr(k, A[Hash[k]])' = bkt_arr[idx].val
            BY DEF ValOfKeyInBktAtAddr
          <5>2. bkt_arr = MemLocs[A[Hash[k]]]
            BY Zenon
          <5> QED
            BY <5>1, <5>2, ZenonT(30) DEF ValOfKeyInBktAtAddr
        <4> QED
          BY <4>1, <4>2, <4>3
      <3>2. ASSUME NEW q \in ProcSet
            PROVE
                CASE pc[q] = RemainderID 
                    -> (c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT)
                  [] pc[q] = "F1"
                    -> (c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                  [] pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q]))
                  [] pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL)
                  [] pc[q] = "F3"
                    -> (c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q])
                  [] pc[q] \in {"I1", "I3", "I4"}
                    -> (c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                  [] pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q]))
                  [] pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                  [] pc[q] = "I5"
                    -> (c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q])
                  [] pc[q] \in {"U1", "U2", "U3", "U4"}
                    -> (c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                  [] pc[q] = "U5"
                    -> (c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q])
                  [] pc[q] \in {"R1", "R3", "R4"}
                    -> (c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                  [] pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                  [] pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL)
                  [] pc[q] = "R5"
                    -> (c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q])
        <4> USE <3>2
        <4>A. \A k \in KeyDomain : KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, bucket[q])'
          BY Zenon DEF KeyInBktAtAddr
        <4>B. \A k \in KeyDomain : ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, bucket[q])
          <5> SUFFICES ASSUME NEW k \in KeyDomain
                        PROVE  ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, bucket[q])
            OBVIOUS
          <5> bkt_arr == MemLocs'[bucket'[q]]
          <5> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
          <5>1. ValOfKeyInBktAtAddr(k, bucket[q])' = bkt_arr[idx].val
            BY DEF ValOfKeyInBktAtAddr
          <5>2. bkt_arr = MemLocs[bucket[q]]
            BY Zenon
          <5> QED
            BY <5>1, <5>2, ZenonT(30) DEF ValOfKeyInBktAtAddr
        <4>1. CASE pc[q] = RemainderID
          <5> USE <4>1
          <5> SUFFICES c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. pc'[q] = RemainderID
            BY RemDef, Zenon
          <5>2. c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>2. CASE pc[q] = "F1"
          <5> USE <4>2
          <5> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. pc'[q] = "F1"
            BY RemDef, Zenon
          <5>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>3. CASE pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>3
          <5> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            BY RemDef, Zenon
          <5>1. pc'[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <5>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5>3. arg[q].key = arg'[q].key /\ arg[q].key \in KeyDomain
            BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
          <5>4. c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            BY <5>2, <5>3, <4>B
          <5> QED
            BY <5>2, <5>4
        <4>4. CASE pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>4
          <5> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
            BY RemDef, Zenon
          <5>2. pc'[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>3. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
            BY <5>2,  SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>3
        <4>5. CASE pc[q] = "F3"
          <5> USE <4>5
          <5> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY RemDef, Zenon
          <5>1. pc'[q] = "F3"
            BY RemDef, Zenon
          <5>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2 
        <4>6. CASE pc[q] \in {"I1", "I3", "I4"}
          <5> USE <4>6
          <5> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. pc'[q] \in {"I1", "I3", "I4"}
            BY RemDef, Zenon
          <5>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2 
        <4>7. CASE pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>7
          <5> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            BY RemDef, Zenon
          <5>1. CASE p = q
            <6> USE <5>1
            <6>1. c.op[p] = "Insert" /\ c.arg[p] = arg[p] /\ c.res[p] = r'[p]
              BY SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6>2. r'[p] = ValOfKeyInBktAtAddr(arg[p].key, bucket[p])
              BY Zenon
            <6> QED
              BY <6>1, <6>2
          <5> SUFFICES ASSUME p # q
                        PROVE  c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            BY <5>1
          <5>2. pc'[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>3. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <5>2,  SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5>4. arg[q].key = arg'[q].key /\ arg[q].key \in KeyDomain
            BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
          <5>5. c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            BY <5>3, <5>4, <4>B
          <5> QED
            BY <5>3, <5>5
        <4>8. CASE pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>8
          <5> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. CASE p = q
            <6> USE <5>1
            <6>1. c.op[p] = "Insert" /\ c.arg[p] = arg[p] /\ c.res[p] = BOT
              BY SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>1
          <5> SUFFICES ASSUME p # q
                        PROVE  c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>1
          <5>2. pc'[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>3. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>2, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>3 
        <4>9. CASE pc[q] = "I5"
          <5> USE <4>9
          <5> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY RemDef, Zenon
          <5>1. pc'[q] = "I5"
            BY RemDef, Zenon 
          <5>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2 
        <4>10. CASE pc[q] \in {"U1", "U2", "U3", "U4"}
          <5> USE <4>10
          <5> SUFFICES c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. pc'[q] \in {"U1", "U2", "U3", "U4"}
            BY RemDef, Zenon
          <5>2. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>11. CASE pc[q] = "U5" 
          <5> USE <4>11
          <5> SUFFICES c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY RemDef, Zenon
          <5>1. pc'[q] = "U5"
            BY RemDef, Zenon
          <5>2. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>12. CASE pc[q] \in {"R1", "R3", "R4"}
          <5> USE <4>12
          <5> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. pc'[q] \in {"R1", "R3", "R4"}
            BY RemDef, Zenon
          <5>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>13. CASE pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>13
          <5> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. pc'[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>14. CASE pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>14
          <5> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
            BY RemDef, Zenon
          <5>1. pc'[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>15. CASE pc[q] = "R5"
          <5> USE <4>15
          <5> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY RemDef, Zenon
          <5>1. pc'[q] = "R5" 
            BY RemDef, Zenon
          <5>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4> QED
            BY RemDef, ZenonT(120),
                <4>1, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, 
                <4>10, <4>11, <4>12, <4>13, <4>14, <4>15
            DEF LineIDs
      <3> QED
        BY <3>1, <3>2, Zenon DEF S
    <2> QED
      BY <2>1, <2>2
  <1>11. CASE LineAction = R1(p)
    <2> USE <1>11 DEF R1, TypeOK, Inv
    <2> SUFFICES ASSUME NEW c \in ConfigDomain,
                        c \in S'
                 PROVE  c \in Evolve(S)
      BY Zenon DEF S
    <2>1. CASE ~KeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]])
      <3> USE <2>1
      <3> c_pred == [state |-> c.state,
                     op    |-> c.op,
                     arg   |-> c.arg,
                     res   |-> [c.res EXCEPT ![p] = BOT]]
      <3>1. c_pred \in ConfigDomain
        <4>1. c_pred.state \in StateDomain
          BY DEF ConfigDomain
        <4>2. c_pred.op \in [ProcSet -> OpDomain]
          BY DEF ConfigDomain
        <4>3. c_pred.arg \in [ProcSet -> ArgDomain]
          BY DEF ConfigDomain
        <4>4. c_pred.res \in [ProcSet -> ResDomain]
          BY DEF ConfigDomain, ResDomain
        <4> QED
          BY <4>1, <4>2, <4>3, <4>4 DEF ConfigDomain
      <3>2. c_pred \in S
        <4>1. c_pred.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL]
          <5>1. c_pred.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]])'
                                                        THEN ValOfKeyInBktAtAddr(k, A[Hash[k]])'
                                                        ELSE NULL]
            BY SPrimeRewrite, Zenon DEF SPrime
          <5>2. \A k \in KeyDomain : /\ KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
                                     /\ ValOfKeyInBktAtAddr(k, A[Hash[k]]) = ValOfKeyInBktAtAddr(k, A[Hash[k]])'
            <6> SUFFICES ASSUME NEW k \in KeyDomain
                          PROVE  /\ KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
                                 /\ ValOfKeyInBktAtAddr(k, A[Hash[k]]) = ValOfKeyInBktAtAddr(k, A[Hash[k]])'
              OBVIOUS
            <6>1. KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
              BY Zenon DEF KeyInBktAtAddr
            <6>2. ValOfKeyInBktAtAddr(k, A[Hash[k]]) = ValOfKeyInBktAtAddr(k, A[Hash[k]])'
              <7> DEFINE bkt_arr == MemLocs'[A'[Hash[k]]]
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
              <7>1. ValOfKeyInBktAtAddr(k, A[Hash[k]])' = bkt_arr[idx].val
                BY Zenon DEF ValOfKeyInBktAtAddr
              <7>2. bkt_arr = MemLocs[A[Hash[k]]]
                BY Zenon
              <7>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
                BY Zenon
              <7> QED
                BY <7>1, <7>2, <7>3, Isa DEF ValOfKeyInBktAtAddr
            <6>3. QED
              BY <6>1, <6>2
          <5> QED
            BY <5>1, <5>2 
        <4>2. ASSUME NEW q \in ProcSet
              PROVE
                CASE pc[q] = RemainderID 
                    -> (c_pred.op[q] = BOT /\ c_pred.arg[q] = BOT /\ c_pred.res[q] = BOT)
                  [] pc[q] = "F1"
                    -> (c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q]))
                  [] pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = NULL)
                  [] pc[q] = "F3"
                    -> (c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q])
                  [] pc[q] \in {"I1", "I3", "I4"}
                    -> (c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q]))
                  [] pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "I5"
                    -> (c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q])
                  [] pc[q] \in {"U1", "U2", "U3", "U4"}
                    -> (c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "U5"
                    -> (c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q])
                  [] pc[q] \in {"R1", "R3", "R4"}
                    -> (c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = NULL)
                  [] pc[q] = "R5"
                    -> (c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q])
          <5> USE <4>2
          <5>1. CASE pc[q] = RemainderID
            <6> USE <5>1
            <6> SUFFICES c_pred.op[q] = BOT /\ c_pred.arg[q] = BOT /\ c_pred.res[q] = BOT
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] = RemainderID
              BY RemDef, Zenon
            <6>4. c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4
          <5>2. CASE pc[q] = "F1"
            <6> USE <5>2
            <6> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] = "F1"
              BY RemDef, Zenon
            <6>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4
          <5>3. CASE pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
            <6> USE <5>3
            <6> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
              BY RemDef, Zenon DEF KeyInBktAtAddr
            <6>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
              <7> DEFINE bkt_arr == MemLocs'[bucket'[q]]
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg'[q].key
              <7>1. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = bkt_arr[idx].val
                BY Zenon DEF ValOfKeyInBktAtAddr
              <7>2. bkt_arr = MemLocs[bucket[q]]
                BY Zenon
              <7>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
                BY Zenon
              <7> QED
                BY <7>1, <7>2, <7>3, Isa DEF ValOfKeyInBktAtAddr
            <6> QED
              BY <6>2, <6>4, <6>5
          <5>4. CASE pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
            <6> USE <5>4
            <6> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = NULL
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
              BY RemDef, Zenon DEF KeyInBktAtAddr
            <6>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4
          <5>5. CASE pc[q] = "F3" 
            <6> USE <5>5
            <6> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] = "F3"
              BY RemDef, Zenon
            <6>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4
          <5>6. CASE pc[q] \in {"I1", "I3", "I4"}
            <6> USE <5>6
            <6> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] \in {"I1", "I3", "I4"}
              BY RemDef, Zenon
            <6>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4
          <5>7. CASE pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
            <6> USE <5>7
            <6> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
              BY RemDef, Zenon DEF KeyInBktAtAddr
            <6>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
              <7> DEFINE bkt_arr == MemLocs'[bucket'[q]]
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg'[q].key
              <7>1. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = bkt_arr[idx].val
                BY Zenon DEF ValOfKeyInBktAtAddr
              <7>2. bkt_arr = MemLocs[bucket[q]]
                BY Zenon
              <7>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
                BY Zenon
              <7> QED
                BY <7>1, <7>2, <7>3, Isa DEF ValOfKeyInBktAtAddr
            <6> QED
              BY <6>2, <6>4, <6>5
          <5>8. CASE pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
            <6> USE <5>8
            <6> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
              BY RemDef, Zenon DEF KeyInBktAtAddr
            <6>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4
          <5>9. CASE pc[q] = "I5"
            <6> USE <5>9
            <6> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] = "I5"
              BY RemDef, Zenon
            <6>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4
          <5>10. CASE pc[q] \in {"U1", "U2", "U3", "U4"}
            <6> USE <5>10
            <6> SUFFICES c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] \in {"U1", "U2", "U3", "U4"}
              BY RemDef, Zenon
            <6>4. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4
          <5>11. CASE pc[q] = "U5" 
            <6> USE <5>11
            <6> SUFFICES c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] = "U5"
              BY RemDef, Zenon
            <6>4. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4
          <5>12. CASE pc[q] \in {"R1", "R3", "R4"}
            <6> USE <5>12
            <6> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
              BY RemDef, Zenon
            <6>1. CASE q = p
              <7> USE <6>1
              <7>1. pc'[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                BY RemDef, Zenon DEF KeyInBktAtAddr
              <7>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7>3. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = BOT
                BY Zenon DEF ConfigDomain  
              <7> QED
                BY <7>2, <7>3
            <6> SUFFICES ASSUME q # p
                          PROVE  c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
              BY <6>1
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              OBVIOUS
            <6>3. pc'[q] \in {"R1", "R3", "R4"}
              BY RemDef, Zenon
            <6>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4
          <5>13. CASE pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q]) 
            <6> USE <5>13
            <6> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
              BY RemDef, Zenon DEF KeyInBktAtAddr
            <6>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4              
          <5>14. CASE pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
            <6> USE <5>14
            <6> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = NULL
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
              BY RemDef, Zenon DEF KeyInBktAtAddr
            <6>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4    
          <5>15. CASE pc[q] = "R5"
            <6> USE <5>15
            <6> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] = "R5"
              BY RemDef, Zenon
            <6>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4
          <5> QED
              BY RemDef, ZenonT(120),
                  <5>1, <5>2, <5>3, <5>4, <5>5, <5>6, <5>7, <5>8, <5>9, 
                  <5>10, <5>11, <5>12, <5>13, <5>14, <5>15
              DEF LineIDs
        <4> QED
          BY <3>1, <4>1, <4>2, Zenon DEF S
      <3>3. Delta(c_pred, p, c)
        <4>1. c_pred.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL]
          BY <3>1, <3>2, Zenon DEF S
        <4>2. c_pred.op[p] = "Remove" /\ c_pred.arg[p] = arg[p] /\ c_pred.res[p] = BOT
          BY <3>1, <3>2, Zenon, RemDef DEF S
        <4>3. arg[p] \in ArgsOf("Remove") /\ arg[p].key \in KeyDomain
          BY RemDef, Zenon DEF ArgsOf, LineIDtoOp 
        <4> SUFFICES /\ c.state = [c_pred.state EXCEPT ![arg[p].key] = NULL]
                      /\ c.res = [c_pred.res EXCEPT ![p] = c_pred.state[arg[p].key]]
          BY <4>2, <4>3, Zenon DEF Delta
        <4> SUFFICES /\ c.state[arg[p].key] = NULL
                      /\ c.res[p] = IF KeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]]) 
                                      THEN ValOfKeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]]) 
                                      ELSE NULL
          BY <3>2, <4>3, ZenonT(60) DEF ConfigDomain, StateDomain
        <4>4. c.state[arg[p].key] = NULL
          BY <4>1, <4>2, <4>3, Zenon
        <4> SUFFICES c.res[p] = NULL
          BY <4>4, Zenon  
        <4>5. pc'[p] = "R2" /\ ~KeyInBktAtAddr(arg[p].key, bucket[p])'
          BY Zenon DEF KeyInBktAtAddr
        <4>6. c.res[p] = NULL
          BY <4>5, SPrimeRewrite, RemDef, Zenon DEF SPrime
        <4> QED  
          BY <4>6
      <3> QED
        BY <3>1, <3>2, <3>3, SingleDeltaEvolve
    <2>2. CASE KeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]])
      <3> USE <2>2
      <3> SUFFICES c \in S
        BY EmptySeqEvolve
      <3>1. \A k \in KeyDomain : KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
        BY Zenon, HashDef DEF KeyInBktAtAddr
      <3>2. \A k \in KeyDomain : ValOfKeyInBktAtAddr(k, A[Hash[k]]) = ValOfKeyInBktAtAddr(k, A[Hash[k]])'
        <4> SUFFICES ASSUME NEW k \in KeyDomain
                      PROVE  ValOfKeyInBktAtAddr(k, A[Hash[k]]) = ValOfKeyInBktAtAddr(k, A[Hash[k]])'
          OBVIOUS
        <4> DEFINE bkt_arr == MemLocs'[A'[Hash[k]]]
        <4> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
        <4>1. ValOfKeyInBktAtAddr(k, A[Hash[k]])' = bkt_arr[idx].val
          BY Zenon DEF ValOfKeyInBktAtAddr
        <4>2. bkt_arr = MemLocs[A[Hash[k]]] /\ A'[Hash[k]] = A[Hash[k]]
          BY Zenon
        <4> QED
          BY <4>1, <4>2 DEF ValOfKeyInBktAtAddr
      <3>3. c.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) 
                                              THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) 
                                              ELSE NULL]
        <4>1. c.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]])' THEN ValOfKeyInBktAtAddr(k, A[Hash[k]])' ELSE NULL]
          BY SPrimeRewrite, Zenon DEF SPrime
        <4> QED
          BY <3>1, <3>2, <4>1
      <3>4. ASSUME NEW q \in ProcSet
            PROVE  
              CASE pc[q] = RemainderID 
                    -> (c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT)
                [] pc[q] = "F1"
                  -> (c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                [] pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                  -> (c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q]))
                [] pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                  -> (c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL)
                [] pc[q] = "F3"
                  -> (c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q])
                [] pc[q] \in {"I1", "I3", "I4"}
                  -> (c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                [] pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                  -> (c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q]))
                [] pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                  -> (c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                [] pc[q] = "I5"
                  -> (c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q])
                [] pc[q] \in {"U1", "U2", "U3", "U4"}
                  -> (c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                [] pc[q] = "U5"
                  -> (c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q])
                [] pc[q] \in {"R1", "R3", "R4"}
                  -> (c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                [] pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                  -> (c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                [] pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                  -> (c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL)
                [] pc[q] = "R5"
                  -> (c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q])
        <4> USE <3>4
        <4>1. CASE pc[q] = RemainderID
          <5> USE <4>1
          <5> SUFFICES c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. pc'[q] = RemainderID
            BY RemDef, Zenon
          <5>2. c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>2. CASE pc[q] = "F1"
          <5> USE <4>2
          <5> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. pc'[q] = "F1"
            BY RemDef, Zenon
          <5>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2    
        <4>3. CASE pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>3
          <5> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            BY RemDef, Zenon
          <5>1. pc'[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <5>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5>3. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            <6> DEFINE bkt_arr == MemLocs'[bucket'[q]]
            <6> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg'[q].key
            <6>1. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = bkt_arr[idx].val
              BY Zenon DEF ValOfKeyInBktAtAddr
            <6>2. bkt_arr = MemLocs[bucket[q]]
              BY Zenon
            <6>3. arg'[q].key = arg[q].key
              BY Zenon
            <6> QED
              BY <6>1, <6>2, <6>3, Isa DEF ValOfKeyInBktAtAddr
          <5> QED
            BY <5>2, <5>3
        <4>4. CASE pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>4
          <5> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
            BY RemDef, Zenon
          <5>1. pc'[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
            BY <5>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>5. CASE pc[q] = "F3"
          <5> USE <4>5
          <5> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY RemDef, Zenon
          <5>1. pc'[q] = "F3"
            BY RemDef, Zenon
          <5>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2 
        <4>6. CASE pc[q] \in {"I1", "I3", "I4"}
          <5> USE <4>6
          <5> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>2. pc'[q] \in {"I1", "I3", "I4"}
            BY RemDef, Zenon
          <5>3. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>2, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>3 
        <4>7. CASE pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>7
          <5> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            BY RemDef, Zenon
          <5>1. pc'[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <5>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5>3. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            <6> DEFINE bkt_arr == MemLocs'[bucket'[q]]
            <6> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg'[q].key
            <6>1. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = bkt_arr[idx].val
              BY Zenon DEF ValOfKeyInBktAtAddr
            <6>2. bkt_arr = MemLocs[bucket[q]]
              BY Zenon
            <6>3. arg'[q].key = arg[q].key
              BY Zenon
            <6> QED
              BY <6>1, <6>2, <6>3, Isa DEF ValOfKeyInBktAtAddr
          <5> QED
            BY <5>2, <5>3
        <4>8. CASE pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>8
          <5> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. pc'[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>9. CASE pc[q] = "I5"
          <5> USE <4>9
          <5> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY RemDef, Zenon
          <5>1. pc'[q] = "I5"
            BY RemDef, Zenon
          <5>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2 
        <4>10. CASE pc[q] \in {"U1", "U2", "U3", "U4"}
          <5> USE <4>10
          <5> SUFFICES c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. pc'[q] \in {"U1", "U2", "U3", "U4"}
            BY RemDef, Zenon
          <5>2. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2 
        <4>11. CASE pc[q] = "U5" 
          <5> USE <4>11
          <5> SUFFICES c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY RemDef, Zenon
          <5>1. pc'[q] = "U5"
            BY RemDef, Zenon
          <5>2. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2 
        <4>12. CASE pc[q] \in {"R1", "R3", "R4"}
          <5> USE <4>12
          <5> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. CASE p = q
            <6> USE <5>1
            <6>1. arg[q].key = arg'[q].key /\ bucket'[q] = A[Hash[arg[q].key]]
              BY Zenon
            <6>2. pc'[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
              BY <6>1, Zenon DEF KeyInBktAtAddr
            <6>3. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
              BY <6>2, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>3
          <5> SUFFICES ASSUME p # q
                        PROVE  c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>1
          <5>2. pc'[q] \in {"R1", "R3", "R4"}
            BY RemDef, Zenon
          <5>3. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>2, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>3 
        <4>13. CASE pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>13
          <5> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. pc'[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>14. CASE pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>14
          <5> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
            BY RemDef, Zenon
          <5>1. pc'[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
            BY <5>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>15. CASE pc[q] = "R5"
          <5> USE <4>15
          <5> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY RemDef, Zenon
          <5>1. pc'[q] = "R5"
            BY RemDef, Zenon
          <5>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2 
        <4> QED
          BY RemDef, ZenonT(120),
              <4>1, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, 
              <4>10, <4>11, <4>12, <4>13, <4>14, <4>15
          DEF LineIDs
      <3> QED
        BY <3>3, <3>4, Zenon DEF S
    <2> QED
      BY <2>1, <2>2
  <1>12. CASE LineAction = R2(p)
    <2> USE <1>12 DEF R2, TypeOK, Inv
    <2> SUFFICES ASSUME NEW c \in ConfigDomain,
                        c \in S'
                 PROVE  c \in Evolve(S)
      BY Zenon DEF S
    <2> SUFFICES c \in S
      BY EmptySeqEvolve
    <2>1. c.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL]
      <3>1. c.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]])' THEN ValOfKeyInBktAtAddr(k, A[Hash[k]])' ELSE NULL]
        BY Zenon, SPrimeRewrite DEF SPrime
      <3>2. \A k \in KeyDomain : KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
        BY Zenon DEF KeyInBktAtAddr
      <3>3. \A k \in KeyDomain : ValOfKeyInBktAtAddr(k, A[Hash[k]])' = ValOfKeyInBktAtAddr(k, A[Hash[k]])
        <4> SUFFICES ASSUME NEW k \in KeyDomain
                      PROVE  ValOfKeyInBktAtAddr(k, A[Hash[k]])' = ValOfKeyInBktAtAddr(k, A[Hash[k]])
          OBVIOUS
        <4> bkt_arr == MemLocs'[A'[Hash[k]]]
        <4> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
        <4>1. ValOfKeyInBktAtAddr(k, A[Hash[k]])' = bkt_arr[idx].val
          BY DEF ValOfKeyInBktAtAddr
        <4>2. bkt_arr = MemLocs[A[Hash[k]]]
          BY Zenon
        <4> QED
          BY <4>1, <4>2, ZenonT(30) DEF ValOfKeyInBktAtAddr
      <3> QED
        BY <3>1, <3>2, <3>3
    <2>2. ASSUME NEW q \in ProcSet
          PROVE
              CASE pc[q] = RemainderID 
                  -> (c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT)
                [] pc[q] = "F1"
                  -> (c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                [] pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                  -> (c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q]))
                [] pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                  -> (c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL)
                [] pc[q] = "F3"
                  -> (c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q])
                [] pc[q] \in {"I1", "I3", "I4"}
                  -> (c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                [] pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                  -> (c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q]))
                [] pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                  -> (c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                [] pc[q] = "I5"
                  -> (c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q])
                [] pc[q] \in {"U1", "U2", "U3", "U4"}
                  -> (c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                [] pc[q] = "U5"
                  -> (c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q])
                [] pc[q] \in {"R1", "R3", "R4"}
                  -> (c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                [] pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                  -> (c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                [] pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                  -> (c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL)
                [] pc[q] = "R5"
                  -> (c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q])
      <3> USE <2>2
      <3>A. \A k \in KeyDomain : KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, bucket[q])'
        BY Zenon DEF KeyInBktAtAddr
      <3>B. \A k \in KeyDomain : ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, bucket[q])
        <4> SUFFICES ASSUME NEW k \in KeyDomain
                      PROVE  ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, bucket[q])
          OBVIOUS
        <4> bkt_arr == MemLocs'[bucket'[q]]
        <4> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
        <4>1. ValOfKeyInBktAtAddr(k, bucket[q])' = bkt_arr[idx].val
          BY DEF ValOfKeyInBktAtAddr
        <4>2. bkt_arr = MemLocs[bucket[q]]
          BY Zenon
        <4> QED
          BY <4>1, <4>2, ZenonT(30) DEF ValOfKeyInBktAtAddr
      <3>1. CASE pc[q] = RemainderID
        <4> USE <3>1
        <4> SUFFICES c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
          BY RemDef, Zenon
        <4>1. pc'[q] = RemainderID
          BY RemDef, Zenon
        <4>2. c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
          BY <4>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2
      <3>2. CASE pc[q] = "F1"
        <4> USE <3>2
        <4> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY RemDef, Zenon
        <4>1. pc'[q] = "F1"
          BY RemDef, Zenon
        <4>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY <4>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2
      <3>3. CASE pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
        <4> USE <3>3
        <4> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
          BY RemDef, Zenon
        <4>1. CASE q = p
          <5> USE <4>1
          <5>1. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r'[q]
            BY SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            BY <5>1, Zenon
          <5> QED
            BY <5>2
        <4> SUFFICES ASSUME q # p
                      PROVE  c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
          BY <4>1
        <4>2. pc'[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
          BY RemDef, Zenon DEF KeyInBktAtAddr
        <4>3. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
          BY <4>2,  SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4>4. arg[q].key = arg'[q].key /\ arg[q].key \in KeyDomain
          BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
        <4>5. c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
          BY <4>3, <4>4, <3>B
        <4> QED
          BY <4>3, <4>5
      <3>4. CASE pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
        <4> USE <3>4
        <4> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
          BY RemDef, Zenon
        <4>1. CASE q = p
          <5> USE <4>1
          <5>1. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r'[q]
            BY SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
            BY <5>1, Zenon
          <5> QED
            BY <5>2
        <4> SUFFICES ASSUME q # p
                      PROVE  c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
          BY <4>1
        <4>2. pc'[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
          BY RemDef, Zenon DEF KeyInBktAtAddr
        <4>3. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
          BY <4>2,  SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>3
      <3>5. CASE pc[q] = "F3"
        <4> USE <3>5
        <4> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
          BY RemDef, Zenon
        <4>1. pc'[q] = "F3"
          BY RemDef, Zenon
        <4>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
          BY <4>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2 
      <3>6. CASE pc[q] \in {"I1", "I3", "I4"}
        <4> USE <3>6
        <4> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY RemDef, Zenon
        <4>1. pc'[q] \in {"I1", "I3", "I4"}
          BY RemDef, Zenon
        <4>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY <4>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2 
      <3>7. CASE pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
        <4> USE <3>7
        <4> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
          BY RemDef, Zenon
        <4>2. pc'[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
          BY RemDef, Zenon DEF KeyInBktAtAddr
        <4>3. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
          BY <4>2,  SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4>4. arg[q].key = arg'[q].key /\ arg[q].key \in KeyDomain
          BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
        <4>5. c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
          BY <4>3, <4>4, <3>B
        <4> QED
          BY <4>3, <4>5
      <3>8. CASE pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
        <4> USE <3>8
        <4> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY RemDef, Zenon
        <4>1. pc'[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
          BY RemDef, Zenon DEF KeyInBktAtAddr
        <4>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY <4>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2 
      <3>9. CASE pc[q] = "I5"
        <4> USE <3>9
        <4> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
          BY RemDef, Zenon
        <4>1. pc'[q] = "I5"
          BY RemDef, Zenon 
        <4>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
          BY <4>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2 
      <3>10. CASE pc[q] \in {"U1", "U2", "U3", "U4"}
        <4> USE <3>10
        <4> SUFFICES c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY RemDef, Zenon
        <4>1. pc'[q] \in {"U1", "U2", "U3", "U4"}
          BY RemDef, Zenon
        <4>2. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY <4>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2
      <3>11. CASE pc[q] = "U5" 
        <4> USE <3>11
        <4> SUFFICES c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
          BY RemDef, Zenon
        <4>1. pc'[q] = "U5"
          BY RemDef, Zenon
        <4>2. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
          BY <4>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2
      <3>12. CASE pc[q] \in {"R1", "R3", "R4"}
        <4> USE <3>12
        <4> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY RemDef, Zenon
        <4>1. pc'[q] \in {"R1", "R3", "R4"}
          BY RemDef, Zenon
        <4>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY <4>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2
      <3>13. CASE pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
        <4> USE <3>13
        <4> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY RemDef, Zenon
        <4>1. CASE p = q
          <5> USE <4>1
          <5>1. c.op[p] = "Remove" /\ c.arg[p] = arg[p] /\ c.res[p] = BOT
            BY SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>1
        <4> SUFFICES ASSUME p # q
                      PROVE  c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY <4>1
        <4>2. pc'[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
          BY RemDef, Zenon DEF KeyInBktAtAddr
        <4>3. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY <4>2, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>3
      <3>14. CASE pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
        <4> USE <3>14
        <4> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
          BY RemDef, Zenon
        <4>1. CASE p = q
          <5> USE <4>1
          <5>1. r'[p] = NULL
            BY Zenon
          <5>2. c.op[p] = "Remove" /\ c.arg[p] = arg[p] /\ c.res[p] = NULL
            BY SPrimeRewrite, Zenon, RemDef, <5>1 DEF SPrime
          <5> QED
            BY <5>2
        <4> SUFFICES ASSUME p # q
                      PROVE  c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
          BY <4>1
        <4>2. pc'[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
          BY RemDef, Zenon DEF KeyInBktAtAddr
        <4>3. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
          BY <4>2, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>3
      <3>15. CASE pc[q] = "R5"
        <4> USE <3>15
        <4> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
          BY RemDef, Zenon
        <4>1. pc'[q] = "R5" 
          BY RemDef, Zenon
        <4>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
          BY <4>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2
      <3> QED
          BY RemDef, ZenonT(120),
              <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9, 
              <3>10, <3>11, <3>12, <3>13, <3>14, <3>15
          DEF LineIDs
    <2> QED
      BY <2>1, <2>2, Zenon DEF S
  <1>13. CASE LineAction = R3(p)
    <2> USE <1>13 DEF TypeOK, Inv
    <2> SUFFICES ASSUME NEW c \in ConfigDomain,
                        c \in S'
                 PROVE  c \in Evolve(S)
      BY Zenon DEF S
    <2> SUFFICES c \in S
      BY EmptySeqEvolve
    <2> /\ pc[p] = "R3" 
        /\ pc' = [pc EXCEPT ![p] = "R4"]
        /\ UNCHANGED <<A, bucket, r, arg, ret>>
      BY Zenon DEF R3
    <2>1. KeyInBktAtAddr(arg[p].key, bucket[p])
      BY DEF BktInv
    <2>2. PICK i \in 1..Len(MemLocs[bucket[p]]) : MemLocs[bucket[p]][i].key = arg[p].key
      BY Zenon, <2>1 DEF KeyInBktAtAddr
    <2>3. i = CHOOSE index \in 1..Len(MemLocs[bucket[p]]) : MemLocs[bucket[p]][index].key = arg[p].key
      BY <2>2
    <2>4. i = IdxInBktAtAddr(arg[p].key, bucket[p])
      BY Zenon, <2>3 DEF IdxInBktAtAddr
    <2> PICK addr \in Addrs :
              /\ addr \notin AllocAddrs
              /\ AllocAddrs' = AllocAddrs \cup {addr}
              /\ newbkt' = [newbkt EXCEPT ![p] = addr]
              /\ MemLocs' = [MemLocs EXCEPT ![addr] = SubSeq(MemLocs[bucket[p]], 1, i-1) \o SubSeq(MemLocs[bucket[p]], i+1, Len(MemLocs[bucket[p]]))]
      BY <2>4, Zenon DEF R3
    <2> /\ i \in 1..Len(MemLocs[bucket[p]])
        /\ MemLocs[bucket[p]][i].key = arg[p].key
      BY <2>2
    <2>5. c.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL]
      <3>1. c.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]])' THEN ValOfKeyInBktAtAddr(k, A[Hash[k]])' ELSE NULL]
        BY Zenon, SPrimeRewrite DEF SPrime
      <3>2. \A k \in KeyDomain : KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
        <4> SUFFICES ASSUME NEW k \in KeyDomain
                      PROVE  KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
          OBVIOUS
        <4>1. A'[Hash[k]] = A[Hash[k]]
          BY Zenon
        <4>2. CASE A[Hash[k]] = NULL
          BY <4>1, <4>2 DEF KeyInBktAtAddr
        <4> SUFFICES ASSUME A[Hash[k]] # NULL
                      PROVE  KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
          BY <4>2
        <4>3. A[Hash[k]] \in AllocAddrs
          BY HashDef, Zenon
        <4>4. A[Hash[k]] # addr
          BY NULLDef, <4>3
        <4>5. \A a \in Addrs : a # addr => MemLocs'[a] = MemLocs[a]
          BY Zenon
        <4>6. MemLocs'[A'[Hash[k]]] = MemLocs[A[Hash[k]]]
          BY <4>1, <4>4, <4>5
        <4> QED
          BY <4>6, Zenon DEF KeyInBktAtAddr
      <3>3. \A k \in KeyDomain : KeyInBktAtAddr(k, A[Hash[k]]) => (ValOfKeyInBktAtAddr(k, A[Hash[k]]) = ValOfKeyInBktAtAddr(k, A[Hash[k]])')
        <4> SUFFICES ASSUME NEW k \in KeyDomain,
                            NEW bkt_arr,
                            A[Hash[k]] # NULL,
                            bkt_arr = MemLocs[A[Hash[k]]],
                            \E index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
                      PROVE  ValOfKeyInBktAtAddr(k, A[Hash[k]]) = ValOfKeyInBktAtAddr(k, A[Hash[k]])'
          BY Zenon DEF KeyInBktAtAddr
        <4>1. A'[Hash[k]] = A[Hash[k]]
          BY Zenon
        <4>2. A[Hash[k]] \in AllocAddrs
          BY HashDef, Zenon
        <4>3. A[Hash[k]] # addr
          BY NULLDef, <4>2
        <4>4. \A a \in Addrs : a # addr => MemLocs'[a] = MemLocs[a]                 
          BY Zenon
        <4>5. MemLocs'[A'[Hash[k]]] = MemLocs[A[Hash[k]]]
          BY <4>1, <4>3, <4>4
        <4> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
        <4>6. ValOfKeyInBktAtAddr(k, A[Hash[k]]) = bkt_arr[idx].val
          BY Zenon DEF ValOfKeyInBktAtAddr
        <4>7. ValOfKeyInBktAtAddr(k, A[Hash[k]])' = bkt_arr[idx].val
          BY Isa, <4>5 DEF ValOfKeyInBktAtAddr
        <4> QED
          BY <4>6, <4>7, Zenon
      <3> QED
        BY <3>1, <3>2, <3>3, Zenon
    <2>6. ASSUME NEW q \in ProcSet
              PROVE
                  CASE pc[q] = RemainderID 
                      -> (c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT)
                    [] pc[q] = "F1"
                      -> (c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                    [] pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                      -> (c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q]))
                    [] pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                      -> (c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL)
                    [] pc[q] = "F3"
                      -> (c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q])
                    [] pc[q] \in {"I1", "I3", "I4"}
                      -> (c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                    [] pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                      -> (c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q]))
                    [] pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                      -> (c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                    [] pc[q] = "I5"
                      -> (c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q])
                    [] pc[q] \in {"U1", "U2", "U3", "U4"}
                      -> (c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                    [] pc[q] = "U5"
                      -> (c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q])
                    [] pc[q] \in {"R1", "R3", "R4"}
                      -> (c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                    [] pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                      -> (c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                    [] pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                      -> (c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL)
                    [] pc[q] = "R5"
                      -> (c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q])
      <3> USE <2>6
      <3>1. KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
        <4>1. bucket[q] = bucket'[q]
          BY Zenon
        <4>2. CASE bucket[q] = NULL
          BY <4>1, <4>2, Zenon DEF KeyInBktAtAddr
        <4> SUFFICES ASSUME bucket[q] # NULL
                      PROVE  KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
          BY <4>2
        <4>3. bucket[q] \in AllocAddrs
          BY NULLDef, Zenon
        <4>4. bucket[q] # addr
          BY <4>3
        <4>5. \A a \in Addrs : a # addr => MemLocs'[a] = MemLocs[a]
          BY Zenon
        <4>6. MemLocs'[bucket'[q]] = MemLocs[bucket[q]]
          BY <4>1, <4>4, <4>5
        <4> QED
          BY <4>6, Zenon DEF KeyInBktAtAddr
      <3>2. KeyInBktAtAddr(arg[q].key, bucket[q]) => (ValOfKeyInBktAtAddr(arg[q].key, bucket[q]) = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])')
        <4> SUFFICES ASSUME NEW bkt_arr,
                            bkt_arr = MemLocs[bucket[q]],
                            bucket[q] # NULL,
                            \E index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
                      PROVE  ValOfKeyInBktAtAddr(arg[q].key, bucket[q]) = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
          BY Zenon DEF KeyInBktAtAddr
        <4>1. bucket[q] = bucket'[q]
          BY Zenon
        <4>2. bucket[q] \in AllocAddrs
          BY NULLDef, Zenon
        <4>3. bucket[q] # addr
          BY <4>2
        <4>4. \A a \in Addrs : a # addr => MemLocs'[a] = MemLocs[a]
          BY Zenon
        <4>5. MemLocs'[bucket'[q]] = MemLocs[bucket[q]]
          BY <4>1, <4>3, <4>4 
        <4> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
        <4>6. ValOfKeyInBktAtAddr(arg[q].key, bucket[q]) = bkt_arr[idx].val
          BY Zenon DEF ValOfKeyInBktAtAddr
        <4>7. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = bkt_arr[idx].val
          BY Isa, <4>5 DEF ValOfKeyInBktAtAddr
        <4> QED
          BY <4>6, <4>7, Zenon
      <3>3. CASE pc[q] = RemainderID
        <4> USE <3>3
        <4> SUFFICES c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
          BY RemDef, Zenon
        <4>1. pc'[q] = RemainderID
          BY RemDef, Zenon
        <4>2. c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
          BY <4>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2
      <3>4. CASE pc[q] = "F1"
        <4> USE <3>4
        <4> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY RemDef, Zenon
        <4>1. pc'[q] = "F1"
          BY RemDef, Zenon
        <4>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY <4>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2  
      <3>5. CASE pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
        <4> USE <3>5
        <4> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
          BY RemDef, Zenon
        <4>1. pc'[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
          BY <3>1, RemDef, Zenon DEF KeyInBktAtAddr
        <4>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
          BY <4>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4>3. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
          BY <3>2, Zenon
        <4> QED
          BY <4>2, <4>3
      <3>6. CASE pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
        <4> USE <3>6
        <4> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
          BY RemDef, Zenon
        <4>1. pc'[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
          BY <3>1, RemDef, Zenon DEF KeyInBktAtAddr
        <4>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
          BY <4>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2
      <3>7. CASE pc[q] = "F3" 
        <4> USE <3>7
        <4> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
          BY RemDef, Zenon
        <4>1. pc'[q] = "F3"
          BY RemDef, Zenon
        <4>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
          BY <4>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2
      <3>8. CASE pc[q] \in {"I1", "I3", "I4"}
        <4> USE <3>8
        <4> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY RemDef, Zenon
        <4>2. pc'[q] \in {"I1", "I3", "I4"}
          BY RemDef, Zenon
        <4>3. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY <4>2,  SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>3
      <3>9. CASE pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
        <4> USE <3>9
        <4> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
          BY RemDef, Zenon
        <4>1. pc'[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
          BY <3>1, RemDef, Zenon DEF KeyInBktAtAddr
        <4>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
          BY <4>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4>3. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
          BY <3>2, Zenon
        <4> QED
          BY <4>2, <4>3
      <3>10. CASE pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
        <4> USE <3>10
        <4> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY RemDef, Zenon
        <4>1. pc'[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
          BY <3>1, RemDef, Zenon DEF KeyInBktAtAddr
        <4>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY <4>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2
      <3>11. CASE pc[q] = "I5"
        <4> USE <3>11
        <4> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
          BY RemDef, Zenon
        <4>1. pc'[q] = "I5"
          BY RemDef, Zenon
        <4>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
          BY <4>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2
      <3>12. CASE pc[q] \in {"U1", "U2", "U3", "U4"}
        <4> USE <3>12
        <4> SUFFICES c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY RemDef, Zenon
        <4>1. pc'[q] \in {"U1", "U2", "U3", "U4"}
          BY RemDef, Zenon
        <4>2. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY <4>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2
      <3>13. CASE pc[q] = "U5" 
        <4> USE <3>13
        <4> SUFFICES c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
          BY RemDef, Zenon
        <4>1. pc'[q] = "U5"
          BY RemDef, Zenon
        <4>2. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
          BY <4>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2
      <3>14. CASE pc[q] \in {"R1", "R3", "R4"}
        <4> USE <3>14
        <4> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY RemDef, Zenon
        <4>1. pc'[q] \in {"R1", "R3", "R4"}
          BY RemDef, Zenon
        <4>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY <4>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2
      <3>15. CASE pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
        <4> USE <3>15
        <4> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY RemDef, Zenon
        <4>1. pc'[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
          BY <3>1, RemDef, Zenon DEF KeyInBktAtAddr
        <4>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
          BY <4>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime               
        <4> QED
          BY <4>2
      <3>16. CASE pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
        <4> USE <3>16
        <4> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
          BY RemDef, Zenon
        <4>1. pc'[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
          BY <3>1, RemDef, Zenon DEF KeyInBktAtAddr
        <4>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
          BY <4>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2
      <3>17. CASE pc[q] = "R5"
        <4> USE <3>17
        <4> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
          BY RemDef, Zenon
        <4>1. pc'[q] = "R5"
          BY RemDef, Zenon
        <4>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
          BY <4>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
        <4> QED
          BY <4>2
      <3> QED
          BY RemDef, ZenonT(120),
              <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9, <3>10, <3>11, 
              <3>12, <3>13, <3>14, <3>15, <3>16, <3>17
          DEF LineIDs
    <2> QED
      BY <2>5, <2>6, Zenon DEF S
  <1>14. CASE LineAction = R4(p)
    <2> USE <1>14 DEF R4, TypeOK, Inv
    <2> SUFFICES ASSUME NEW c \in ConfigDomain,
                 c \in S'
                 PROVE c \in Evolve(S)
      BY Zenon DEF S
    <2>1. CASE A[Hash[arg[p].key]] = bucket[p]
      <3> USE <2>1
      <3> DEFINE c_pred == [state |-> [c.state EXCEPT ![arg[p].key] = ValOfKeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]])],
                            op    |-> c.op,
                            arg   |-> c.arg,
                            res   |-> [c.res EXCEPT ![p] = BOT]]
      <3>1. c_pred \in ConfigDomain
        <4>1. c_pred.state \in StateDomain
          <5>1. arg[p].key \in KeyDomain
            BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
          <5> KeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]])
            BY Zenon DEF BktInv
          <5> SUFFICES ValOfKeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]]) \in ValDomain
            BY <5>1 DEF StateDomain, ConfigDomain
          <5>2. PICK idx \in 1..Len(MemLocs[A[Hash[arg[p].key]]]) : MemLocs[A[Hash[arg[p].key]]][idx].key = arg[p].key
            BY Zenon DEF KeyInBktAtAddr
          <5>3. idx = CHOOSE index \in 1..Len(MemLocs[A[Hash[arg[p].key]]]) : MemLocs[A[Hash[arg[p].key]]][index].key = arg[p].key
            BY <5>2
          <5>4. ValOfKeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]]) = MemLocs[A[Hash[arg[p].key]]][idx].val
            BY Zenon, <5>3 DEF ValOfKeyInBktAtAddr
          <5>5. A[Hash[arg[p].key]] # NULL
            BY Zenon DEF KeyInBktAtAddr
          <5>6. MemLocs[A[Hash[arg[p].key]]] \in Seq([key: KeyDomain, val: ValDomain])
            BY Zenon, HashDef, NULLDef, <5>5
          <5>7. MemLocs[A[Hash[arg[p].key]]][idx] \in [key: KeyDomain, val: ValDomain]
            BY Zenon, <5>2, <5>6, ElementOfSeq
          <5>8. MemLocs[A[Hash[arg[p].key]]][idx].val \in ValDomain
            BY <5>7
          <5> QED
            BY <5>4, <5>8
        <4>2. c_pred.op \in [ProcSet -> OpDomain]
          BY DEF ConfigDomain
        <4>3. c_pred.arg \in [ProcSet -> ArgDomain]
          BY DEF ConfigDomain
        <4>4. c_pred.res \in [ProcSet -> ResDomain]
          BY DEF ConfigDomain, ResDomain
        <4> QED
          BY <4>1, <4>2, <4>3, <4>4 DEF ConfigDomain
      <3>2. c_pred \in S
        <4>1. c_pred.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL]
          <5> SUFFICES ASSUME NEW k \in KeyDomain
                        PROVE  c_pred.state[k] = IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL
            BY Zenon, <3>1 DEF StateDomain, ConfigDomain
          <5>1. CASE k = arg[p].key
            <6>1. arg[p].key \in KeyDomain
              BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
            <6>2. KeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]]) 
              BY Zenon DEF BktInv
            <6>3. c_pred.state[arg[p].key] = ValOfKeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]])
              BY <6>1, Zenon DEF StateDomain, ConfigDomain
            <6> QED
              BY <5>1, <6>2, <6>3 DEF StateDomain, ConfigDomain
          <5>2. CASE k # arg[p].key /\ Hash[k] # Hash[arg[p].key]
            <6> USE <5>2
            <6>1. c.state = [key \in KeyDomain |-> IF KeyInBktAtAddr(key, A[Hash[key]])' THEN ValOfKeyInBktAtAddr(key, A[Hash[key]])' ELSE NULL]
              BY SPrimeRewrite, Zenon DEF SPrime
            <6>2. A'[Hash[k]] = A[Hash[k]]
              BY HashDef, Zenon
            <6>3. KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
              BY <6>2, Zenon DEF KeyInBktAtAddr
            <6>4. ValOfKeyInBktAtAddr(k, A[Hash[k]]) = ValOfKeyInBktAtAddr(k, A[Hash[k]])'
              <7> DEFINE bkt_arr == MemLocs'[A'[Hash[k]]]
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
              <7>1. ValOfKeyInBktAtAddr(k, A[Hash[k]])' = bkt_arr[idx].val
                BY Zenon DEF ValOfKeyInBktAtAddr
              <7>2. bkt_arr = MemLocs[A[Hash[k]]]
                BY Zenon, <6>2
              <7>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
                BY Zenon
              <7>4. ValOfKeyInBktAtAddr(k, A[Hash[k]]) = MemLocs[A[Hash[k]]][CHOOSE index \in 1..Len(MemLocs[A[Hash[k]]]) : MemLocs[A[Hash[k]]][index].key = k].val
                BY Zenon DEF ValOfKeyInBktAtAddr
              <7>5. ValOfKeyInBktAtAddr(k, A[Hash[k]]) = bkt_arr[idx].val
                BY ZenonT(90), <7>2, <7>3, <7>4
              <7> QED
                BY Zenon, <7>1, <7>5
            <6> QED
              BY <6>1, <6>3, <6>4
          <5>3. CASE k # arg[p].key /\ Hash[k] = Hash[arg[p].key]
            <6> USE <5>3
            <6>1. c.state = [key \in KeyDomain |-> IF KeyInBktAtAddr(key, A[Hash[key]])' 
                                                      THEN ValOfKeyInBktAtAddr(key, A[Hash[key]])' 
                                                      ELSE NULL]
              BY SPrimeRewrite, Zenon DEF SPrime
            <6>2. c_pred.state[k] = IF KeyInBktAtAddr(k, A[Hash[k]])' 
                                        THEN ValOfKeyInBktAtAddr(k, A[Hash[k]])' 
                                        ELSE NULL
              BY <6>1
            <6>3. MemLocs' = MemLocs
              BY Zenon
            <6>4. bucket[p] = A[Hash[k]]
              BY Zenon
            <6>5. arg[p].key \in KeyDomain
              BY RemDef, Zenon DEF ArgsOf, LineIDtoOp
            <6>6. newbkt[p] = A'[Hash[k]]
              BY Zenon, <6>5, HashDef
            <6>7. KeyInBktAtAddr(k, A[Hash[k]])' = KeyInBktAtAddr(k, newbkt[p])
              BY <6>6, Zenon DEF KeyInBktAtAddr
            <6>8. ValOfKeyInBktAtAddr(k, A[Hash[k]])' = ValOfKeyInBktAtAddr(k, newbkt[p])
              BY <6>6, Zenon DEF ValOfKeyInBktAtAddr
            <6>9. c_pred.state[k] = IF KeyInBktAtAddr(k, newbkt[p]) THEN ValOfKeyInBktAtAddr(k, newbkt[p]) ELSE NULL
              BY <6>2, <6>7, <6>8, Zenon
            <6>10. /\ KeyInBktAtAddr(k, bucket[p]) = KeyInBktAtAddr(k, newbkt[p])
                   /\ KeyInBktAtAddr(k, bucket[p]) => (ValOfKeyInBktAtAddr(k, bucket[p]) = ValOfKeyInBktAtAddr(k, newbkt[p]))
              BY Zenon DEF NewBktInv
            <6>11. c_pred.state[k] = IF KeyInBktAtAddr(k, bucket[p]) THEN ValOfKeyInBktAtAddr(k, bucket[p]) ELSE NULL
              BY <6>9, <6>10, Zenon
            <6>12. c_pred.state[k] = IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL
              BY <6>11, <6>6, Zenon
            <6> QED
              BY <6>12, Zenon
          <5> QED
            BY <5>1, <5>2, <5>3
        <4>2. ASSUME NEW q \in ProcSet
              PROVE
                CASE pc[q] = RemainderID 
                    -> (c_pred.op[q] = BOT /\ c_pred.arg[q] = BOT /\ c_pred.res[q] = BOT)
                  [] pc[q] = "F1"
                    -> (c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q]))
                  [] pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = NULL)
                  [] pc[q] = "F3"
                    -> (c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q])
                  [] pc[q] \in {"I1", "I3", "I4"}
                    -> (c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q]))
                  [] pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "I5"
                    -> (c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q])
                  [] pc[q] \in {"U1", "U2", "U3", "U4"}
                    -> (c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "U5"
                    -> (c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q])
                  [] pc[q] \in {"R1", "R3", "R4"}
                    -> (c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT)
                  [] pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = NULL)
                  [] pc[q] = "R5"
                    -> (c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q])
          <5> USE <4>2
          <5>1. CASE pc[q] = RemainderID
            <6> USE <5>1
            <6> SUFFICES c_pred.op[q] = BOT /\ c_pred.arg[q] = BOT /\ c_pred.res[q] = BOT
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] = RemainderID
              BY RemDef, Zenon
            <6>4. c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4
          <5>2. CASE pc[q] = "F1"
            <6> USE <5>2
            <6> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] = "F1"
              BY RemDef, Zenon
            <6>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4
          <5>3. CASE pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
            <6> USE <5>3
            <6> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
              BY RemDef, Zenon DEF KeyInBktAtAddr
            <6>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
              <7> DEFINE bkt_arr == MemLocs'[bucket'[q]]
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg'[q].key
              <7>1. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = bkt_arr[idx].val
                BY Zenon DEF ValOfKeyInBktAtAddr
              <7>2. bkt_arr = MemLocs[bucket[q]]
                BY Zenon
              <7>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
                BY Zenon
              <7> QED
                BY <7>1, <7>2, <7>3, Isa DEF ValOfKeyInBktAtAddr
            <6> QED
              BY <6>2, <6>4, <6>5
          <5>4. CASE pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
            <6> USE <5>4
            <6> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = NULL
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
              BY RemDef, Zenon DEF KeyInBktAtAddr
            <6>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4
          <5>5. CASE pc[q] = "F3"
            <6> USE <5>5
            <6> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] = "F3"
              BY RemDef, Zenon
            <6>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4 
          <5>6. CASE pc[q] \in {"I1", "I3", "I4"}
            <6> USE <5>6
            <6> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
              BY RemDef, Zenon
            <6>A. CASE p = q
              <7> USE <6>A
              <7>1. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = BOT
                BY <3>1 DEF ConfigDomain
              <7>2. pc'[q] = "I5"
                BY Zenon
              <7>3. c.op[q] = "Insert" /\ c.arg[p] = arg[q]
                BY <7>2, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>1, <7>3
            <6> SUFFICES ASSUME p # q
                          PROVE  c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
              BY <6>A
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              OBVIOUS
            <6>3. pc'[q] \in {"I1", "I3", "I4"}
              BY RemDef, Zenon
            <6>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4
          <5>7. CASE pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
            <6> USE <5>7
            <6> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
              BY RemDef, Zenon DEF KeyInBktAtAddr
            <6>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
              <7> DEFINE bkt_arr == MemLocs'[bucket'[q]]
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg'[q].key
              <7>1. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = bkt_arr[idx].val
                BY Zenon DEF ValOfKeyInBktAtAddr
              <7>2. bkt_arr = MemLocs[bucket[q]]
                BY Zenon
              <7>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
                BY Zenon
              <7> QED
                BY <7>1, <7>2, <7>3, Isa DEF ValOfKeyInBktAtAddr
            <6> QED
              BY <6>2, <6>4, <6>5
          <5>8. CASE pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
            <6> USE <5>8
            <6> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
              BY RemDef, Zenon DEF KeyInBktAtAddr
            <6>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4
          <5>9. CASE pc[q] = "I5"
            <6> USE <5>9
            <6> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] = "I5"
              BY RemDef, Zenon
            <6>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4
          <5>10. CASE pc[q] \in {"U1", "U2", "U3", "U4"}
            <6> USE <5>10
            <6> SUFFICES c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
              BY RemDef, Zenon
            <6>1. q # p
              BY Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] \in {"U1", "U2", "U3", "U4"}
              BY RemDef, Zenon
            <6>4. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4
          <5>11. CASE pc[q] = "U5" 
            <6> USE <5>11
            <6> SUFFICES c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] = "U5"
              BY RemDef, Zenon
            <6>4. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4
          <5>12. CASE pc[q] \in {"R1", "R3", "R4"}
            <6> USE <5>12
            <6> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
              BY RemDef, Zenon
            <6>1. CASE q = p
              <7> USE <6>1
              <7>1. pc'[q] = "R5"
                BY Zenon
              <7>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r'[q]
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7>3. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = BOT
                BY DEF ConfigDomain 
              <7> QED
                BY <7>2, <7>3
            <6> SUFFICES ASSUME q # p
                          PROVE  c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
              BY <6>1
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              OBVIOUS
            <6>3. pc'[q] \in {"R1", "R3", "R4"}
              BY RemDef, Zenon
            <6>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4
          <5>13. CASE pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q]) 
            <6> USE <5>13
            <6> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
              BY RemDef, Zenon DEF KeyInBktAtAddr
            <6>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4              
          <5>14. CASE pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
            <6> USE <5>14
            <6> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = NULL
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
              BY RemDef, Zenon DEF KeyInBktAtAddr
            <6>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4    
          <5>15. CASE pc[q] = "R5"
            <6> USE <5>15
            <6> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
              BY RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] = "R5"
              BY RemDef, Zenon
            <6>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4
          <5> QED
              BY RemDef, ZenonT(120),
                  <5>1, <5>2, <5>3, <5>4, <5>5, <5>6, <5>7, <5>8, <5>9, 
                  <5>10, <5>11, <5>12, <5>13, <5>14, <5>15
              DEF LineIDs 
        <4> QED
          BY <3>1, <4>1, <4>2, Zenon DEF S
      <3>3. Delta(c_pred, p, c)
        <4>1. c_pred.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL]
          BY <3>1, <3>2, Zenon DEF S
        <4>2. c_pred.op[p] = "Remove" /\ c_pred.arg[p] = arg[p] /\ c_pred.res[p] = BOT
          BY <3>1, <3>2, Zenon, RemDef DEF S
        <4>3. arg[p] \in ArgsOf("Remove") /\ arg[p].key \in KeyDomain
          BY RemDef, Zenon DEF ArgsOf, LineIDtoOp 
        <4> SUFFICES /\ c.state = [c_pred.state EXCEPT ![arg[p].key] = NULL]
                     /\ c.res = [c_pred.res EXCEPT ![p] = c_pred.state[arg[p].key]]
          BY <4>2, <4>3, Zenon DEF Delta
        <4> SUFFICES /\ c.state[arg[p].key] = NULL
                     /\ c.res = [c_pred.res EXCEPT ![p] = c_pred.state[arg[p].key]]
          BY <4>2, <4>3, Zenon DEF ConfigDomain, StateDomain
        <4>4. c_pred.state[arg[p].key] = IF KeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]]) 
                                          THEN ValOfKeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]]) 
                                          ELSE NULL
          BY <4>1, <4>2, <4>3, Zenon DEF ConfigDomain, StateDomain
        <4> SUFFICES /\ c.state[arg[p].key] = NULL
                     /\ c.res[p] = IF KeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]]) 
                                      THEN ValOfKeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]]) 
                                      ELSE NULL
          BY <3>2, <4>4, Zenon DEF ConfigDomain
        <4>5. KeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]]) 
          BY Zenon DEF BktInv
        <4> SUFFICES /\ c.state[arg[p].key] = NULL
                     /\ c.res[p] = ValOfKeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]]) 
          BY Zenon, <4>5 
        <4>6. c.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]])' THEN ValOfKeyInBktAtAddr(k, A[Hash[k]])' ELSE NULL]
          BY SPrimeRewrite, Zenon DEF SPrime
        <4>7. c.state[arg[p].key] = IF KeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]])' THEN ValOfKeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]])' ELSE NULL
          BY <4>6, <4>3, Zenon
        <4>8. newbkt[p] = A'[Hash[arg[p].key]]
          BY Zenon, HashDef, <4>3
        <4>9. MemLocs[A'[Hash[arg[p].key]]] = MemLocs[newbkt[p]]
          BY Zenon, <4>8
        <4>10. KeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]])' = KeyInBktAtAddr(arg[p].key, newbkt[p])
          BY Zenon, <4>8 DEF KeyInBktAtAddr
        <4>11. ~KeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]])'
          BY Zenon, <4>10 DEF NewBktInv
        <4>12. c.state[arg[p].key] = NULL
          BY Zenon, <4>7, <4>11
        <4>13. pc'[p] = "R5"
          BY Zenon
        <4>14. c.res[p] = r'[p]
          BY <4>13, SPrimeRewrite, RemDef, Zenon DEF SPrime
        <4>15. c.res[p] = ValOfKeyInBktAtAddr(arg[p].key, bucket[p])
          BY <4>14, Zenon DEF BktInv
        <4>16. c.res[p] = ValOfKeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]])
          BY <4>15, Zenon
        <4> QED
          BY <4>16, <4>12
      <3> QED
        BY <3>1, <3>2, <3>3, SingleDeltaEvolve
    <2>2. CASE A[Hash[arg[p].key]] # bucket[p]
      <3> USE <2>2
      <3> SUFFICES c \in S
        BY EmptySeqEvolve
      <3>1. c.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL]
        <4>1. c.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]])' THEN ValOfKeyInBktAtAddr(k, A[Hash[k]])' ELSE NULL]
          BY Zenon, SPrimeRewrite DEF SPrime
        <4>2. \A k \in KeyDomain : KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
          BY Zenon DEF KeyInBktAtAddr
        <4>3. \A k \in KeyDomain : ValOfKeyInBktAtAddr(k, A[Hash[k]])' = ValOfKeyInBktAtAddr(k, A[Hash[k]])
          <5> SUFFICES ASSUME NEW k \in KeyDomain
                        PROVE  ValOfKeyInBktAtAddr(k, A[Hash[k]])' = ValOfKeyInBktAtAddr(k, A[Hash[k]])
            OBVIOUS
          <5> bkt_arr == MemLocs'[A'[Hash[k]]]
          <5> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
          <5>1. ValOfKeyInBktAtAddr(k, A[Hash[k]])' = bkt_arr[idx].val
            BY DEF ValOfKeyInBktAtAddr
          <5>2. bkt_arr = MemLocs[A[Hash[k]]]
            BY Zenon
          <5> QED
            BY <5>1, <5>2, ZenonT(30) DEF ValOfKeyInBktAtAddr
        <4> QED
          BY <4>1, <4>2, <4>3
      <3>2. ASSUME NEW q \in ProcSet
            PROVE
                CASE pc[q] = RemainderID 
                    -> (c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT)
                  [] pc[q] = "F1"
                    -> (c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                  [] pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q]))
                  [] pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL)
                  [] pc[q] = "F3"
                    -> (c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q])
                  [] pc[q] \in {"I1", "I3", "I4"}
                    -> (c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                  [] pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q]))
                  [] pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                  [] pc[q] = "I5"
                    -> (c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q])
                  [] pc[q] \in {"U1", "U2", "U3", "U4"}
                    -> (c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                  [] pc[q] = "U5"
                    -> (c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q])
                  [] pc[q] \in {"R1", "R3", "R4"}
                    -> (c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                  [] pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT)
                  [] pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                    -> (c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL)
                  [] pc[q] = "R5"
                    -> (c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q])
        <4> USE <3>2
        <4>A. \A k \in KeyDomain : KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, bucket[q])'
          BY Zenon DEF KeyInBktAtAddr
        <4>B. \A k \in KeyDomain : ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, bucket[q])
          <5> SUFFICES ASSUME NEW k \in KeyDomain
                        PROVE  ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, bucket[q])
            OBVIOUS
          <5> bkt_arr == MemLocs'[bucket'[q]]
          <5> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
          <5>1. ValOfKeyInBktAtAddr(k, bucket[q])' = bkt_arr[idx].val
            BY DEF ValOfKeyInBktAtAddr
          <5>2. bkt_arr = MemLocs[bucket[q]]
            BY Zenon
          <5> QED
            BY <5>1, <5>2, ZenonT(30) DEF ValOfKeyInBktAtAddr
        <4>1. CASE pc[q] = RemainderID
          <5> USE <4>1
          <5> SUFFICES c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. pc'[q] = RemainderID
            BY RemDef, Zenon
          <5>2. c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>2. CASE pc[q] = "F1"
          <5> USE <4>2
          <5> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. pc'[q] = "F1"
            BY RemDef, Zenon
          <5>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>3. CASE pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>3
          <5> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            BY RemDef, Zenon
          <5>1. pc'[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <5>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5>3. arg[q].key = arg'[q].key /\ arg[q].key \in KeyDomain
            BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
          <5>4. c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            BY <5>2, <5>3, <4>B
          <5> QED
            BY <5>2, <5>4
        <4>4. CASE pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>4
          <5> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
            BY RemDef, Zenon
          <5>2. pc'[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>3. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
            BY <5>2,  SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>3
        <4>5. CASE pc[q] = "F3"
          <5> USE <4>5
          <5> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY RemDef, Zenon
          <5>1. pc'[q] = "F3"
            BY RemDef, Zenon
          <5>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2 
        <4>6. CASE pc[q] \in {"I1", "I3", "I4"}
          <5> USE <4>6
          <5> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. pc'[q] \in {"I1", "I3", "I4"}
            BY RemDef, Zenon
          <5>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2 
        <4>7. CASE pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>7
          <5> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            BY RemDef, Zenon
          <5>1. CASE p = q
            <6> USE <5>1
            <6>1. c.op[p] = "Insert" /\ c.arg[p] = arg[p] /\ c.res[p] = r'[p]
              BY SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6>2. r'[p] = ValOfKeyInBktAtAddr(arg[p].key, bucket[p])
              BY Zenon
            <6> QED
              BY <6>1, <6>2
          <5> SUFFICES ASSUME p # q
                        PROVE  c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            BY <5>1
          <5>2. pc'[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>3. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <5>2,  SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5>4. arg[q].key = arg'[q].key /\ arg[q].key \in KeyDomain
            BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
          <5>5. c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            BY <5>3, <5>4, <4>B
          <5> QED
            BY <5>3, <5>5
        <4>8. CASE pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>8
          <5> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. CASE p = q
            <6> USE <5>1
            <6>1. c.op[p] = "Insert" /\ c.arg[p] = arg[p] /\ c.res[p] = BOT
              BY SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>1
          <5> SUFFICES ASSUME p # q
                        PROVE  c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>1
          <5>2. pc'[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>3. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>2, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>3 
        <4>9. CASE pc[q] = "I5"
          <5> USE <4>9
          <5> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY RemDef, Zenon
          <5>1. pc'[q] = "I5"
            BY RemDef, Zenon 
          <5>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2 
        <4>10. CASE pc[q] \in {"U1", "U2", "U3", "U4"}
          <5> USE <4>10
          <5> SUFFICES c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. pc'[q] \in {"U1", "U2", "U3", "U4"}
            BY RemDef, Zenon
          <5>2. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>11. CASE pc[q] = "U5" 
          <5> USE <4>11
          <5> SUFFICES c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY RemDef, Zenon
          <5>1. pc'[q] = "U5"
            BY RemDef, Zenon
          <5>2. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>12. CASE pc[q] \in {"R1", "R3", "R4"}
          <5> USE <4>12
          <5> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. pc'[q] \in {"R1", "R3", "R4"}
            BY RemDef, Zenon
          <5>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>13. CASE pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>13
          <5> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY RemDef, Zenon
          <5>1. pc'[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>14. CASE pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>14
          <5> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
            BY RemDef, Zenon
          <5>1. pc'[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4>15. CASE pc[q] = "R5"
          <5> USE <4>15
          <5> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY RemDef, Zenon
          <5>1. pc'[q] = "R5" 
            BY RemDef, Zenon
          <5>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>2
        <4> QED
            BY RemDef, ZenonT(120),
                <4>1, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, 
                <4>10, <4>11, <4>12, <4>13, <4>14, <4>15
            DEF LineIDs
      <3> QED
        BY <3>1, <3>2, Zenon DEF S
    <2> QED
      BY <2>1, <2>2
  <1> QED
    BY Zenon, <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7,
       <1>8, <1>9, <1>10, <1>11, <1>12, <1>13, <1>14 DEF IntLines
                   
THEOREM StrongLinearizability == Spec => [][/\ IntermAction => S' \in SUBSET Evolve(S)
                                            /\ InvocnAction => S' \in SUBSET Evolve(Invoke(S, InvokerProc, LineIDtoOp(pc'[InvokerProc]), arg'[InvokerProc]))
                                            /\ ReturnAction => S' \in SUBSET Filter(Evolve(S), ReturnProc, ret'[ReturnProc])
                                            /\ Cardinality(S) = 1]_vars
  <1>1. Spec => [][Inv]_vars
    BY SpecInv, PTL
  <1>2. Inv => /\ IntermAction => S' \in SUBSET Evolve(S)
               /\ InvocnAction => S' \in SUBSET Evolve(Invoke(S, InvokerProc, LineIDtoOp(pc'[InvokerProc]), arg'[InvokerProc]))
               /\ ReturnAction => S' \in SUBSET Filter(Evolve(S), ReturnProc, ret'[ReturnProc])
               /\ Cardinality(S) = 1
    BY LinIntermediateLine, LinInvocationLine, LinReturnLine, LinSingleton DEF Inv
  <1>3. QED
    BY <1>1, <1>2, PTL

===========================================================================
\* Modification History
\* Last modified Fri Aug 16 17:02:31 EDT 2024 by uguryavuz
\* Created Thu Aug 08 09:43:24 EDT 2024 by uguryavuz
