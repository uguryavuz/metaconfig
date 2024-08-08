--------------------------- MODULE PHash_Proof2 ---------------------------
EXTENDS PHash_Proof1

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

InvL1 == S \in SUBSET P
InvWithL1 == Inv /\ InvL1

THEOREM L1Init == AInit => InvWithL1
  <1> SUFFICES ASSUME AInit
               PROVE  InvWithL1
    OBVIOUS
  <1>1. Inv
    BY InitInv
  <1>2. InvL1
    <2> SUFFICES ASSUME NEW c \in ConfigDomain,
                 c \in S
                 PROVE  c \in P
      BY Zenon DEF InvL1, S
    <2> SUFFICES /\ c.state = [k \in KeyDomain |-> NULL]
                 /\ c.op    = [p \in ProcSet   |-> BOT]
                 /\ c.arg   = [p \in ProcSet   |-> BOT]
                 /\ c.res   = [p \in ProcSet   |-> BOT]
      BY DEF ConfigDomain, AInit
    <2>1. \A k \in KeyDomain : ~KeyInBktAtAddr(k, A[Hash[k]])
      <3> SUFFICES ASSUME NEW k \in KeyDomain
                   PROVE  ~KeyInBktAtAddr(k, A[Hash[k]])
        OBVIOUS
      <3>1. A[Hash[k]] = NULL
        BY HashDef, Zenon DEF AInit, Init
      <3> QED
        BY <3>1, Zenon DEF KeyInBktAtAddr
    <2>2. c.state = [k \in KeyDomain |-> NULL]
      BY <2>1 DEF S
    <2>3. \A p \in ProcSet : pc[p] = RemainderID
      BY DEF AInit, Init
    <2>4. \A p \in ProcSet : c.op[p] = BOT /\ c.arg[p] = BOT /\ c.res[p] = BOT
      BY <2>3, RemDef, ZenonT(60) DEF S
    <2> QED
      BY <2>2, <2>4 DEF ConfigDomain
  <1>3. QED
    BY <1>1, <1>2 DEF InvWithL1

THEOREM L1Next == InvWithL1 /\ [Next]_vars => InvL1'
  <1> USE DEF InvWithL1, Inv, TOK
  <1> SUFFICES ASSUME InvWithL1 /\ [Next]_vars
               PROVE  InvL1'
    OBVIOUS
  <1>1. CASE Next
    <2> SUFFICES ASSUME NEW p \in ProcSet,
                        \/ L0(p)
                        \/ IntLine(p)
                        \/ RetLine(p)
                 PROVE  InvL1'
      BY <1>1 DEF Next
    <2>1. CASE L0(p)
      <3> SUFFICES ASSUME NEW op \in OpNames,
                          pc[p] = RemainderID,
                          pc' = [pc EXCEPT ![p] = OpToInvocLine(op)],
                          NEW new_arg \in ArgsOf(op),
                          /\ arg' = [arg EXCEPT ![p] = new_arg]
                          /\ P' = Evolve(Invoke(P, p, op, new_arg))
                   PROVE  InvL1'
        BY <2>1, Zenon DEF L0 
      <3> UNCHANGED <<A, MemLocs, AllocAddrs, bucket, newbkt, r, ret>>
        BY <2>1 DEF L0, vars, algvars
      <3> pc'[p] \in {"F1", "I1", "U1", "R1"}
        BY Zenon DEF OpNames, OpToInvocLine
      <3> SUFFICES ASSUME NEW c \in ConfigDomain,
                          c \in S'
                   PROVE  c \in P'
        BY Zenon DEF InvL1, S
      <3> DEFINE c_pred == [state |-> c.state,
                            op    |-> [c.op EXCEPT ![p] = BOT],
                            arg   |-> [c.arg EXCEPT ![p] = BOT],
                            res   |-> [c.res EXCEPT ![p] = BOT]]
      <3>1. c_pred \in ConfigDomain
        <4>1. c_pred.state \in StateDomain
          BY DEF ConfigDomain
        <4>2. c_pred.op \in [ProcSet -> OpDomain]
          BY DEF ConfigDomain, OpDomain
        <4>3. c_pred.arg \in [ProcSet -> ArgDomain]
          BY DEF ConfigDomain, ArgDomain
        <4>4. c_pred.res \in [ProcSet -> ResDomain]
          BY DEF ConfigDomain, ResDomain
        <4> QED
          BY <4>1, <4>2, <4>3, <4>4 DEF ConfigDomain
      <3>2. c_pred \in S
        <4>1. c_pred.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL]
          <5>1. c_pred.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL]
            <6>1. c_pred.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]])' THEN ValOfKeyInBktAtAddr(k, A[Hash[k]])' ELSE NULL]
              BY Zenon, SPrimeRewrite DEF SPrime
            <6>2. \A k \in KeyDomain : KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
              BY Zenon DEF KeyInBktAtAddr
            <6>3. \A k \in KeyDomain : ValOfKeyInBktAtAddr(k, A[Hash[k]])' = ValOfKeyInBktAtAddr(k, A[Hash[k]])
              <7> SUFFICES ASSUME NEW k \in KeyDomain
                           PROVE  ValOfKeyInBktAtAddr(k, A[Hash[k]])' = ValOfKeyInBktAtAddr(k, A[Hash[k]])
                OBVIOUS
              <7> bkt_arr == MemLocs'[A'[Hash[k]]]
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
              <7>1. ValOfKeyInBktAtAddr(k, A[Hash[k]])' = bkt_arr[idx].val
                BY DEF ValOfKeyInBktAtAddr
              <7>2. bkt_arr = MemLocs[A[Hash[k]]]
                BY Zenon
              <7> QED
                BY <7>1, <7>2, ZenonT(30) DEF ValOfKeyInBktAtAddr
            <6> QED
              BY <6>1, <6>2, <6>3
          <5> QED
            BY <5>1
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
            <6> SUFFICES c_pred.op[q] = BOT /\ c_pred.arg[q] = BOT /\ c_pred.res[q] = BOT
              BY <5>1, RemDef, Zenon
            <6>A. CASE q = p
              BY <6>A DEF ConfigDomain
            <6> SUFFICES ASSUME q # p
                         PROVE  c_pred.op[q] = BOT /\ c_pred.arg[q] = BOT /\ c_pred.res[q] = BOT
              BY <6>A
            <6>1. q # p
              BY <5>1, RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] = RemainderID
              BY <5>1, RemDef, Zenon
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
                BY <6>1, Zenon
              <7>4. ValOfKeyInBktAtAddr(arg[q].key, bucket[q]) =
                    MemLocs[bucket[q]][CHOOSE index \in 1..Len(MemLocs[bucket[q]]) : MemLocs[bucket[q]][index].key = arg[q].key].val
                BY Zenon DEF ValOfKeyInBktAtAddr
              <7>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q]) = bkt_arr[idx].val
                BY <7>2, <7>3, <7>4, Zenon
              <7> QED
                BY <7>1, <7>5
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
              BY <5>5, RemDef, Zenon
            <6>1. q # p
              BY RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] = "F3"
              BY <5>5, RemDef, Zenon
            <6>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
              BY <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
            <6> QED
              BY <6>2, <6>4
          <5>6. CASE pc[q] \in {"I1", "I3", "I4"}
            <6> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
              BY <5>6, RemDef, Zenon
            <6>1. q # p
              BY <5>6, RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] \in {"I1", "I3", "I4"}
              BY <5>6, RemDef, Zenon
            <6>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
              BY <6>1, <6>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
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
                BY <6>1, Zenon
              <7>4. ValOfKeyInBktAtAddr(arg[q].key, bucket[q]) =
                    MemLocs[bucket[q]][CHOOSE index \in 1..Len(MemLocs[bucket[q]]) : MemLocs[bucket[q]][index].key = arg[q].key].val
                BY Zenon DEF ValOfKeyInBktAtAddr
              <7>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q]) = bkt_arr[idx].val
                BY <7>2, <7>3, <7>4, Zenon
              <7> QED
                BY <7>1, <7>5
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
            <6> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
              BY <5>9, RemDef, Zenon
            <6>1. q # p
              BY <5>9, RemDef, Zenon
            <6>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
              BY <6>1
            <6>3. pc'[q] = "I5"
              BY <5>9, RemDef, Zenon
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
      <3>3. c_pred \in P
        BY <3>2 DEF InvL1
      <3>4. c_pred.op[p] = BOT /\ c_pred.arg[p] = BOT /\ c_pred.res[p] = BOT
        BY <3>1 DEF ConfigDomain
      <3>5. CASE op = "Find"
        <4> USE <3>5
        <4>1. pc'[p] = "F1"
          BY DEF OpToInvocLine
        <4>2. c.op[p] = op /\ c.arg[p] = arg'[p] /\ c.res[p] = BOT
          BY <4>1, Zenon, RemDef, SPrimeRewrite DEF SPrime
        <4>3. c.op = [c_pred.op EXCEPT ![p] = op]
          BY <4>2, Zenon DEF ConfigDomain
        <4>4. c.arg = [c_pred.arg EXCEPT ![p] = new_arg]
          BY <4>2, Zenon DEF ConfigDomain
        <4>5. c.res = [c_pred.res EXCEPT ![p] = BOT]
          BY <4>2, Zenon DEF ConfigDomain
        <4>6. c \in Invoke(P, p, op, new_arg)
          BY <3>3, <3>4, <4>3, <4>4, <4>5 DEF Invoke
        <4>7. c \in Evolve(Invoke(P, p, op, new_arg))
          BY <4>6, EmptySeqEvolve, Zenon
        <4> QED
          BY <4>7
      <3>6. CASE op = "Insert"
        <4> USE <3>6
        <4>1. pc'[p] = "I1"
          BY DEF OpToInvocLine
        <4>2. c.op[p] = op /\ c.arg[p] = arg'[p] /\ c.res[p] = BOT
          BY <4>1, Zenon, RemDef, SPrimeRewrite DEF SPrime
        <4>3. c.op = [c_pred.op EXCEPT ![p] = op]
          BY <4>2, Zenon DEF ConfigDomain
        <4>4. c.arg = [c_pred.arg EXCEPT ![p] = new_arg]
          BY <4>2, Zenon DEF ConfigDomain
        <4>5. c.res = [c_pred.res EXCEPT ![p] = BOT]
          BY <4>2, Zenon DEF ConfigDomain
        <4>6. c \in Invoke(P, p, op, new_arg)
          BY <3>3, <3>4, <4>3, <4>4, <4>5 DEF Invoke
        <4>7. c \in Evolve(Invoke(P, p, op, new_arg))
          BY <4>6, EmptySeqEvolve, Zenon
        <4> QED
          BY <4>7
      <3>7. CASE op = "Upsert"
        <4> USE <3>7
        <4>1. pc'[p] = "U1"
          BY DEF OpToInvocLine
        <4>2. c.op[p] = op /\ c.arg[p] = arg'[p] /\ c.res[p] = BOT
          BY <4>1, Zenon, RemDef, SPrimeRewrite DEF SPrime
        <4>3. c.op = [c_pred.op EXCEPT ![p] = op]
          BY <4>2, Zenon DEF ConfigDomain
        <4>4. c.arg = [c_pred.arg EXCEPT ![p] = new_arg]
          BY <4>2, Zenon DEF ConfigDomain
        <4>5. c.res = [c_pred.res EXCEPT ![p] = BOT]
          BY <4>2, Zenon DEF ConfigDomain
        <4>6. c \in Invoke(P, p, op, new_arg)
          BY <3>3, <3>4, <4>3, <4>4, <4>5 DEF Invoke
        <4>7. c \in Evolve(Invoke(P, p, op, new_arg))
          BY <4>6, EmptySeqEvolve, Zenon
        <4> QED
          BY <4>7
      <3>8. CASE op = "Remove"
        <4> USE <3>8
        <4>1. pc'[p] = "R1"
          BY DEF OpToInvocLine
        <4>2. c.op[p] = op /\ c.arg[p] = arg'[p] /\ c.res[p] = BOT
          BY <4>1, Zenon, RemDef, SPrimeRewrite DEF SPrime
        <4>3. c.op = [c_pred.op EXCEPT ![p] = op]
          BY <4>2, Zenon DEF ConfigDomain
        <4>4. c.arg = [c_pred.arg EXCEPT ![p] = new_arg]
          BY <4>2, Zenon DEF ConfigDomain
        <4>5. c.res = [c_pred.res EXCEPT ![p] = BOT]
          BY <4>2, Zenon DEF ConfigDomain
        <4>6. c \in Invoke(P, p, op, new_arg)
          BY <3>3, <3>4, <4>3, <4>4, <4>5 DEF Invoke
        <4>7. c \in Evolve(Invoke(P, p, op, new_arg))
          BY <4>6, EmptySeqEvolve, Zenon
        <4> QED
          BY <4>7
      <3> QED
        BY <3>5, <3>6, <3>7, <3>8 DEF OpNames
    <2>2. CASE IntLine(p)
      <3> SUFFICES ASSUME NEW Line \in IntLines(p), Line,
                          P' = Evolve(P)
                   PROVE  InvL1'
        BY <2>2 DEF IntLine
      <3>1. CASE Line = F1(p)
        <4> USE <3>1 DEF F1
        <4> SUFFICES ASSUME NEW c \in ConfigDomain,
                     c \in S'
                     PROVE c \in P'
          BY Zenon DEF InvL1, S
        <4> DEFINE c_pred == [state |-> c.state,
                              op    |-> c.op,
                              arg   |-> c.arg,
                              res   |-> [c.res EXCEPT ![p] = BOT]]
        <4>1. c_pred \in ConfigDomain
          <5>1. c_pred.state \in StateDomain
            BY DEF ConfigDomain
          <5>2. c_pred.op \in [ProcSet -> OpDomain]
            BY DEF ConfigDomain
          <5>3. c_pred.arg \in [ProcSet -> ArgDomain]
            BY DEF ConfigDomain
          <5>4. c_pred.res \in [ProcSet -> ResDomain]
            BY DEF ConfigDomain, ResDomain
          <5> QED
            BY <5>1, <5>2, <5>3, <5>4 DEF ConfigDomain
        <4>2. c_pred \in S
          <5>1. c_pred.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) 
                                                       THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) 
                                                       ELSE NULL]
            <6>1. c_pred.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]])'
                                                         THEN ValOfKeyInBktAtAddr(k, A[Hash[k]])'
                                                         ELSE NULL]
              BY SPrimeRewrite, Zenon DEF SPrime
            <6>2. \A k \in KeyDomain : /\ KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
                                       /\ ValOfKeyInBktAtAddr(k, A[Hash[k]]) = ValOfKeyInBktAtAddr(k, A[Hash[k]])'
              <7> SUFFICES ASSUME NEW k \in KeyDomain
                           PROVE  /\ KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
                                  /\ ValOfKeyInBktAtAddr(k, A[Hash[k]]) = ValOfKeyInBktAtAddr(k, A[Hash[k]])'
                OBVIOUS
              <7>1. KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
                BY Zenon DEF KeyInBktAtAddr
              <7>2. ValOfKeyInBktAtAddr(k, A[Hash[k]]) = ValOfKeyInBktAtAddr(k, A[Hash[k]])'
                <8> DEFINE bkt_arr == MemLocs'[A'[Hash[k]]]
                <8> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
                <8>1. ValOfKeyInBktAtAddr(k, A[Hash[k]])' = bkt_arr[idx].val
                  BY Zenon DEF ValOfKeyInBktAtAddr
                <8>2. bkt_arr = MemLocs[A[Hash[k]]]
                  BY Zenon
                <8>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
                  BY Zenon
                <8> QED
                  BY <8>1, <8>2, <8>3, Isa DEF ValOfKeyInBktAtAddr
              <7>3. QED
                BY <7>1, <7>2
            <6> QED
              BY <6>1, <6>2   
          <5>2. ASSUME NEW q \in ProcSet
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
            <6> USE <5>2
            <6>1. CASE pc[q] = RemainderID
              <7> SUFFICES c_pred.op[q] = BOT /\ c_pred.arg[q] = BOT /\ c_pred.res[q] = BOT
                BY <6>1, RemDef, Zenon
              <7>1. q # p
                BY <6>1, RemDef, Zenon
              <7>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                BY <7>1
              <7>3. pc'[q] = RemainderID
                BY <6>1, RemDef, Zenon
              <7>4. c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
                BY <7>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2, <7>4
            <6>2. CASE pc[q] = "F1"
              <7> USE <6>2
              <7> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
                BY RemDef, Zenon
              <7>1. CASE q = p
                <8> USE <7>1
                <8>1. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = BOT
                  BY Zenon DEF ConfigDomain
                <8>2. pc'[q] = "F2"
                  BY Zenon
                <8>3. c.op[q] = "Find" /\ c.arg[q] = arg[q]
                  BY <8>2, SPrimeRewrite, ZenonT(30), RemDef DEF SPrime
                <8> QED
                  BY <8>1, <8>3
              <7> SUFFICES ASSUME q # p
                           PROVE  c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
                BY <7>1
              <7>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                OBVIOUS
              <7>3. pc'[q] = "F1"
                BY RemDef, Zenon
              <7>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <7>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2, <7>4
            <6>3. CASE pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
              <7> USE <6>3
              <7> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                BY RemDef, Zenon
              <7>1. q # p
                BY RemDef, Zenon
              <7>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                BY <7>1
              <7>3. pc'[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                BY RemDef, Zenon DEF KeyInBktAtAddr
              <7>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
                BY <7>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                <8> DEFINE bkt_arr == MemLocs'[bucket'[q]]
                <8> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg'[q].key
                <8>1. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = bkt_arr[idx].val
                  BY Zenon DEF ValOfKeyInBktAtAddr
                <8>2. bkt_arr = MemLocs[bucket[q]]
                  BY Zenon
                <8>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
                  BY Zenon
                <8> QED
                  BY <8>1, <8>2, <8>3, Isa DEF ValOfKeyInBktAtAddr
              <7> QED
                BY <7>2, <7>4, <7>5
            <6>4. CASE pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
              <7> USE <6>4
              <7> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = NULL
                BY RemDef, Zenon
              <7>1. q # p
                BY RemDef, Zenon
              <7>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                BY <7>1
              <7>3. pc'[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                BY RemDef, Zenon DEF KeyInBktAtAddr
              <7>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                BY <7>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2, <7>4
            <6>5. CASE pc[q] = "F3"
              <7> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
                BY <6>5, RemDef, Zenon
              <7>1. q # p
                BY <6>5, RemDef, Zenon
              <7>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                BY <7>1
              <7>3. pc'[q] = "F3"
                BY <6>5, RemDef, Zenon
              <7>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY <7>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2, <7>4
            <6>6. CASE pc[q] \in {"I1", "I3", "I4"}
              <7> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
                BY <6>6, RemDef, Zenon
              <7>1. q # p
                BY <6>6, RemDef, Zenon
              <7>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                BY <7>1
              <7>3. pc'[q] \in {"I1", "I3", "I4"}
                BY <6>6, RemDef, Zenon
              <7>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <7>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2, <7>4
            <6>7. CASE pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
              <7> USE <6>7
              <7> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                BY RemDef, Zenon
              <7>1. q # p
                BY RemDef, Zenon
              <7>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                BY <7>1
              <7>3. pc'[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                BY RemDef, Zenon DEF KeyInBktAtAddr
              <7>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
                BY <7>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                <8> DEFINE bkt_arr == MemLocs'[bucket'[q]]
                <8> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg'[q].key
                <8>1. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = bkt_arr[idx].val
                  BY Zenon DEF ValOfKeyInBktAtAddr
                <8>2. bkt_arr = MemLocs[bucket[q]]
                  BY Zenon
                <8>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
                  BY Zenon
                <8> QED
                  BY <8>1, <8>2, <8>3, Isa DEF ValOfKeyInBktAtAddr
              <7> QED
                BY <7>2, <7>4, <7>5
            <6>8. CASE pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
              <7> USE <6>8
              <7> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
                BY RemDef, Zenon
              <7>1. q # p
                BY RemDef, Zenon
              <7>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                BY <7>1
              <7>3. pc'[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                BY RemDef, Zenon DEF KeyInBktAtAddr
              <7>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <7>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2, <7>4
            <6>9. CASE pc[q] = "I5"
              <7> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
                BY <6>9, RemDef, Zenon
              <7>1. q # p
                BY <6>9, RemDef, Zenon
              <7>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                BY <7>1
              <7>3. pc'[q] = "I5"
                BY <6>9, RemDef, Zenon
              <7>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY <7>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2, <7>4
            <6>10. CASE pc[q] \in {"U1", "U2", "U3", "U4"}
              <7> USE <6>10
              <7> SUFFICES c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
                BY RemDef, Zenon
              <7>1. q # p
                BY RemDef, Zenon
              <7>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                BY <7>1
              <7>3. pc'[q] \in {"U1", "U2", "U3", "U4"}
                BY RemDef, Zenon
              <7>4. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <7>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2, <7>4
            <6>11. CASE pc[q] = "U5"
              <7> USE <6>11
              <7> SUFFICES c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
                BY RemDef, Zenon
              <7>1. q # p
                BY RemDef, Zenon
              <7>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                BY <7>1
              <7>3. pc'[q] = "U5"
                BY RemDef, Zenon
              <7>4. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY <7>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2, <7>4
            <6>12. CASE pc[q] \in {"R1", "R3", "R4"}
              <7> USE <6>12
              <7> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
                BY RemDef, Zenon
              <7>1. q # p
                BY RemDef, Zenon
              <7>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                BY <7>1
              <7>3. pc'[q] \in {"R1", "R3", "R4"}
                BY RemDef, Zenon
              <7>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <7>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2, <7>4
            <6>13. CASE pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
              <7> USE <6>13
              <7> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
                BY RemDef, Zenon
              <7>1. q # p
                BY RemDef, Zenon
              <7>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                BY <7>1
              <7>3. pc'[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                BY RemDef, Zenon DEF KeyInBktAtAddr
              <7>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <7>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2, <7>4
            <6>14. CASE pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
              <7> USE <6>14
              <7> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = NULL
                BY RemDef, Zenon
              <7>1. q # p
                BY RemDef, Zenon
              <7>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                BY <7>1
              <7>3. pc'[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                BY RemDef, Zenon DEF KeyInBktAtAddr
              <7>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                BY <7>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2, <7>4
            <6>15. CASE pc[q] = "R5"
              <7> USE <6>15
              <7> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
                BY RemDef, Zenon
              <7>1. q # p
                BY RemDef, Zenon
              <7>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                BY <7>1
              <7>3. pc'[q] = "R5"
                BY RemDef, Zenon
              <7>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY <7>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2, <7>4
            <6> QED
              BY RemDef, ZenonT(120),
                 <6>1, <6>2, <6>3, <6>4, <6>5, <6>6, <6>7, <6>8, <6>9, 
                 <6>10, <6>11, <6>12, <6>13, <6>14, <6>15
              DEF LineIDs
          <5> QED
            BY <4>1, <5>1, <5>2, Zenon DEF S
        <4>3. c_pred \in P
          BY <4>2 DEF InvL1
        <4>4. Delta(c_pred, p, c)
          <5>1. c_pred.op[p] = "Find" /\ c_pred.arg[p] = arg[p] /\ c_pred.res[p] = BOT
            BY <4>2, RemDef, Zenon DEF S
          <5>2. c_pred.arg[p] \in ArgsOf("Find")
            BY <5>1, RemDef, Zenon DEF ArgsOf, LineIDtoOp
          <5> SUFFICES c.res = [c_pred.res EXCEPT ![p] = c_pred.state[c_pred.arg[p].key]]
            BY <5>1, <5>2 DEF Delta
          <5> SUFFICES c.res[p] = c_pred.state[c_pred.arg[p].key]
            BY <4>1, Zenon DEF ConfigDomain
          <5>3. KeyInBktAtAddr(arg[p].key, bucket[p])' = KeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]])
            BY Zenon DEF KeyInBktAtAddr
          <5>4. ValOfKeyInBktAtAddr(arg[p].key, bucket[p])' = ValOfKeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]])
            <6> DEFINE bkt_arr == MemLocs'[bucket'[p]]
            <6> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg'[p].key
            <6>1. ValOfKeyInBktAtAddr(arg[p].key, bucket[p])' = bkt_arr[idx].val
              BY Zenon DEF ValOfKeyInBktAtAddr
            <6> DEFINE bkt_arr2 == MemLocs[A[Hash[arg[p].key]]]
            <6> DEFINE idx2 == CHOOSE index \in 1..Len(bkt_arr2) : bkt_arr2[index].key = arg[p].key
            <6>2. ValOfKeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]]) = bkt_arr2[idx2].val
              BY Zenon DEF ValOfKeyInBktAtAddr
            <6>3. bkt_arr = bkt_arr2 /\ idx = idx2
              BY ZenonT(30)
            <6> QED
              BY <6>1, <6>2, <6>3
          <5>5. CASE KeyInBktAtAddr(arg[p].key, bucket[p])'
            <6> USE <5>5
            <6>1. c.res[p] = ValOfKeyInBktAtAddr(arg[p].key, bucket[p])'
              BY RemDef, Zenon DEF S
            <6>2. c.res[p] = ValOfKeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]])
              BY <5>4, <6>1
            <6>3. c_pred.arg[p].key \in KeyDomain /\ c_pred.arg[p] = arg[p]
              BY <5>1, <5>2 DEF ArgsOf
            <6>4. c_pred.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) 
                                             THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) 
                                             ELSE NULL]
              BY <4>2, Zenon DEF S
            <6>5. c_pred.state[c_pred.arg[p].key] = IF KeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]]) 
                                                       THEN ValOfKeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]]) 
                                                       ELSE NULL
              BY <6>3, <6>4, Zenon
            <6>6. c_pred.state[c_pred.arg[p].key] = ValOfKeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]]) 
              BY <5>3, <6>5
            <6> QED
              BY <6>2, <6>6
          <5>6. CASE ~KeyInBktAtAddr(arg[p].key, bucket[p])'
            <6> USE <5>6
            <6>1. c.res[p] = NULL
              BY RemDef, Zenon DEF S
            <6>2. c_pred.arg[p].key \in KeyDomain /\ c_pred.arg[p] = arg[p]
              BY <5>1, <5>2 DEF ArgsOf
            <6>3. c_pred.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) 
                                             THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) 
                                             ELSE NULL]
              BY <4>2, Zenon DEF S
            <6>4. c_pred.state[c_pred.arg[p].key] = IF KeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]]) 
                                                       THEN ValOfKeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]]) 
                                                       ELSE NULL
              BY <6>2, <6>3, Zenon
            <6>5. c_pred.state[c_pred.arg[p].key] = NULL 
              BY <5>3, <6>4
            <6> QED
              BY <6>1, <6>5
          <5> QED 
            BY <5>5, <5>6
        <4>5. c \in Evolve(P)
          BY <4>1, <4>3, <4>4, SingleDeltaEvolve
        <4> QED
          BY <4>5
      <3>2. CASE Line = F2(p)
        <4> USE <3>2 DEF F2
        <4> SUFFICES ASSUME NEW c \in ConfigDomain,
                            c \in S'
                     PROVE  c \in P'
          BY Zenon DEF InvL1, S
        <4>1. c \in S
          <5>1. c.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL]
            <6>1. c.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]])' THEN ValOfKeyInBktAtAddr(k, A[Hash[k]])' ELSE NULL]
              BY Zenon, SPrimeRewrite DEF SPrime
            <6>2. \A k \in KeyDomain : KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
              BY Zenon DEF KeyInBktAtAddr
            <6>3. \A k \in KeyDomain : ValOfKeyInBktAtAddr(k, A[Hash[k]])' = ValOfKeyInBktAtAddr(k, A[Hash[k]])
              <7> SUFFICES ASSUME NEW k \in KeyDomain
                           PROVE  ValOfKeyInBktAtAddr(k, A[Hash[k]])' = ValOfKeyInBktAtAddr(k, A[Hash[k]])
                OBVIOUS
              <7> bkt_arr == MemLocs'[A'[Hash[k]]]
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
              <7>1. ValOfKeyInBktAtAddr(k, A[Hash[k]])' = bkt_arr[idx].val
                BY DEF ValOfKeyInBktAtAddr
              <7>2. bkt_arr = MemLocs[A[Hash[k]]]
                BY Zenon
              <7> QED
                BY <7>1, <7>2, ZenonT(30) DEF ValOfKeyInBktAtAddr
            <6> QED
              BY <6>1, <6>2, <6>3
          <5>2. ASSUME NEW q \in ProcSet
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
            <6> USE <5>2
            <6>A. \A k \in KeyDomain : KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, bucket[q])'
              BY Zenon DEF KeyInBktAtAddr
            <6>B. \A k \in KeyDomain : ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, bucket[q])
              <7> SUFFICES ASSUME NEW k \in KeyDomain
                           PROVE  ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, bucket[q])
                OBVIOUS
              <7> bkt_arr == MemLocs'[bucket'[q]]
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
              <7>1. ValOfKeyInBktAtAddr(k, bucket[q])' = bkt_arr[idx].val
                BY DEF ValOfKeyInBktAtAddr
              <7>2. bkt_arr = MemLocs[bucket[q]]
                BY Zenon
              <7> QED
                BY <7>1, <7>2, ZenonT(30) DEF ValOfKeyInBktAtAddr
            <6>1. CASE pc[q] = RemainderID
              <7> USE <6>1
              <7> SUFFICES c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
                BY RemDef, Zenon
              <7>1. pc'[q] = RemainderID
                BY RemDef, Zenon
              <7>2. c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2
            <6>2. CASE pc[q] = "F1"
              <7> USE <6>2
              <7> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY RemDef, Zenon
              <7>1. pc'[q] = "F1"
                BY RemDef, Zenon
              <7>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2
            <6>3. CASE pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
              <7> USE <6>3
              <7> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                BY RemDef, Zenon
              <7>1. CASE q = p
                <8> USE <7>1
                <8>1. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r'[q]
                  BY SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                  BY <8>1, Zenon
                <8> QED
                  BY <8>2
              <7> SUFFICES ASSUME q # p
                           PROVE  c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                BY <7>1
              <7>2. pc'[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                BY RemDef, Zenon DEF KeyInBktAtAddr
              <7>3. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
                BY <7>2,  SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7>4. arg[q].key = arg'[q].key /\ arg[q].key \in KeyDomain
                BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
              <7>5. c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                BY <7>3, <7>4, <6>B
              <7> QED
                BY <7>3, <7>5
            <6>4. CASE pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
              <7> USE <6>4
              <7> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                BY RemDef, Zenon
              <7>1. CASE q = p
                <8> USE <7>1
                <8>1. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r'[q]
                  BY SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                  BY <8>1, Zenon
                <8> QED
                  BY <8>2
              <7> SUFFICES ASSUME q # p
                           PROVE  c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                BY <7>1
              <7>2. pc'[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                BY RemDef, Zenon DEF KeyInBktAtAddr
              <7>3. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                BY <7>2,  SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>3
            <6>5. CASE pc[q] = "F3"
              <7> USE <6>5
              <7> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY RemDef, Zenon
              <7>1. pc'[q] = "F3"
                BY RemDef, Zenon
              <7>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2 
            <6>6. CASE pc[q] \in {"I1", "I3", "I4"}
              <7> USE <6>6
              <7> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY RemDef, Zenon
              <7>1. pc'[q] \in {"I1", "I3", "I4"}
                BY RemDef, Zenon
              <7>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2 
            <6>7. CASE pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
              <7> USE <6>7
              <7> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                BY RemDef, Zenon
              <7>2. pc'[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                BY RemDef, Zenon DEF KeyInBktAtAddr
              <7>3. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
                BY <7>2,  SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7>4. arg[q].key = arg'[q].key /\ arg[q].key \in KeyDomain
                BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
              <7>5. c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                BY <7>3, <7>4, <6>B
              <7> QED
                BY <7>3, <7>5
            <6>8. CASE pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
              <7> USE <6>8
              <7> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY RemDef, Zenon
              <7>1. pc'[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                BY RemDef, Zenon DEF KeyInBktAtAddr
              <7>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2 
            <6>9. CASE pc[q] = "I5"
              <7> USE <6>9
              <7> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY RemDef, Zenon
              <7>1. pc'[q] = "I5"
                BY RemDef, Zenon 
              <7>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2 
            <6>10. CASE pc[q] \in {"U1", "U2", "U3", "U4"}
              <7> USE <6>10
              <7> SUFFICES c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY RemDef, Zenon
              <7>1. pc'[q] \in {"U1", "U2", "U3", "U4"}
                BY RemDef, Zenon
              <7>2. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2
            <6>11. CASE pc[q] = "U5" 
              <7> USE <6>11
              <7> SUFFICES c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY RemDef, Zenon
              <7>1. pc'[q] = "U5"
                BY RemDef, Zenon
              <7>2. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2
            <6>12. CASE pc[q] \in {"R1", "R3", "R4"}
              <7> USE <6>12
              <7> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY RemDef, Zenon
              <7>1. pc'[q] \in {"R1", "R3", "R4"}
                BY RemDef, Zenon
              <7>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2
            <6>13. CASE pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
              <7> USE <6>13
              <7> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY RemDef, Zenon
              <7>1. pc'[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                BY RemDef, Zenon DEF KeyInBktAtAddr
              <7>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2
            <6>14. CASE pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
              <7> USE <6>14
              <7> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                BY RemDef, Zenon
              <7>1. pc'[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                BY RemDef, Zenon DEF KeyInBktAtAddr
              <7>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2
            <6>15. CASE pc[q] = "R5"
              <7> USE <6>15
              <7> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY RemDef, Zenon
              <7>1. pc'[q] = "R5" 
                BY RemDef, Zenon
              <7>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2
            <6> QED
                BY RemDef, ZenonT(120),
                    <6>1, <6>2, <6>3, <6>4, <6>5, <6>6, <6>7, <6>8, <6>9, 
                    <6>10, <6>11, <6>12, <6>13, <6>14, <6>15
                DEF LineIDs
          <5> QED
            BY <5>1, <5>2, Zenon DEF S
        <4>2. c \in P
          BY <4>1 DEF InvL1
        <4>3. c \in Evolve(P)
          BY <4>2, EmptySeqEvolve
        <4> QED
          BY <4>3
      <3>3. CASE Line = I1(p)
        <4> USE <3>3 DEF I1
        <4> SUFFICES ASSUME NEW c \in ConfigDomain,
                            c \in S'
                     PROVE  c \in P'
          BY Zenon DEF InvL1, S
        <4>1. CASE ~KeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]])
          <5> USE <4>1
          <5>1. c \in S
            <6>A. \A k \in KeyDomain : KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
              BY Zenon, HashDef DEF KeyInBktAtAddr
            <6>B. \A k \in KeyDomain : ValOfKeyInBktAtAddr(k, A[Hash[k]]) = ValOfKeyInBktAtAddr(k, A[Hash[k]])'
              <7> SUFFICES ASSUME NEW k \in KeyDomain
                           PROVE  ValOfKeyInBktAtAddr(k, A[Hash[k]]) = ValOfKeyInBktAtAddr(k, A[Hash[k]])'
                OBVIOUS
              <7> DEFINE bkt_arr == MemLocs'[A'[Hash[k]]]
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
              <7>1. ValOfKeyInBktAtAddr(k, A[Hash[k]])' = bkt_arr[idx].val
                BY Zenon DEF ValOfKeyInBktAtAddr
              <7>2. bkt_arr = MemLocs[A[Hash[k]]] /\ A'[Hash[k]] = A[Hash[k]]
                BY Zenon
              <7> QED
                BY <7>1, <7>2 DEF ValOfKeyInBktAtAddr
            <6>1. c.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) 
                                                    THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) 
                                                    ELSE NULL]
              <7>1. c.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]])' THEN ValOfKeyInBktAtAddr(k, A[Hash[k]])' ELSE NULL]
                BY SPrimeRewrite, Zenon DEF SPrime
              <7> QED
                BY <6>A, <6>B, <7>1
            <6>2. ASSUME NEW q \in ProcSet
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
              <7> USE <6>2
              <7>1. CASE pc[q] = RemainderID
                <8> USE <7>1
                <8> SUFFICES c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
                  BY RemDef, Zenon
                <8>1. pc'[q] = RemainderID
                  BY RemDef, Zenon
                <8>2. c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
                  BY <8>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2
              <7>2. CASE pc[q] = "F1"
                <8> USE <7>2
                <8> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY RemDef, Zenon
                <8>1. pc'[q] = "F1"
                  BY RemDef, Zenon
                <8>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY <8>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2    
              <7>3. CASE pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                <8> USE <7>3
                <8> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                  BY RemDef, Zenon
                <8>1. pc'[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY RemDef, Zenon DEF KeyInBktAtAddr
                <8>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY <8>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8>3. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                  <9> DEFINE bkt_arr == MemLocs'[bucket'[q]]
                  <9> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg'[q].key
                  <9>1. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = bkt_arr[idx].val
                    BY Zenon DEF ValOfKeyInBktAtAddr
                  <9>2. bkt_arr = MemLocs[bucket[q]]
                    BY Zenon
                  <9>3. arg'[q].key = arg[q].key
                    BY Zenon
                  <9> QED
                    BY <9>1, <9>2, <9>3, Isa DEF ValOfKeyInBktAtAddr
                <8> QED
                  BY <8>2, <8>3
              <7>4. CASE pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                <8> USE <7>4
                <8> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                  BY RemDef, Zenon
                <8>1. pc'[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY RemDef, Zenon DEF KeyInBktAtAddr
                <8>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                  BY <8>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2
              <7>5. CASE pc[q] = "F3"
                <8> USE <7>5
                <8> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                  BY RemDef, Zenon
                <8>1. pc'[q] = "F3"
                  BY RemDef, Zenon
                <8>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                  BY <8>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2 
              <7>6. CASE pc[q] \in {"I1", "I3", "I4"}
                <8> USE <7>6
                <8> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY RemDef, Zenon
                <8>1. CASE p = q
                  <9> USE <8>1
                  <9>1. arg[q].key = arg'[q].key /\ bucket'[q] = A[Hash[arg[q].key]]
                    BY Zenon
                  <9>2. pc'[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                    BY <9>1, Zenon DEF KeyInBktAtAddr
                  <9>3. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                    BY <9>2, SPrimeRewrite, Zenon, RemDef DEF SPrime
                  <9> QED
                    BY <9>3
                <8> SUFFICES ASSUME p # q
                             PROVE  c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY <8>1
                <8>2. pc'[q] \in {"I1", "I3", "I4"}
                  BY RemDef, Zenon
                <8>3. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY <8>2, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>3 
              <7>7. CASE pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                <8> USE <7>7
                <8> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                  BY RemDef, Zenon
                <8>1. pc'[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY RemDef, Zenon DEF KeyInBktAtAddr
                <8>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY <8>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8>3. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                  <9> DEFINE bkt_arr == MemLocs'[bucket'[q]]
                  <9> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg'[q].key
                  <9>1. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = bkt_arr[idx].val
                    BY Zenon DEF ValOfKeyInBktAtAddr
                  <9>2. bkt_arr = MemLocs[bucket[q]]
                    BY Zenon
                  <9>3. arg'[q].key = arg[q].key
                    BY Zenon
                  <9> QED
                    BY <9>1, <9>2, <9>3, Isa DEF ValOfKeyInBktAtAddr
                <8> QED
                  BY <8>2, <8>3
              <7>8. CASE pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                <8> USE <7>8
                <8> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY RemDef, Zenon
                <8>1. pc'[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY RemDef, Zenon DEF KeyInBktAtAddr
                <8>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY <8>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2
              <7>9. CASE pc[q] = "I5"
                <8> USE <7>9
                <8> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                  BY RemDef, Zenon
                <8>1. pc'[q] = "I5"
                  BY RemDef, Zenon
                <8>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                  BY <8>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2 
              <7>10. CASE pc[q] \in {"U1", "U2", "U3", "U4"}
                <8> USE <7>10
                <8> SUFFICES c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY RemDef, Zenon
                <8>1. pc'[q] \in {"U1", "U2", "U3", "U4"}
                  BY RemDef, Zenon
                <8>2. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY <8>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2 
              <7>11. CASE pc[q] = "U5" 
                <8> USE <7>11
                <8> SUFFICES c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                  BY RemDef, Zenon
                <8>1. pc'[q] = "U5"
                  BY RemDef, Zenon
                <8>2. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                  BY <8>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2 
              <7>12. CASE pc[q] \in {"R1", "R3", "R4"}
                <8> USE <7>12
                <8> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY RemDef, Zenon
                <8>1. pc'[q] \in {"R1", "R3", "R4"}
                  BY RemDef, Zenon
                <8>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY <8>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2 
              <7>13. CASE pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                <8> USE <7>13
                <8> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY RemDef, Zenon
                <8>1. pc'[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY RemDef, Zenon DEF KeyInBktAtAddr
                <8>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY <8>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2
              <7>14. CASE pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                <8> USE <7>14
                <8> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                  BY RemDef, Zenon
                <8>1. pc'[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY RemDef, Zenon DEF KeyInBktAtAddr
                <8>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                  BY <8>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2
              <7>15. CASE pc[q] = "R5"
                <8> USE <7>15
                <8> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                  BY RemDef, Zenon
                <8>1. pc'[q] = "R5"
                  BY RemDef, Zenon
                <8>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                  BY <8>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2 
              <7> QED
                BY RemDef, ZenonT(120),
                   <7>1, <7>2, <7>3, <7>4, <7>5, <7>6, <7>7, <7>8, <7>9, 
                   <7>10, <7>11, <7>12, <7>13, <7>14, <7>15
                DEF LineIDs
            <6> QED
              BY <6>1, <6>2, Zenon DEF S
          <5>2. c \in P
            BY <5>1 DEF InvL1
          <5>3. c \in Evolve(P)
            BY <5>2, EmptySeqEvolve
          <5> QED
            BY <5>3
        <4>2. CASE KeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]])
          <5> USE <4>2
          <5> c_pred == [state |-> c.state,
                         op    |-> c.op,
                         arg   |-> c.arg,
                         res   |-> [c.res EXCEPT ![p] = BOT]]
          <5>1. c_pred \in ConfigDomain
            <6>1. c_pred.state \in StateDomain
              BY DEF ConfigDomain
            <6>2. c_pred.op \in [ProcSet -> OpDomain]
              BY DEF ConfigDomain
            <6>3. c_pred.arg \in [ProcSet -> ArgDomain]
              BY DEF ConfigDomain
            <6>4. c_pred.res \in [ProcSet -> ResDomain]
              BY DEF ConfigDomain, ResDomain
            <6> QED
              BY <6>1, <6>2, <6>3, <6>4 DEF ConfigDomain
          <5>2. c_pred \in S
            <6>1. c_pred.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL]
              <7>1. c_pred.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]])'
                                                           THEN ValOfKeyInBktAtAddr(k, A[Hash[k]])'
                                                           ELSE NULL]
                BY SPrimeRewrite, Zenon DEF SPrime
              <7>2. \A k \in KeyDomain : /\ KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
                                         /\ ValOfKeyInBktAtAddr(k, A[Hash[k]]) = ValOfKeyInBktAtAddr(k, A[Hash[k]])'
                <8> SUFFICES ASSUME NEW k \in KeyDomain
                             PROVE  /\ KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
                                    /\ ValOfKeyInBktAtAddr(k, A[Hash[k]]) = ValOfKeyInBktAtAddr(k, A[Hash[k]])'
                  OBVIOUS
                <8>1. KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
                  BY Zenon DEF KeyInBktAtAddr
                <8>2. ValOfKeyInBktAtAddr(k, A[Hash[k]]) = ValOfKeyInBktAtAddr(k, A[Hash[k]])'
                  <9> DEFINE bkt_arr == MemLocs'[A'[Hash[k]]]
                  <9> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
                  <9>1. ValOfKeyInBktAtAddr(k, A[Hash[k]])' = bkt_arr[idx].val
                    BY Zenon DEF ValOfKeyInBktAtAddr
                  <9>2. bkt_arr = MemLocs[A[Hash[k]]]
                    BY Zenon
                  <9>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
                    BY Zenon
                  <9> QED
                    BY <9>1, <9>2, <9>3, Isa DEF ValOfKeyInBktAtAddr
                <8>3. QED
                  BY <8>1, <8>2
              <7> QED
                BY <7>1, <7>2 
            <6>2. ASSUME NEW q \in ProcSet
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
              <7> USE <6>2
              <7>1. CASE pc[q] = RemainderID
                <8> USE <7>1
                <8> SUFFICES c_pred.op[q] = BOT /\ c_pred.arg[q] = BOT /\ c_pred.res[q] = BOT
                  BY RemDef, Zenon
                <8>1. q # p
                  BY RemDef, Zenon
                <8>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                  BY <8>1
                <8>3. pc'[q] = RemainderID
                  BY RemDef, Zenon
                <8>4. c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
                  BY <8>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2, <8>4
              <7>2. CASE pc[q] = "F1"
                <8> USE <7>2
                <8> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
                  BY RemDef, Zenon
                <8>1. q # p
                  BY RemDef, Zenon
                <8>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                  BY <8>1
                <8>3. pc'[q] = "F1"
                  BY RemDef, Zenon
                <8>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY <8>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2, <8>4
              <7>3. CASE pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                <8> USE <7>3
                <8> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                  BY RemDef, Zenon
                <8>1. q # p
                  BY RemDef, Zenon
                <8>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                  BY <8>1
                <8>3. pc'[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY RemDef, Zenon DEF KeyInBktAtAddr
                <8>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY <8>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                  <9> DEFINE bkt_arr == MemLocs'[bucket'[q]]
                  <9> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg'[q].key
                  <9>1. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = bkt_arr[idx].val
                    BY Zenon DEF ValOfKeyInBktAtAddr
                  <9>2. bkt_arr = MemLocs[bucket[q]]
                    BY Zenon
                  <9>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
                    BY Zenon
                  <9> QED
                    BY <9>1, <9>2, <9>3, Isa DEF ValOfKeyInBktAtAddr
                <8> QED
                  BY <8>2, <8>4, <8>5
              <7>4. CASE pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                <8> USE <7>4
                <8> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = NULL
                  BY RemDef, Zenon
                <8>1. q # p
                  BY RemDef, Zenon
                <8>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                  BY <8>1
                <8>3. pc'[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY RemDef, Zenon DEF KeyInBktAtAddr
                <8>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                  BY <8>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2, <8>4
              <7>5. CASE pc[q] = "F3" 
                <8> USE <7>5
                <8> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
                  BY RemDef, Zenon
                <8>1. q # p
                  BY RemDef, Zenon
                <8>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                  BY <8>1
                <8>3. pc'[q] = "F3"
                  BY RemDef, Zenon
                <8>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                  BY <8>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2, <8>4
              <7>6. CASE pc[q] \in {"I1", "I3", "I4"}
                <8> USE <7>6
                <8> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
                  BY RemDef, Zenon
                <8>A. CASE p = q
                  <9> USE <8>A
                  <9>1. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = BOT
                    BY <5>1 DEF ConfigDomain
                  <9>2. pc'[q] = "I2"
                    BY Zenon
                  <9>3. c.op[q] = "Insert" /\ c.arg[p] = arg[q]
                    BY <9>2, SPrimeRewrite, Zenon, RemDef DEF SPrime
                  <9> QED
                    BY <9>1, <9>3
                <8> SUFFICES ASSUME p # q
                             PROVE  c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
                  BY <8>A
                <8>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                  OBVIOUS
                <8>3. pc'[q] \in {"I1", "I3", "I4"}
                  BY RemDef, Zenon
                <8>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY <8>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2, <8>4
              <7>7. CASE pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                <8> USE <7>7
                <8> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                  BY RemDef, Zenon
                <8>1. q # p
                  BY RemDef, Zenon
                <8>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                  BY <8>1
                <8>3. pc'[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY RemDef, Zenon DEF KeyInBktAtAddr
                <8>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY <8>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                  <9> DEFINE bkt_arr == MemLocs'[bucket'[q]]
                  <9> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg'[q].key
                  <9>1. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = bkt_arr[idx].val
                    BY Zenon DEF ValOfKeyInBktAtAddr
                  <9>2. bkt_arr = MemLocs[bucket[q]]
                    BY Zenon
                  <9>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
                    BY Zenon
                  <9> QED
                    BY <9>1, <9>2, <9>3, Isa DEF ValOfKeyInBktAtAddr
                <8> QED
                  BY <8>2, <8>4, <8>5
              <7>8. CASE pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                <8> USE <7>8
                <8> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
                  BY RemDef, Zenon
                <8>1. q # p
                  BY RemDef, Zenon
                <8>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                  BY <8>1
                <8>3. pc'[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY RemDef, Zenon DEF KeyInBktAtAddr
                <8>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY <8>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2, <8>4
              <7>9. CASE pc[q] = "I5"
                <8> USE <7>9
                <8> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
                  BY RemDef, Zenon
                <8>1. q # p
                  BY RemDef, Zenon
                <8>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                  BY <8>1
                <8>3. pc'[q] = "I5"
                  BY RemDef, Zenon
                <8>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                  BY <8>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2, <8>4
              <7>10. CASE pc[q] \in {"U1", "U2", "U3", "U4"}
                <8> USE <7>10
                <8> SUFFICES c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
                  BY RemDef, Zenon
                <8>1. q # p
                  BY RemDef, Zenon
                <8>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                  BY <8>1
                <8>3. pc'[q] \in {"U1", "U2", "U3", "U4"}
                  BY RemDef, Zenon
                <8>4. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY <8>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2, <8>4
              <7>11. CASE pc[q] = "U5" 
                <8> USE <7>11
                <8> SUFFICES c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
                  BY RemDef, Zenon
                <8>1. q # p
                  BY RemDef, Zenon
                <8>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                  BY <8>1
                <8>3. pc'[q] = "U5"
                  BY RemDef, Zenon
                <8>4. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                  BY <8>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2, <8>4
              <7>12. CASE pc[q] \in {"R1", "R3", "R4"}
                <8> USE <7>12
                <8> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
                  BY RemDef, Zenon
                <8>1. q # p
                  BY RemDef, Zenon
                <8>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                  BY <8>1
                <8>3. pc'[q] \in {"R1", "R3", "R4"}
                  BY RemDef, Zenon
                <8>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY <8>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2, <8>4
              <7>13. CASE pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q]) 
                <8> USE <7>13
                <8> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
                  BY RemDef, Zenon
                <8>1. q # p
                  BY RemDef, Zenon
                <8>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                  BY <8>1
                <8>3. pc'[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY RemDef, Zenon DEF KeyInBktAtAddr
                <8>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY <8>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2, <8>4              
              <7>14. CASE pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                <8> USE <7>14
                <8> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = NULL
                  BY RemDef, Zenon
                <8>1. q # p
                  BY RemDef, Zenon
                <8>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                  BY <8>1
                <8>3. pc'[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY RemDef, Zenon DEF KeyInBktAtAddr
                <8>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                  BY <8>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2, <8>4    
              <7>15. CASE pc[q] = "R5"
                <8> USE <7>15
                <8> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
                  BY RemDef, Zenon
                <8>1. q # p
                  BY RemDef, Zenon
                <8>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                  BY <8>1
                <8>3. pc'[q] = "R5"
                  BY RemDef, Zenon
                <8>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                  BY <8>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2, <8>4
              <7> QED
                  BY RemDef, ZenonT(120),
                     <7>1, <7>2, <7>3, <7>4, <7>5, <7>6, <7>7, <7>8, <7>9, 
                     <7>10, <7>11, <7>12, <7>13, <7>14, <7>15
                  DEF LineIDs
            <6> QED
              BY <5>1, <6>1, <6>2, Zenon DEF S
          <5>3. c_pred \in P
            BY <5>2 DEF InvL1
          <5>4. Delta(c_pred, p, c)
            <6>1. c_pred.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL]
              BY <5>1, <5>2, Zenon DEF S
            <6>2. c_pred.op[p] = "Insert" /\ c_pred.arg[p] = arg[p] /\ c_pred.res[p] = BOT
              BY <5>1, <5>2, Zenon, RemDef DEF S
            <6>3. arg[p] \in ArgsOf("Insert") /\ arg[p].key \in KeyDomain
              BY RemDef, Zenon DEF ArgsOf, LineIDtoOp 
            <6>4. c_pred.state[c_pred.arg[p].key] = ValOfKeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]])
              BY <6>1, <6>2, <6>3, Zenon
            <6>5. ValOfKeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]]) \in ValDomain
              <7> DEFINE bkt_arr == MemLocs[A[Hash[arg[p].key]]]
              <7>1. A[Hash[arg[p].key]] # NULL
                BY DEF KeyInBktAtAddr
              <7>2. bkt_arr \in Seq([key: KeyDomain, val: ValDomain])
                BY HashDef, <6>3, <7>1, Zenon
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[p].key
              <7>3. idx \in 1..Len(bkt_arr)
                BY Zenon DEF KeyInBktAtAddr
              <7>4. bkt_arr[idx] \in [key: KeyDomain, val: ValDomain]
                BY Zenon, ElementOfSeq, <7>2, <7>3
              <7>5. bkt_arr[idx].val \in ValDomain
                BY Zenon, <7>4
              <7>6. ValOfKeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]]) = bkt_arr[idx].val
                BY DEF ValOfKeyInBktAtAddr
              <7> QED
                BY Zenon, <7>5, <7>6
            <6>6. ValOfKeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]]) # NULL
              BY <6>5, NULLDef
            <6> SUFFICES c.res = [c_pred.res EXCEPT ![p] = c_pred.state[c_pred.arg[p].key]]
              BY <6>2, <6>3, <6>4, <6>6, Zenon DEF Delta
            <6> SUFFICES c.res[p] = c_pred.state[c_pred.arg[p].key]
              BY <5>2, Zenon DEF ConfigDomain, S
            <6>A. pc'[p] = "I2" /\ KeyInBktAtAddr(arg[p].key, bucket[p])'
              BY Zenon DEF KeyInBktAtAddr
            <6>B. c.res[p] = ValOfKeyInBktAtAddr(arg[p].key, bucket[p])'
              BY <6>A, SPrimeRewrite, RemDef, Zenon DEF SPrime
            <6>C. ValOfKeyInBktAtAddr(arg[p].key, bucket[p])' = ValOfKeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]])
              <7> DEFINE bkt_arr == MemLocs'[bucket'[p]]
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg'[p].key
              <7>1. ValOfKeyInBktAtAddr(arg[p].key, bucket[p])' = bkt_arr[idx].val
                BY Zenon DEF ValOfKeyInBktAtAddr
              <7> DEFINE bkt_arr2 == MemLocs[A[Hash[arg[p].key]]]
              <7> DEFINE idx2 == CHOOSE index \in 1..Len(bkt_arr2) : bkt_arr2[index].key = arg[p].key
              <7>2. ValOfKeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]]) = bkt_arr2[idx2].val
                BY Zenon DEF ValOfKeyInBktAtAddr
              <7>3. bkt_arr = bkt_arr2 /\ idx = idx2
                BY ZenonT(30)
              <7> QED
                BY <7>1, <7>2, <7>3, Zenon
            <6> QED
              BY <6>B, <6>C, <6>4, Zenon
          <5>5. c \in Evolve(P)
            BY <5>1, <5>3, <5>4, SingleDeltaEvolve
          <5> QED
            BY <5>5
        <4> QED
          BY <4>1, <4>2
      <3>4. CASE Line = I2(p)
        <4> USE <3>4 DEF I2
        <4> SUFFICES ASSUME NEW c \in ConfigDomain,
                            c \in S'
                     PROVE  c \in P'
          BY Zenon DEF InvL1, S
        <4>1. c \in S
          <5>1. c.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL]
            <6>1. c.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]])' THEN ValOfKeyInBktAtAddr(k, A[Hash[k]])' ELSE NULL]
              BY Zenon, SPrimeRewrite DEF SPrime
            <6>2. \A k \in KeyDomain : KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
              BY Zenon DEF KeyInBktAtAddr
            <6>3. \A k \in KeyDomain : ValOfKeyInBktAtAddr(k, A[Hash[k]])' = ValOfKeyInBktAtAddr(k, A[Hash[k]])
              <7> SUFFICES ASSUME NEW k \in KeyDomain
                           PROVE  ValOfKeyInBktAtAddr(k, A[Hash[k]])' = ValOfKeyInBktAtAddr(k, A[Hash[k]])
                OBVIOUS
              <7> bkt_arr == MemLocs'[A'[Hash[k]]]
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
              <7>1. ValOfKeyInBktAtAddr(k, A[Hash[k]])' = bkt_arr[idx].val
                BY DEF ValOfKeyInBktAtAddr
              <7>2. bkt_arr = MemLocs[A[Hash[k]]]
                BY Zenon
              <7> QED
                BY <7>1, <7>2, ZenonT(30) DEF ValOfKeyInBktAtAddr
            <6> QED
              BY <6>1, <6>2, <6>3
          <5>2. ASSUME NEW q \in ProcSet
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
            <6> USE <5>2
            <6>A. \A k \in KeyDomain : KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, bucket[q])'
              BY Zenon DEF KeyInBktAtAddr
            <6>B. \A k \in KeyDomain : ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, bucket[q])
              <7> SUFFICES ASSUME NEW k \in KeyDomain
                           PROVE  ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, bucket[q])
                OBVIOUS
              <7> bkt_arr == MemLocs'[bucket'[q]]
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
              <7>1. ValOfKeyInBktAtAddr(k, bucket[q])' = bkt_arr[idx].val
                BY DEF ValOfKeyInBktAtAddr
              <7>2. bkt_arr = MemLocs[bucket[q]]
                BY Zenon
              <7> QED
                BY <7>1, <7>2, ZenonT(30) DEF ValOfKeyInBktAtAddr
            <6>1. CASE pc[q] = RemainderID
              <7> USE <6>1
              <7> SUFFICES c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
                BY RemDef, Zenon
              <7>1. pc'[q] = RemainderID
                BY RemDef, Zenon
              <7>2. c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2
            <6>2. CASE pc[q] = "F1"
              <7> USE <6>2
              <7> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY RemDef, Zenon
              <7>1. pc'[q] = "F1"
                BY RemDef, Zenon
              <7>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2
            <6>3. CASE pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
              <7> USE <6>3
              <7> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                BY RemDef, Zenon
              <7>1. pc'[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                BY RemDef, Zenon DEF KeyInBktAtAddr
              <7>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
                BY <7>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7>3. arg[q].key = arg'[q].key /\ arg[q].key \in KeyDomain
                BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
              <7>4. c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                BY <7>2, <7>3, <6>B
              <7> QED
                BY <7>2, <7>4
            <6>4. CASE pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
              <7> USE <6>4
              <7> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                BY RemDef, Zenon
              <7>1. CASE q = p
                <8> USE <7>1
                <8>1. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r'[q]
                  BY SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                  BY <8>1, Zenon
                <8> QED
                  BY <8>2
              <7> SUFFICES ASSUME q # p
                           PROVE  c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                BY <7>1
              <7>2. pc'[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                BY RemDef, Zenon DEF KeyInBktAtAddr
              <7>3. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                BY <7>2,  SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>3
            <6>5. CASE pc[q] = "F3"
              <7> USE <6>5
              <7> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY RemDef, Zenon
              <7>1. pc'[q] = "F3"
                BY RemDef, Zenon
              <7>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2 
            <6>6. CASE pc[q] \in {"I1", "I3", "I4"}
              <7> USE <6>6
              <7> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY RemDef, Zenon
              <7>1. pc'[q] \in {"I1", "I3", "I4"}
                BY RemDef, Zenon
              <7>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2 
            <6>7. CASE pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
              <7> USE <6>7
              <7> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                BY RemDef, Zenon
              <7>1. CASE p = q
                <8> USE <7>1
                <8>1. c.op[p] = "Insert" /\ c.arg[p] = arg[p] /\ c.res[p] = r'[p]
                  BY SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8>2. r'[p] = ValOfKeyInBktAtAddr(arg[p].key, bucket[p])
                  BY Zenon
                <8> QED
                  BY <8>1, <8>2
              <7> SUFFICES ASSUME p # q
                           PROVE  c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                BY <7>1
              <7>2. pc'[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                BY RemDef, Zenon DEF KeyInBktAtAddr
              <7>3. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
                BY <7>2,  SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7>4. arg[q].key = arg'[q].key /\ arg[q].key \in KeyDomain
                BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
              <7>5. c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                BY <7>3, <7>4, <6>B
              <7> QED
                BY <7>3, <7>5
            <6>8. CASE pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
              <7> USE <6>8
              <7> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY RemDef, Zenon
              <7>1. CASE p = q
                <8> USE <7>1
                <8>1. c.op[p] = "Insert" /\ c.arg[p] = arg[p] /\ c.res[p] = BOT
                  BY SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>1
              <7> SUFFICES ASSUME p # q
                           PROVE  c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <7>1
              <7>2. pc'[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                BY RemDef, Zenon DEF KeyInBktAtAddr
              <7>3. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <7>2, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>3 
            <6>9. CASE pc[q] = "I5"
              <7> USE <6>9
              <7> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY RemDef, Zenon
              <7>1. pc'[q] = "I5"
                BY RemDef, Zenon 
              <7>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2 
            <6>10. CASE pc[q] \in {"U1", "U2", "U3", "U4"}
              <7> USE <6>10
              <7> SUFFICES c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY RemDef, Zenon
              <7>1. pc'[q] \in {"U1", "U2", "U3", "U4"}
                BY RemDef, Zenon
              <7>2. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2
            <6>11. CASE pc[q] = "U5" 
              <7> USE <6>11
              <7> SUFFICES c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY RemDef, Zenon
              <7>1. pc'[q] = "U5"
                BY RemDef, Zenon
              <7>2. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2
            <6>12. CASE pc[q] \in {"R1", "R3", "R4"}
              <7> USE <6>12
              <7> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY RemDef, Zenon
              <7>1. pc'[q] \in {"R1", "R3", "R4"}
                BY RemDef, Zenon
              <7>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2
            <6>13. CASE pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
              <7> USE <6>13
              <7> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY RemDef, Zenon
              <7>1. pc'[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                BY RemDef, Zenon DEF KeyInBktAtAddr
              <7>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2
            <6>14. CASE pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
              <7> USE <6>14
              <7> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                BY RemDef, Zenon
              <7>1. pc'[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                BY RemDef, Zenon DEF KeyInBktAtAddr
              <7>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2
            <6>15. CASE pc[q] = "R5"
              <7> USE <6>15
              <7> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY RemDef, Zenon
              <7>1. pc'[q] = "R5" 
                BY RemDef, Zenon
              <7>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2
            <6> QED
                BY RemDef, ZenonT(120),
                    <6>1, <6>2, <6>3, <6>4, <6>5, <6>6, <6>7, <6>8, <6>9, 
                    <6>10, <6>11, <6>12, <6>13, <6>14, <6>15
                DEF LineIDs
          <5> QED
            BY <5>1, <5>2, Zenon DEF S
        <4>2. c \in P
          BY <4>1 DEF InvL1
        <4>3. c \in Evolve(P)
          BY <4>2, EmptySeqEvolve
        <4> QED
          BY <4>3
      <3>5. CASE Line = I3(p)
        <4> USE <3>5 DEF I3
        <4> SUFFICES ASSUME NEW c \in ConfigDomain,
                            c \in S'
                     PROVE  c \in P'
          BY Zenon DEF InvL1, S
        <4>1. CASE bucket[p] = NULL
          <5> PICK addr \in Addrs : 
                   /\ addr \notin AllocAddrs
                   /\ AllocAddrs' = AllocAddrs \cup {addr}
                   /\ newbkt' = [newbkt EXCEPT ![p] = addr]
                   /\ MemLocs' = [MemLocs EXCEPT ![addr] = <<arg[p]>>]
            BY <4>1, Zenon
          <5>1. c \in S
            <6>1. c.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL]
              <7>1. c.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]])' THEN ValOfKeyInBktAtAddr(k, A[Hash[k]])' ELSE NULL]
                BY Zenon, SPrimeRewrite DEF SPrime
              <7>2. \A k \in KeyDomain : KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
                <8> SUFFICES ASSUME NEW k \in KeyDomain
                             PROVE  KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
                  OBVIOUS
                <8>1. A'[Hash[k]] = A[Hash[k]]
                  BY Zenon
                <8>2. CASE A[Hash[k]] = NULL
                  BY <8>1, <8>2 DEF KeyInBktAtAddr
                <8> SUFFICES ASSUME A[Hash[k]] # NULL
                             PROVE  KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
                  BY <8>2
                <8>3. A[Hash[k]] \in AllocAddrs
                  BY HashDef, Zenon
                <8>4. A[Hash[k]] # addr
                  BY NULLDef, <8>3
                <8>5. \A a \in Addrs : a # addr => MemLocs'[a] = MemLocs[a]
                  BY Zenon
                <8>6. MemLocs'[A'[Hash[k]]] = MemLocs[A[Hash[k]]]
                  BY <8>1, <8>4, <8>5
                <8> QED
                  BY <8>6, Zenon DEF KeyInBktAtAddr
              <7>3. \A k \in KeyDomain : KeyInBktAtAddr(k, A[Hash[k]]) => (ValOfKeyInBktAtAddr(k, A[Hash[k]]) = ValOfKeyInBktAtAddr(k, A[Hash[k]])')
                <8> SUFFICES ASSUME NEW k \in KeyDomain,
                                    NEW bkt_arr,
                                    A[Hash[k]] # NULL,
                                    bkt_arr = MemLocs[A[Hash[k]]],
                                    \E index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
                             PROVE  ValOfKeyInBktAtAddr(k, A[Hash[k]]) = ValOfKeyInBktAtAddr(k, A[Hash[k]])'
                  BY Zenon DEF KeyInBktAtAddr
                <8>1. A'[Hash[k]] = A[Hash[k]]
                  BY Zenon
                <8>2. A[Hash[k]] \in AllocAddrs
                  BY HashDef, Zenon
                <8>3. A[Hash[k]] # addr
                  BY NULLDef, <8>2
                <8>4. \A a \in Addrs : a # addr => MemLocs'[a] = MemLocs[a]
                  BY Zenon
                <8>5. MemLocs'[A'[Hash[k]]] = MemLocs[A[Hash[k]]]
                  BY <8>1, <8>3, <8>4
                <8> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
                <8>6. ValOfKeyInBktAtAddr(k, A[Hash[k]]) = bkt_arr[idx].val
                  BY Zenon DEF ValOfKeyInBktAtAddr
                <8>7. ValOfKeyInBktAtAddr(k, A[Hash[k]])' = bkt_arr[idx].val
                  BY Isa, <8>5 DEF ValOfKeyInBktAtAddr
                <8> QED
                  BY <8>6, <8>7, Zenon
              <7> QED
                BY <7>1, <7>2, <7>3, Zenon
            <6>2. ASSUME NEW q \in ProcSet
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
              <7> USE <6>2
              <7>A. KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
                <8>1. bucket[q] = bucket'[q]
                  BY Zenon
                <8>2. CASE bucket[q] = NULL
                  BY <8>1, <8>2, Zenon DEF KeyInBktAtAddr
                <8> SUFFICES ASSUME bucket[q] # NULL
                             PROVE  KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY <8>2
                <8>3. bucket[q] \in AllocAddrs
                  BY NULLDef, Zenon
                <8>4. bucket[q] # addr
                  BY <8>3
                <8>5. \A a \in Addrs : a # addr => MemLocs'[a] = MemLocs[a]
                  BY Zenon
                <8>6. MemLocs'[bucket'[q]] = MemLocs[bucket[q]]
                  BY <8>1, <8>4, <8>5
                <8> QED
                  BY <8>6, Zenon DEF KeyInBktAtAddr
              <7>B. KeyInBktAtAddr(arg[q].key, bucket[q]) => (ValOfKeyInBktAtAddr(arg[q].key, bucket[q]) = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])')
                <8> SUFFICES ASSUME NEW bkt_arr,
                                    bkt_arr = MemLocs[bucket[q]],
                                    bucket[q] # NULL,
                                    \E index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
                             PROVE  ValOfKeyInBktAtAddr(arg[q].key, bucket[q]) = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY Zenon DEF KeyInBktAtAddr
                <8>1. bucket[q] = bucket'[q]
                  BY Zenon
                <8>2. bucket[q] \in AllocAddrs
                  BY NULLDef, Zenon
                <8>3. bucket[q] # addr
                  BY <8>2
                <8>4. \A a \in Addrs : a # addr => MemLocs'[a] = MemLocs[a]
                  BY Zenon
                <8>5. MemLocs'[bucket'[q]] = MemLocs[bucket[q]]
                  BY <8>1, <8>3, <8>4 
                <8> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
                <8>6. ValOfKeyInBktAtAddr(arg[q].key, bucket[q]) = bkt_arr[idx].val
                  BY Zenon DEF ValOfKeyInBktAtAddr
                <8>7. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = bkt_arr[idx].val
                  BY Isa, <8>5 DEF ValOfKeyInBktAtAddr
                <8> QED
                  BY <8>6, <8>7, Zenon
              <7>1. CASE pc[q] = RemainderID
                <8> USE <7>1
                <8> SUFFICES c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
                  BY RemDef, Zenon
                <8>1. pc'[q] = RemainderID
                  BY RemDef, Zenon
                <8>2. c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
                  BY <8>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2
              <7>2. CASE pc[q] = "F1"
                <8> USE <7>2
                <8> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY RemDef, Zenon
                <8>1. pc'[q] = "F1"
                  BY RemDef, Zenon
                <8>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY <8>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2  
              <7>3. CASE pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                <8> USE <7>3
                <8> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                  BY RemDef, Zenon
                <8>1. pc'[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY <7>A, RemDef, Zenon DEF KeyInBktAtAddr
                <8>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY <8>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8>3. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                  BY <7>B, Zenon
                <8> QED
                  BY <8>2, <8>3
              <7>4. CASE pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                <8> USE <7>4
                <8> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                  BY RemDef, Zenon
                <8>1. pc'[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY <7>A, RemDef, Zenon DEF KeyInBktAtAddr
                <8>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                  BY <8>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2
              <7>5. CASE pc[q] = "F3" 
                <8> USE <7>5
                <8> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                  BY RemDef, Zenon
                <8>1. pc'[q] = "F3"
                  BY RemDef, Zenon
                <8>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                  BY <8>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2
              <7>6. CASE pc[q] \in {"I1", "I3", "I4"}
                <8> USE <7>6
                <8> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY RemDef, Zenon
                <8>1. CASE p = q
                  <9> USE <8>1
                  <9>1. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                    BY SPrimeRewrite, Zenon, RemDef DEF SPrime
                  <9> QED
                    BY <9>1
                <8> SUFFICES ASSUME p # q
                             PROVE  c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY <8>1
                <8>2. pc'[q] \in {"I1", "I3", "I4"}
                  BY RemDef, Zenon
                <8>3. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY <8>2,  SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>3
              <7>7. CASE pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                <8> USE <7>7
                <8> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                  BY RemDef, Zenon
                <8>1. pc'[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY <7>A, RemDef, Zenon DEF KeyInBktAtAddr
                <8>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY <8>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8>3. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                  BY <7>B, Zenon
                <8> QED
                  BY <8>2, <8>3
              <7>8. CASE pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                <8> USE <7>8
                <8> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY RemDef, Zenon
                <8>1. pc'[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY <7>A, RemDef, Zenon DEF KeyInBktAtAddr
                <8>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY <8>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2
              <7>9. CASE pc[q] = "I5"
                <8> USE <7>9
                <8> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                  BY RemDef, Zenon
                <8>1. pc'[q] = "I5"
                  BY RemDef, Zenon
                <8>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                  BY <8>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2
              <7>10. CASE pc[q] \in {"U1", "U2", "U3", "U4"}
                <8> USE <7>10
                <8> SUFFICES c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY RemDef, Zenon
                <8>1. pc'[q] \in {"U1", "U2", "U3", "U4"}
                  BY RemDef, Zenon
                <8>2. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY <8>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2
              <7>11. CASE pc[q] = "U5" 
                <8> USE <7>11
                <8> SUFFICES c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                  BY RemDef, Zenon
                <8>1. pc'[q] = "U5"
                  BY RemDef, Zenon
                <8>2. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                  BY <8>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2
              <7>12. CASE pc[q] \in {"R1", "R3", "R4"}
                <8> USE <7>12
                <8> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY RemDef, Zenon
                <8>1. pc'[q] \in {"R1", "R3", "R4"}
                  BY RemDef, Zenon
                <8>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY <8>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2
              <7>13. CASE pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                <8> USE <7>13
                <8> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY RemDef, Zenon
                <8>1. pc'[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY <7>A, RemDef, Zenon DEF KeyInBktAtAddr
                <8>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY <8>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2
              <7>14. CASE pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                <8> USE <7>14
                <8> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                  BY RemDef, Zenon
                <8>1. pc'[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY <7>A, RemDef, Zenon DEF KeyInBktAtAddr
                <8>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                  BY <8>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2
              <7>15. CASE pc[q] = "R5"
                <8> USE <7>15
                <8> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                  BY RemDef, Zenon
                <8>1. pc'[q] = "R5"
                  BY RemDef, Zenon
                <8>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                  BY <8>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2
              <7> QED
                  BY RemDef, ZenonT(120),
                     <7>1, <7>2, <7>3, <7>4, <7>5, <7>6, <7>7, <7>8, <7>9, 
                     <7>10, <7>11, <7>12, <7>13, <7>14, <7>15
                  DEF LineIDs
            <6> QED
              BY <6>1, <6>2, Zenon DEF S
          <5>2. c \in P
            BY <5>1 DEF InvL1
          <5>3. c \in Evolve(P)
            BY <5>2, EmptySeqEvolve
          <5> QED
            BY <5>3
        <4>2. CASE bucket[p] # NULL
          <5> PICK addr \in Addrs : 
                   /\ addr \notin AllocAddrs
                   /\ AllocAddrs' = AllocAddrs \cup {addr}
                   /\ newbkt' = [newbkt EXCEPT ![p] = addr]
                   /\ MemLocs' = [MemLocs EXCEPT ![addr] = Append(MemLocs[bucket[p]], arg[p])]
            BY <4>2, Zenon
          <5>1. c \in S
            <6>1. c.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL]
              <7>1. c.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]])' THEN ValOfKeyInBktAtAddr(k, A[Hash[k]])' ELSE NULL]
                BY Zenon, SPrimeRewrite DEF SPrime
              <7>2. \A k \in KeyDomain : KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
                <8> SUFFICES ASSUME NEW k \in KeyDomain
                             PROVE  KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
                  OBVIOUS
                <8>1. A'[Hash[k]] = A[Hash[k]]
                  BY Zenon
                <8>2. CASE A[Hash[k]] = NULL
                  BY <8>1, <8>2 DEF KeyInBktAtAddr
                <8> SUFFICES ASSUME A[Hash[k]] # NULL
                             PROVE  KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
                  BY <8>2
                <8>3. A[Hash[k]] \in AllocAddrs
                  BY HashDef, Zenon
                <8>4. A[Hash[k]] # addr
                  BY NULLDef, <8>3
                <8>5. \A a \in Addrs : a # addr => MemLocs'[a] = MemLocs[a]
                  BY Zenon
                <8>6. MemLocs'[A'[Hash[k]]] = MemLocs[A[Hash[k]]]
                  BY <8>1, <8>4, <8>5
                <8> QED
                  BY <8>6, Zenon DEF KeyInBktAtAddr
              <7>3. \A k \in KeyDomain : KeyInBktAtAddr(k, A[Hash[k]]) => (ValOfKeyInBktAtAddr(k, A[Hash[k]]) = ValOfKeyInBktAtAddr(k, A[Hash[k]])')
                <8> SUFFICES ASSUME NEW k \in KeyDomain,
                                    NEW bkt_arr,
                                    A[Hash[k]] # NULL,
                                    bkt_arr = MemLocs[A[Hash[k]]],
                                    \E index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
                             PROVE  ValOfKeyInBktAtAddr(k, A[Hash[k]]) = ValOfKeyInBktAtAddr(k, A[Hash[k]])'
                  BY Zenon DEF KeyInBktAtAddr
                <8>1. A'[Hash[k]] = A[Hash[k]]
                  BY Zenon
                <8>2. A[Hash[k]] \in AllocAddrs
                  BY HashDef, Zenon
                <8>3. A[Hash[k]] # addr
                  BY NULLDef, <8>2
                <8>4. \A a \in Addrs : a # addr => MemLocs'[a] = MemLocs[a]
                  BY Zenon
                <8>5. MemLocs'[A'[Hash[k]]] = MemLocs[A[Hash[k]]]
                  BY <8>1, <8>3, <8>4
                <8> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
                <8>6. ValOfKeyInBktAtAddr(k, A[Hash[k]]) = bkt_arr[idx].val
                  BY Zenon DEF ValOfKeyInBktAtAddr
                <8>7. ValOfKeyInBktAtAddr(k, A[Hash[k]])' = bkt_arr[idx].val
                  BY Isa, <8>5 DEF ValOfKeyInBktAtAddr
                <8> QED
                  BY <8>6, <8>7, Zenon
              <7> QED
                BY <7>1, <7>2, <7>3, Zenon
            <6>2. ASSUME NEW q \in ProcSet
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
              <7> USE <6>2
              <7>A. KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
                <8>1. bucket[q] = bucket'[q]
                  BY Zenon
                <8>2. CASE bucket[q] = NULL
                  BY <8>1, <8>2, Zenon DEF KeyInBktAtAddr
                <8> SUFFICES ASSUME bucket[q] # NULL
                             PROVE  KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY <8>2
                <8>3. bucket[q] \in AllocAddrs
                  BY NULLDef, Zenon
                <8>4. bucket[q] # addr
                  BY <8>3
                <8>5. \A a \in Addrs : a # addr => MemLocs'[a] = MemLocs[a]
                  BY Zenon
                <8>6. MemLocs'[bucket'[q]] = MemLocs[bucket[q]]
                  BY <8>1, <8>4, <8>5
                <8> QED
                  BY <8>6, Zenon DEF KeyInBktAtAddr
              <7>B. KeyInBktAtAddr(arg[q].key, bucket[q]) => (ValOfKeyInBktAtAddr(arg[q].key, bucket[q]) = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])')
                <8> SUFFICES ASSUME NEW bkt_arr,
                                    bkt_arr = MemLocs[bucket[q]],
                                    bucket[q] # NULL,
                                    \E index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
                             PROVE  ValOfKeyInBktAtAddr(arg[q].key, bucket[q]) = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY Zenon DEF KeyInBktAtAddr
                <8>1. bucket[q] = bucket'[q]
                  BY Zenon
                <8>2. bucket[q] \in AllocAddrs
                  BY NULLDef, Zenon
                <8>3. bucket[q] # addr
                  BY <8>2
                <8>4. \A a \in Addrs : a # addr => MemLocs'[a] = MemLocs[a]
                  BY Zenon
                <8>5. MemLocs'[bucket'[q]] = MemLocs[bucket[q]]
                  BY <8>1, <8>3, <8>4 
                <8> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
                <8>6. ValOfKeyInBktAtAddr(arg[q].key, bucket[q]) = bkt_arr[idx].val
                  BY Zenon DEF ValOfKeyInBktAtAddr
                <8>7. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = bkt_arr[idx].val
                  BY Isa, <8>5 DEF ValOfKeyInBktAtAddr
                <8> QED
                  BY <8>6, <8>7, Zenon
              <7>1. CASE pc[q] = RemainderID
                <8> USE <7>1
                <8> SUFFICES c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
                  BY RemDef, Zenon
                <8>1. pc'[q] = RemainderID
                  BY RemDef, Zenon
                <8>2. c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
                  BY <8>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2
              <7>2. CASE pc[q] = "F1"
                <8> USE <7>2
                <8> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY RemDef, Zenon
                <8>1. pc'[q] = "F1"
                  BY RemDef, Zenon
                <8>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY <8>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2  
              <7>3. CASE pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                <8> USE <7>3
                <8> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                  BY RemDef, Zenon
                <8>1. pc'[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY <7>A, RemDef, Zenon DEF KeyInBktAtAddr
                <8>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY <8>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8>3. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                  BY <7>B, Zenon
                <8> QED
                  BY <8>2, <8>3
              <7>4. CASE pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                <8> USE <7>4
                <8> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                  BY RemDef, Zenon
                <8>1. pc'[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY <7>A, RemDef, Zenon DEF KeyInBktAtAddr
                <8>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                  BY <8>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2
              <7>5. CASE pc[q] = "F3" 
                <8> USE <7>5
                <8> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                  BY RemDef, Zenon
                <8>1. pc'[q] = "F3"
                  BY RemDef, Zenon
                <8>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                  BY <8>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2
              <7>6. CASE pc[q] \in {"I1", "I3", "I4"}
                <8> USE <7>6
                <8> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY RemDef, Zenon
                <8>1. CASE p = q
                  <9> USE <8>1
                  <9>1. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                    BY SPrimeRewrite, Zenon, RemDef DEF SPrime
                  <9> QED
                    BY <9>1
                <8> SUFFICES ASSUME p # q
                             PROVE  c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY <8>1
                <8>2. pc'[q] \in {"I1", "I3", "I4"}
                  BY RemDef, Zenon
                <8>3. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY <8>2,  SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>3
              <7>7. CASE pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                <8> USE <7>7
                <8> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                  BY RemDef, Zenon
                <8>1. pc'[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY <7>A, RemDef, Zenon DEF KeyInBktAtAddr
                <8>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY <8>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8>3. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                  BY <7>B, Zenon
                <8> QED
                  BY <8>2, <8>3
              <7>8. CASE pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                <8> USE <7>8
                <8> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY RemDef, Zenon
                <8>1. pc'[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY <7>A, RemDef, Zenon DEF KeyInBktAtAddr
                <8>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY <8>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2
              <7>9. CASE pc[q] = "I5"
                <8> USE <7>9
                <8> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                  BY RemDef, Zenon
                <8>1. pc'[q] = "I5"
                  BY RemDef, Zenon
                <8>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                  BY <8>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2
              <7>10. CASE pc[q] \in {"U1", "U2", "U3", "U4"}
                <8> USE <7>10
                <8> SUFFICES c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY RemDef, Zenon
                <8>1. pc'[q] \in {"U1", "U2", "U3", "U4"}
                  BY RemDef, Zenon
                <8>2. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY <8>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2
              <7>11. CASE pc[q] = "U5" 
                <8> USE <7>11
                <8> SUFFICES c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                  BY RemDef, Zenon
                <8>1. pc'[q] = "U5"
                  BY RemDef, Zenon
                <8>2. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                  BY <8>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2
              <7>12. CASE pc[q] \in {"R1", "R3", "R4"}
                <8> USE <7>12
                <8> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY RemDef, Zenon
                <8>1. pc'[q] \in {"R1", "R3", "R4"}
                  BY RemDef, Zenon
                <8>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY <8>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2
              <7>13. CASE pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                <8> USE <7>13
                <8> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY RemDef, Zenon
                <8>1. pc'[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY <7>A, RemDef, Zenon DEF KeyInBktAtAddr
                <8>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY <8>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2
              <7>14. CASE pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                <8> USE <7>14
                <8> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                  BY RemDef, Zenon
                <8>1. pc'[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY <7>A, RemDef, Zenon DEF KeyInBktAtAddr
                <8>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                  BY <8>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2
              <7>15. CASE pc[q] = "R5"
                <8> USE <7>15
                <8> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                  BY RemDef, Zenon
                <8>1. pc'[q] = "R5"
                  BY RemDef, Zenon
                <8>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                  BY <8>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2
              <7> QED
                  BY RemDef, ZenonT(120),
                     <7>1, <7>2, <7>3, <7>4, <7>5, <7>6, <7>7, <7>8, <7>9, 
                     <7>10, <7>11, <7>12, <7>13, <7>14, <7>15
                  DEF LineIDs
            <6> QED
              BY <6>1, <6>2, Zenon DEF S
          <5>2. c \in P
            BY <5>1 DEF InvL1
          <5>3. c \in Evolve(P)
            BY <5>2, EmptySeqEvolve
          <5> QED
            BY <5>3
        <4> QED
          BY <4>1, <4>2
      <3>6. CASE Line = I4(p)
        <4> USE <3>6 DEF I4
        <4> SUFFICES ASSUME NEW c \in ConfigDomain,
                     c \in S'
                     PROVE c \in P'
          BY Zenon DEF InvL1, S
        <4>1. CASE A[Hash[arg[p].key]] = bucket[p]
          <5> USE <4>1
          <5> DEFINE c_pred == [state |-> [c.state EXCEPT ![arg[p].key] = NULL],
                                op    |-> c.op,
                                arg   |-> c.arg,
                                res   |-> [c.res EXCEPT ![p] = BOT]]
          <5>1. c_pred \in ConfigDomain
            <6>1. c_pred.state \in StateDomain
              BY Zenon DEF ConfigDomain, StateDomain
            <6>2. c_pred.op \in [ProcSet -> OpDomain]
              BY DEF ConfigDomain
            <6>3. c_pred.arg \in [ProcSet -> ArgDomain]
              BY DEF ConfigDomain
            <6>4. c_pred.res \in [ProcSet -> ResDomain]
              BY DEF ConfigDomain, ResDomain
            <6> QED
              BY <6>1, <6>2, <6>3, <6>4 DEF ConfigDomain
          <5>2. c_pred \in S
            <6>1. c_pred.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL]
              <7> SUFFICES ASSUME NEW k \in KeyDomain
                           PROVE  c_pred.state[k] = IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL
                BY Zenon, <5>1 DEF StateDomain, ConfigDomain
              <7>1. CASE k = arg[p].key
                <8> USE <7>1
                <8>1. ~KeyInBktAtAddr(k, A[Hash[k]])
                  BY Zenon DEF BktOK
                <8>2. c_pred.state[k] = NULL
                  BY Zenon DEF ConfigDomain, StateDomain
                <8> QED
                  BY <8>1, <8>2
              <7>2. CASE k # arg[p].key /\ Hash[k] # Hash[arg[p].key]
                <8> USE <7>2
                <8>1. c.state = [key \in KeyDomain |-> IF KeyInBktAtAddr(key, A[Hash[key]])' THEN ValOfKeyInBktAtAddr(key, A[Hash[key]])' ELSE NULL]
                  BY SPrimeRewrite, Zenon DEF SPrime
                <8>2. A'[Hash[k]] = A[Hash[k]]
                  BY HashDef, Zenon
                <8>3. KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
                  BY <8>2, Zenon DEF KeyInBktAtAddr
                <8>4. ValOfKeyInBktAtAddr(k, A[Hash[k]]) = ValOfKeyInBktAtAddr(k, A[Hash[k]])'
                  <9> DEFINE bkt_arr == MemLocs'[A'[Hash[k]]]
                  <9> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
                  <9>1. ValOfKeyInBktAtAddr(k, A[Hash[k]])' = bkt_arr[idx].val
                    BY Zenon DEF ValOfKeyInBktAtAddr
                  <9>2. bkt_arr = MemLocs[A[Hash[k]]]
                    BY Zenon, <8>2
                  <9>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
                    BY Zenon
                  <9>4. ValOfKeyInBktAtAddr(k, A[Hash[k]]) = MemLocs[A[Hash[k]]][CHOOSE index \in 1..Len(MemLocs[A[Hash[k]]]) : MemLocs[A[Hash[k]]][index].key = k].val
                    BY Zenon DEF ValOfKeyInBktAtAddr
                  <9>5. ValOfKeyInBktAtAddr(k, A[Hash[k]]) = bkt_arr[idx].val
                    BY ZenonT(90), <9>2, <9>3, <9>4
                  <9> QED
                    BY Zenon, <9>1, <9>5
                <8> QED
                  BY <8>1, <8>3, <8>4
              <7>3. CASE k # arg[p].key /\ Hash[k] = Hash[arg[p].key]
                <8> USE <7>3
                <8>1. c.state = [key \in KeyDomain |-> IF KeyInBktAtAddr(key, A[Hash[key]])' 
                                                          THEN ValOfKeyInBktAtAddr(key, A[Hash[key]])' 
                                                          ELSE NULL]
                  BY SPrimeRewrite, Zenon DEF SPrime
                <8>2. c_pred.state[k] = IF KeyInBktAtAddr(k, A[Hash[k]])' 
                                           THEN ValOfKeyInBktAtAddr(k, A[Hash[k]])' 
                                           ELSE NULL
                  BY <8>1
                <8>3. MemLocs' = MemLocs
                  BY Zenon
                <8>4. bucket[p] = A[Hash[k]]
                  BY Zenon
                <8>5. arg[p].key \in KeyDomain
                  BY RemDef, Zenon DEF ArgsOf, LineIDtoOp
                <8>6. newbkt[p] = A'[Hash[k]]
                  BY Zenon, <8>5, HashDef
                <8>7. KeyInBktAtAddr(k, A[Hash[k]])' = KeyInBktAtAddr(k, newbkt[p])
                  BY <8>6, Zenon DEF KeyInBktAtAddr
                <8>8. ValOfKeyInBktAtAddr(k, A[Hash[k]])' = ValOfKeyInBktAtAddr(k, newbkt[p])
                  BY <8>6, Zenon DEF ValOfKeyInBktAtAddr
                <8>9. c_pred.state[k] = IF KeyInBktAtAddr(k, newbkt[p]) THEN ValOfKeyInBktAtAddr(k, newbkt[p]) ELSE NULL
                  BY <8>2, <8>7, <8>8, Zenon
                <8>10. /\ KeyInBktAtAddr(k, bucket[p]) = KeyInBktAtAddr(k, newbkt[p])
                       /\ KeyInBktAtAddr(k, bucket[p]) => (ValOfKeyInBktAtAddr(k, bucket[p]) = ValOfKeyInBktAtAddr(k, newbkt[p]))
                  BY Zenon DEF NewBktOK
                <8>11. c_pred.state[k] = IF KeyInBktAtAddr(k, bucket[p]) THEN ValOfKeyInBktAtAddr(k, bucket[p]) ELSE NULL
                  BY <8>9, <8>10, Zenon
                <8>12. c_pred.state[k] = IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL
                  BY <8>11, <8>6, Zenon
                <8> QED
                  BY <8>12, Zenon
              <7> QED
                BY <7>1, <7>2, <7>3
            <6>2. ASSUME NEW q \in ProcSet
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
              <7> USE <6>2
              <7>1. CASE pc[q] = RemainderID
                <8> USE <7>1
                <8> SUFFICES c_pred.op[q] = BOT /\ c_pred.arg[q] = BOT /\ c_pred.res[q] = BOT
                  BY RemDef, Zenon
                <8>1. q # p
                  BY RemDef, Zenon
                <8>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                  BY <8>1
                <8>3. pc'[q] = RemainderID
                  BY RemDef, Zenon
                <8>4. c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
                  BY <8>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2, <8>4
              <7>2. CASE pc[q] = "F1"
                <8> USE <7>2
                <8> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
                  BY RemDef, Zenon
                <8>1. q # p
                  BY RemDef, Zenon
                <8>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                  BY <8>1
                <8>3. pc'[q] = "F1"
                  BY RemDef, Zenon
                <8>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY <8>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2, <8>4
              <7>3. CASE pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                <8> USE <7>3
                <8> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                  BY RemDef, Zenon
                <8>1. q # p
                  BY RemDef, Zenon
                <8>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                  BY <8>1
                <8>3. pc'[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY RemDef, Zenon DEF KeyInBktAtAddr
                <8>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY <8>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                  <9> DEFINE bkt_arr == MemLocs'[bucket'[q]]
                  <9> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg'[q].key
                  <9>1. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = bkt_arr[idx].val
                    BY Zenon DEF ValOfKeyInBktAtAddr
                  <9>2. bkt_arr = MemLocs[bucket[q]]
                    BY Zenon
                  <9>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
                    BY Zenon
                  <9> QED
                    BY <9>1, <9>2, <9>3, Isa DEF ValOfKeyInBktAtAddr
                <8> QED
                  BY <8>2, <8>4, <8>5
              <7>4. CASE pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                <8> USE <7>4
                <8> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = NULL
                  BY RemDef, Zenon
                <8>1. q # p
                  BY RemDef, Zenon
                <8>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                  BY <8>1
                <8>3. pc'[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY RemDef, Zenon DEF KeyInBktAtAddr
                <8>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                  BY <8>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2, <8>4
              <7>5. CASE pc[q] = "F3"
                <8> USE <7>5
                <8> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
                  BY RemDef, Zenon
                <8>1. q # p
                  BY RemDef, Zenon
                <8>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                  BY <8>1
                <8>3. pc'[q] = "F3"
                  BY RemDef, Zenon
                <8>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                  BY <8>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2, <8>4 
              <7>6. CASE pc[q] \in {"I1", "I3", "I4"}
                <8> USE <7>6
                <8> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
                  BY RemDef, Zenon
                <8>A. CASE p = q
                  <9> USE <8>A
                  <9>1. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = BOT
                    BY <5>1 DEF ConfigDomain
                  <9>2. pc'[q] = "I5"
                    BY Zenon
                  <9>3. c.op[q] = "Insert" /\ c.arg[p] = arg[q]
                    BY <9>2, SPrimeRewrite, Zenon, RemDef DEF SPrime
                  <9> QED
                    BY <9>1, <9>3
                <8> SUFFICES ASSUME p # q
                             PROVE  c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
                  BY <8>A
                <8>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                  OBVIOUS
                <8>3. pc'[q] \in {"I1", "I3", "I4"}
                  BY RemDef, Zenon
                <8>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY <8>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2, <8>4
              <7>7. CASE pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                <8> USE <7>7
                <8> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                  BY RemDef, Zenon
                <8>1. q # p
                  BY RemDef, Zenon
                <8>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                  BY <8>1
                <8>3. pc'[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY RemDef, Zenon DEF KeyInBktAtAddr
                <8>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY <8>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                  <9> DEFINE bkt_arr == MemLocs'[bucket'[q]]
                  <9> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg'[q].key
                  <9>1. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = bkt_arr[idx].val
                    BY Zenon DEF ValOfKeyInBktAtAddr
                  <9>2. bkt_arr = MemLocs[bucket[q]]
                    BY Zenon
                  <9>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
                    BY Zenon
                  <9> QED
                    BY <9>1, <9>2, <9>3, Isa DEF ValOfKeyInBktAtAddr
                <8> QED
                  BY <8>2, <8>4, <8>5
              <7>8. CASE pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                <8> USE <7>8
                <8> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
                  BY RemDef, Zenon
                <8>1. q # p
                  BY RemDef, Zenon
                <8>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                  BY <8>1
                <8>3. pc'[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY RemDef, Zenon DEF KeyInBktAtAddr
                <8>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY <8>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2, <8>4
              <7>9. CASE pc[q] = "I5"
                <8> USE <7>9
                <8> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
                  BY RemDef, Zenon
                <8>1. q # p
                  BY RemDef, Zenon
                <8>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                  BY <8>1
                <8>3. pc'[q] = "I5"
                  BY RemDef, Zenon
                <8>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                  BY <8>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2, <8>4
              <7>10. CASE pc[q] \in {"U1", "U2", "U3", "U4"}
                <8> USE <7>10
                <8> SUFFICES c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
                  BY RemDef, Zenon
                <8>1. q # p
                  BY RemDef, Zenon
                <8>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                  BY <8>1
                <8>3. pc'[q] \in {"U1", "U2", "U3", "U4"}
                  BY RemDef, Zenon
                <8>4. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY <8>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2, <8>4
              <7>11. CASE pc[q] = "U5" 
                <8> USE <7>11
                <8> SUFFICES c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
                  BY RemDef, Zenon
                <8>1. q # p
                  BY RemDef, Zenon
                <8>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                  BY <8>1
                <8>3. pc'[q] = "U5"
                  BY RemDef, Zenon
                <8>4. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                  BY <8>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2, <8>4
              <7>12. CASE pc[q] \in {"R1", "R3", "R4"}
                <8> USE <7>12
                <8> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
                  BY RemDef, Zenon
                <8>1. q # p
                  BY RemDef, Zenon
                <8>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                  BY <8>1
                <8>3. pc'[q] \in {"R1", "R3", "R4"}
                  BY RemDef, Zenon
                <8>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY <8>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2, <8>4
              <7>13. CASE pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q]) 
                <8> USE <7>13
                <8> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
                  BY RemDef, Zenon
                <8>1. q # p
                  BY RemDef, Zenon
                <8>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                  BY <8>1
                <8>3. pc'[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY RemDef, Zenon DEF KeyInBktAtAddr
                <8>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY <8>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2, <8>4              
              <7>14. CASE pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                <8> USE <7>14
                <8> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = NULL
                  BY RemDef, Zenon
                <8>1. q # p
                  BY RemDef, Zenon
                <8>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                  BY <8>1
                <8>3. pc'[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY RemDef, Zenon DEF KeyInBktAtAddr
                <8>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                  BY <8>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2, <8>4    
              <7>15. CASE pc[q] = "R5"
                <8> USE <7>15
                <8> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
                  BY RemDef, Zenon
                <8>1. q # p
                  BY RemDef, Zenon
                <8>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                  BY <8>1
                <8>3. pc'[q] = "R5"
                  BY RemDef, Zenon
                <8>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                  BY <8>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2, <8>4
              <7> QED
                  BY RemDef, ZenonT(120),
                     <7>1, <7>2, <7>3, <7>4, <7>5, <7>6, <7>7, <7>8, <7>9, 
                     <7>10, <7>11, <7>12, <7>13, <7>14, <7>15
                  DEF LineIDs 
            <6> QED
              BY <5>1, <6>1, <6>2, Zenon DEF S
          <5>3. c_pred \in P
            BY <5>2 DEF InvL1
          <5>4. Delta(c_pred, p, c)
            <6>1. c_pred.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL]
              BY <5>1, <5>2, Zenon DEF S
            <6>2. c_pred.op[p] = "Insert" /\ c_pred.arg[p] = arg[p] /\ c_pred.res[p] = BOT
              BY <5>1, <5>2, Zenon, RemDef DEF S
            <6>3. arg[p] \in ArgsOf("Insert") /\ arg[p].key \in KeyDomain
              BY RemDef, Zenon DEF ArgsOf, LineIDtoOp 
            <6>4. c_pred.state[c_pred.arg[p].key] = NULL
              BY <6>1, <6>2, <6>3, Zenon DEF BktOK
            <6> SUFFICES /\ c.state = [c_pred.state EXCEPT ![arg[p].key] = arg[p].val]
                         /\ c.res = [c_pred.res EXCEPT ![p] = NULL]
              BY <6>2, <6>3, <6>4, Zenon DEF Delta
            <6> SUFFICES /\ c.state[arg[p].key] = arg[p].val
                         /\ c.res[p] = NULL
              BY <5>2, <6>3, ZenonT(60) DEF ConfigDomain, StateDomain
            <6>5. c.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]])' THEN ValOfKeyInBktAtAddr(k, A[Hash[k]])' ELSE NULL]
              BY SPrimeRewrite, Zenon DEF SPrime
            <6>6. c.state[arg[p].key] = IF KeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]])' THEN ValOfKeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]])' ELSE NULL
              BY <6>5, <6>3, Zenon
            <6>7. newbkt[p] = A'[Hash[arg[p].key]]
              BY Zenon, HashDef, <6>3
            <6>8. MemLocs[A'[Hash[arg[p].key]]] = MemLocs[newbkt[p]]
              BY Zenon, <6>7
            <6>9. KeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]])' = KeyInBktAtAddr(arg[p].key, newbkt[p])
              BY Zenon, <6>7 DEF KeyInBktAtAddr
            <6>10. ValOfKeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]])' = 
              MemLocs[A'[Hash[arg[p].key]]][CHOOSE index \in 1..Len(MemLocs[A'[Hash[arg[p].key]]]) : MemLocs[A'[Hash[arg[p].key]]][index].key = arg[p].key].val
              BY Zenon DEF ValOfKeyInBktAtAddr
            <6>11. ValOfKeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]])' = 
              MemLocs[newbkt[p]][CHOOSE index \in 1..Len(MemLocs[newbkt[p]]) : MemLocs[newbkt[p]][index].key = arg[p].key].val
              BY <6>10, <6>8
            <6>12. ValOfKeyInBktAtAddr(arg[p].key, newbkt[p]) = 
              MemLocs[newbkt[p]][CHOOSE index \in 1..Len(MemLocs[newbkt[p]]) : MemLocs[newbkt[p]][index].key = arg[p].key].val
              BY Zenon DEF ValOfKeyInBktAtAddr
            <6>13. ValOfKeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]])' = ValOfKeyInBktAtAddr(arg[p].key, newbkt[p])
              BY <6>11, <6>12, Zenon
            <6>14. c.state[arg[p].key] = IF KeyInBktAtAddr(arg[p].key, newbkt[p]) THEN ValOfKeyInBktAtAddr(arg[p].key, newbkt[p]) ELSE NULL
              BY <6>6, <6>9, <6>13, Zenon
            <6>15. c.state[arg[p].key] = arg[p].val
              BY <6>14, Zenon DEF NewBktOK
            <6>16. pc'[p] = "I5"
              BY Zenon
            <6>17. c.res[p] = r'[p]
              BY <6>16, SPrimeRewrite, RemDef, Zenon DEF SPrime
            <6>18. c.res[p] = NULL
              BY <6>17, Zenon DEF BktOK
            <6> QED
              BY <6>18, <6>15
          <5>5. c \in Evolve(P)
            BY <5>1, <5>3, <5>4, SingleDeltaEvolve
          <5> QED
            BY <5>5
        <4>2. CASE A[Hash[arg[p].key]] # bucket[p]
          <5> USE <4>2
          <5>0. ASSUME c \in S
                PROVE  c \in P'
            <6> USE <5>0
            <6>1. c \in P
              BY DEF InvL1
            <6>2. c \in Evolve(P)
              BY <6>1, EmptySeqEvolve
            <6> QED
              BY <6>2
          <5> SUFFICES c \in S
            BY <5>0
          <5>1. c.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL]
            <6>1. c.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]])' THEN ValOfKeyInBktAtAddr(k, A[Hash[k]])' ELSE NULL]
              BY Zenon, SPrimeRewrite DEF SPrime
            <6>2. \A k \in KeyDomain : KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
              BY Zenon DEF KeyInBktAtAddr
            <6>3. \A k \in KeyDomain : ValOfKeyInBktAtAddr(k, A[Hash[k]])' = ValOfKeyInBktAtAddr(k, A[Hash[k]])
              <7> SUFFICES ASSUME NEW k \in KeyDomain
                           PROVE  ValOfKeyInBktAtAddr(k, A[Hash[k]])' = ValOfKeyInBktAtAddr(k, A[Hash[k]])
                OBVIOUS
              <7> bkt_arr == MemLocs'[A'[Hash[k]]]
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
              <7>1. ValOfKeyInBktAtAddr(k, A[Hash[k]])' = bkt_arr[idx].val
                BY DEF ValOfKeyInBktAtAddr
              <7>2. bkt_arr = MemLocs[A[Hash[k]]]
                BY Zenon
              <7> QED
                BY <7>1, <7>2, ZenonT(30) DEF ValOfKeyInBktAtAddr
            <6> QED
              BY <6>1, <6>2, <6>3
          <5>2. ASSUME NEW q \in ProcSet
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
            <6> USE <5>2
            <6>A. \A k \in KeyDomain : KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, bucket[q])'
              BY Zenon DEF KeyInBktAtAddr
            <6>B. \A k \in KeyDomain : ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, bucket[q])
              <7> SUFFICES ASSUME NEW k \in KeyDomain
                           PROVE  ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, bucket[q])
                OBVIOUS
              <7> bkt_arr == MemLocs'[bucket'[q]]
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
              <7>1. ValOfKeyInBktAtAddr(k, bucket[q])' = bkt_arr[idx].val
                BY DEF ValOfKeyInBktAtAddr
              <7>2. bkt_arr = MemLocs[bucket[q]]
                BY Zenon
              <7> QED
                BY <7>1, <7>2, ZenonT(30) DEF ValOfKeyInBktAtAddr
            <6>1. CASE pc[q] = RemainderID
              <7> USE <6>1
              <7> SUFFICES c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
                BY RemDef, Zenon
              <7>1. pc'[q] = RemainderID
                BY RemDef, Zenon
              <7>2. c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2
            <6>2. CASE pc[q] = "F1"
              <7> USE <6>2
              <7> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY RemDef, Zenon
              <7>1. pc'[q] = "F1"
                BY RemDef, Zenon
              <7>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2
            <6>3. CASE pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
              <7> USE <6>3
              <7> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                BY RemDef, Zenon
              <7>1. pc'[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                BY RemDef, Zenon DEF KeyInBktAtAddr
              <7>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
                BY <7>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7>3. arg[q].key = arg'[q].key /\ arg[q].key \in KeyDomain
                BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
              <7>4. c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                BY <7>2, <7>3, <6>B
              <7> QED
                BY <7>2, <7>4
            <6>4. CASE pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
              <7> USE <6>4
              <7> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                BY RemDef, Zenon
              <7>2. pc'[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                BY RemDef, Zenon DEF KeyInBktAtAddr
              <7>3. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                BY <7>2,  SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>3
            <6>5. CASE pc[q] = "F3"
              <7> USE <6>5
              <7> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY RemDef, Zenon
              <7>1. pc'[q] = "F3"
                BY RemDef, Zenon
              <7>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2 
            <6>6. CASE pc[q] \in {"I1", "I3", "I4"}
              <7> USE <6>6
              <7> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY RemDef, Zenon
              <7>1. pc'[q] \in {"I1", "I3", "I4"}
                BY RemDef, Zenon
              <7>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2 
            <6>7. CASE pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
              <7> USE <6>7
              <7> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                BY RemDef, Zenon
              <7>1. CASE p = q
                <8> USE <7>1
                <8>1. c.op[p] = "Insert" /\ c.arg[p] = arg[p] /\ c.res[p] = r'[p]
                  BY SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8>2. r'[p] = ValOfKeyInBktAtAddr(arg[p].key, bucket[p])
                  BY Zenon
                <8> QED
                  BY <8>1, <8>2
              <7> SUFFICES ASSUME p # q
                           PROVE  c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                BY <7>1
              <7>2. pc'[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                BY RemDef, Zenon DEF KeyInBktAtAddr
              <7>3. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
                BY <7>2,  SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7>4. arg[q].key = arg'[q].key /\ arg[q].key \in KeyDomain
                BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
              <7>5. c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                BY <7>3, <7>4, <6>B
              <7> QED
                BY <7>3, <7>5
            <6>8. CASE pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
              <7> USE <6>8
              <7> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY RemDef, Zenon
              <7>1. CASE p = q
                <8> USE <7>1
                <8>1. c.op[p] = "Insert" /\ c.arg[p] = arg[p] /\ c.res[p] = BOT
                  BY SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>1
              <7> SUFFICES ASSUME p # q
                           PROVE  c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <7>1
              <7>2. pc'[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                BY RemDef, Zenon DEF KeyInBktAtAddr
              <7>3. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <7>2, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>3 
            <6>9. CASE pc[q] = "I5"
              <7> USE <6>9
              <7> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY RemDef, Zenon
              <7>1. pc'[q] = "I5"
                BY RemDef, Zenon 
              <7>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2 
            <6>10. CASE pc[q] \in {"U1", "U2", "U3", "U4"}
              <7> USE <6>10
              <7> SUFFICES c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY RemDef, Zenon
              <7>1. pc'[q] \in {"U1", "U2", "U3", "U4"}
                BY RemDef, Zenon
              <7>2. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2
            <6>11. CASE pc[q] = "U5" 
              <7> USE <6>11
              <7> SUFFICES c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY RemDef, Zenon
              <7>1. pc'[q] = "U5"
                BY RemDef, Zenon
              <7>2. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2
            <6>12. CASE pc[q] \in {"R1", "R3", "R4"}
              <7> USE <6>12
              <7> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY RemDef, Zenon
              <7>1. pc'[q] \in {"R1", "R3", "R4"}
                BY RemDef, Zenon
              <7>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2
            <6>13. CASE pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
              <7> USE <6>13
              <7> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY RemDef, Zenon
              <7>1. pc'[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                BY RemDef, Zenon DEF KeyInBktAtAddr
              <7>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2
            <6>14. CASE pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
              <7> USE <6>14
              <7> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                BY RemDef, Zenon
              <7>1. pc'[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                BY RemDef, Zenon DEF KeyInBktAtAddr
              <7>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2
            <6>15. CASE pc[q] = "R5"
              <7> USE <6>15
              <7> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY RemDef, Zenon
              <7>1. pc'[q] = "R5" 
                BY RemDef, Zenon
              <7>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2
            <6> QED
                BY RemDef, ZenonT(120),
                    <6>1, <6>2, <6>3, <6>4, <6>5, <6>6, <6>7, <6>8, <6>9, 
                    <6>10, <6>11, <6>12, <6>13, <6>14, <6>15
                DEF LineIDs
          <5> QED
            BY <5>1, <5>2, Zenon DEF S
        <4> QED
          BY <4>1, <4>2
      <3>7. CASE Line = U1(p)
        <4> USE <3>7 DEF U1
        <4> SUFFICES ASSUME NEW c \in ConfigDomain,
                     c \in S'
                     PROVE c \in P'
          BY Zenon DEF InvL1, S
        <4>1. ASSUME c \in S
              PROVE  c \in P'
          <5> USE <4>1
          <5>1. c \in P
            BY DEF InvL1
          <5>2. c \in Evolve(P)
            BY <5>1, EmptySeqEvolve
          <5> QED
            BY <5>2
        <4> SUFFICES c \in S
          BY <4>1
        <4>2. c \in S
          <5>1. c.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL]
            <6>1. c.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]])' THEN ValOfKeyInBktAtAddr(k, A[Hash[k]])' ELSE NULL]
              BY Zenon, SPrimeRewrite DEF SPrime
            <6>2. \A k \in KeyDomain : /\ KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
                                       /\ ValOfKeyInBktAtAddr(k, A[Hash[k]]) = ValOfKeyInBktAtAddr(k, A[Hash[k]])'
              <7> SUFFICES ASSUME NEW k \in KeyDomain
                           PROVE  /\ KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
                                  /\ ValOfKeyInBktAtAddr(k, A[Hash[k]]) = ValOfKeyInBktAtAddr(k, A[Hash[k]])'
                OBVIOUS
              <7>1. KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
                BY Zenon DEF KeyInBktAtAddr
              <7>2. ValOfKeyInBktAtAddr(k, A[Hash[k]]) = ValOfKeyInBktAtAddr(k, A[Hash[k]])'
                <8> DEFINE bkt_arr == MemLocs'[A'[Hash[k]]]
                <8> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
                <8>1. ValOfKeyInBktAtAddr(k, A[Hash[k]])' = bkt_arr[idx].val
                  BY Zenon DEF ValOfKeyInBktAtAddr
                <8>2. bkt_arr = MemLocs[A[Hash[k]]]
                  BY Zenon
                <8>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
                  BY Zenon
                <8> QED
                  BY <8>1, <8>2, <8>3, Isa DEF ValOfKeyInBktAtAddr
              <7> QED
                BY <7>1, <7>2
            <6> QED
              BY <6>1, <6>2 
          <5>2. ASSUME NEW q \in ProcSet
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
            <6>A. q # p => \A k \in KeyDomain : KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, bucket[q])'
              BY Zenon DEF KeyInBktAtAddr
            <6>B. q # p => \A k \in KeyDomain : ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, bucket[q])
              <7> SUFFICES ASSUME NEW k \in KeyDomain, q # p
                           PROVE  ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, bucket[q])
                OBVIOUS
              <7> bkt_arr == MemLocs'[bucket'[q]]
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
              <7>1. ValOfKeyInBktAtAddr(k, bucket[q])' = bkt_arr[idx].val
                BY DEF ValOfKeyInBktAtAddr
              <7>2. bkt_arr = MemLocs[bucket[q]]
                BY Zenon
              <7> QED
                BY <7>1, <7>2, ZenonT(30) DEF ValOfKeyInBktAtAddr
            <6>1. CASE pc[q] = RemainderID
              <7> USE <6>1
              <7> SUFFICES c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
                BY RemDef, Zenon
              <7>1. pc'[q] = RemainderID
                BY RemDef, Zenon
              <7>2. c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2
            <6>2. CASE pc[q] = "F1"
              <7> USE <6>2
              <7> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY RemDef, Zenon
              <7>1. pc'[q] = "F1"
                BY RemDef, Zenon
              <7>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2
            <6>3. CASE pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
              <7> USE <6>3
              <7> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                BY RemDef, Zenon
              <7>1. q # p
                BY Zenon
              <7>2. pc'[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                BY RemDef, Zenon DEF KeyInBktAtAddr
              <7>3. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
                BY <7>2,  SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7>4. arg[q].key = arg'[q].key /\ arg[q].key \in KeyDomain
                BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
              <7>5. c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                BY <7>3, <7>4, <6>B, <7>1
              <7> QED
                BY <7>3, <7>5
            <6>4. CASE pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
              <7> USE <6>4
              <7> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                BY RemDef, Zenon
              <7>2. pc'[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                BY RemDef, Zenon DEF KeyInBktAtAddr
              <7>3. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                BY <7>2,  SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>3
            <6>5. CASE pc[q] = "F3"
              <7> USE <6>5
              <7> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY RemDef, Zenon
              <7>1. pc'[q] = "F3"
                BY RemDef, Zenon
              <7>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2 
            <6>6. CASE pc[q] \in {"I1", "I3", "I4"}
              <7> USE <6>6
              <7> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY RemDef, Zenon
              <7>1. pc'[q] \in {"I1", "I3", "I4"}
                BY RemDef, Zenon
              <7>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2
            <6>7. CASE pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
              <7> USE <6>7
              <7> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                BY RemDef, Zenon
              <7>1. q # p 
                BY Zenon
              <7>2. pc'[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                BY RemDef, Zenon DEF KeyInBktAtAddr
              <7>3. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
                BY <7>2,  SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7>4. arg[q].key = arg'[q].key /\ arg[q].key \in KeyDomain
                BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
              <7>5. c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                BY <7>3, <7>4, <6>B, <7>1
              <7> QED
                BY <7>3, <7>5
            <6>8. CASE pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
              <7> USE <6>8
              <7> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY RemDef, Zenon
              <7>2. pc'[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                BY RemDef, Zenon DEF KeyInBktAtAddr
              <7>3. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <7>2,  SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>3
            <6>9. CASE pc[q] = "I5"
              <7> USE <6>9
              <7> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY RemDef, Zenon
              <7>1. pc'[q] = "I5"
                BY RemDef, Zenon 
              <7>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2 
            <6>10. CASE pc[q] \in {"U1", "U2", "U3", "U4"}
              <7> USE <6>10
              <7> SUFFICES c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY RemDef, Zenon
              <7>1. pc'[q] \in {"U1", "U2", "U3", "U4"}
                BY RemDef, Zenon
              <7>2. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2
            <6>11. CASE pc[q] = "U5" 
              <7> USE <6>11
              <7> SUFFICES c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY RemDef, Zenon
              <7>1. pc'[q] = "U5"
                BY RemDef, Zenon
              <7>2. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2
            <6>12. CASE pc[q] \in {"R1", "R3", "R4"}
              <7> USE <6>12
              <7> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY RemDef, Zenon
              <7>1. pc'[q] \in {"R1", "R3", "R4"}
                BY RemDef, Zenon
              <7>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2
            <6>13. CASE pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
              <7> USE <6>13
              <7> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY RemDef, Zenon
              <7>1. pc'[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                BY RemDef, Zenon DEF KeyInBktAtAddr
              <7>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2
            <6>14. CASE pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
              <7> USE <6>14
              <7> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                BY RemDef, Zenon
              <7>1. pc'[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                BY RemDef, Zenon DEF KeyInBktAtAddr
              <7>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2
            <6>15. CASE pc[q] = "R5"
              <7> USE <6>15
              <7> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY RemDef, Zenon
              <7>1. pc'[q] = "R5" 
                BY RemDef, Zenon
              <7>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2
            <6> QED
                BY RemDef, ZenonT(120),
                    <6>1, <6>2, <6>3, <6>4, <6>5, <6>6, <6>7, <6>8, <6>9, 
                    <6>10, <6>11, <6>12, <6>13, <6>14, <6>15
                DEF LineIDs
          <5> QED
            BY <5>1, <5>2, Zenon DEF S
        <4> QED
          BY <4>2      
      <3>8. CASE Line = U2(p)
        <4> USE <3>8 DEF U2
        <4> SUFFICES ASSUME NEW c \in ConfigDomain,
                            c \in S'
                     PROVE  c \in P'
          BY Zenon DEF InvL1, S
        <4>1. c \in S
          <5>1. c.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL]
            <6>1. c.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]])' THEN ValOfKeyInBktAtAddr(k, A[Hash[k]])' ELSE NULL]
              BY Zenon, SPrimeRewrite DEF SPrime
            <6>2. \A k \in KeyDomain : KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
              BY Zenon DEF KeyInBktAtAddr
            <6>3. \A k \in KeyDomain : ValOfKeyInBktAtAddr(k, A[Hash[k]])' = ValOfKeyInBktAtAddr(k, A[Hash[k]])
              <7> SUFFICES ASSUME NEW k \in KeyDomain
                           PROVE  ValOfKeyInBktAtAddr(k, A[Hash[k]])' = ValOfKeyInBktAtAddr(k, A[Hash[k]])
                OBVIOUS
              <7> bkt_arr == MemLocs'[A'[Hash[k]]]
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
              <7>1. ValOfKeyInBktAtAddr(k, A[Hash[k]])' = bkt_arr[idx].val
                BY DEF ValOfKeyInBktAtAddr
              <7>2. bkt_arr = MemLocs[A[Hash[k]]]
                BY Zenon
              <7> QED
                BY <7>1, <7>2, ZenonT(30) DEF ValOfKeyInBktAtAddr
            <6> QED
              BY <6>1, <6>2, <6>3
          <5>2. ASSUME NEW q \in ProcSet
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
            <6> USE <5>2
            <6>A. \A k \in KeyDomain : KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, bucket[q])'
              BY Zenon DEF KeyInBktAtAddr
            <6>B. \A k \in KeyDomain : ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, bucket[q])
              <7> SUFFICES ASSUME NEW k \in KeyDomain
                           PROVE  ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, bucket[q])
                OBVIOUS
              <7> bkt_arr == MemLocs'[bucket'[q]]
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
              <7>1. ValOfKeyInBktAtAddr(k, bucket[q])' = bkt_arr[idx].val
                BY DEF ValOfKeyInBktAtAddr
              <7>2. bkt_arr = MemLocs[bucket[q]]
                BY Zenon
              <7> QED
                BY <7>1, <7>2, ZenonT(30) DEF ValOfKeyInBktAtAddr
            <6>1. CASE pc[q] = RemainderID
              <7> USE <6>1
              <7> SUFFICES c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
                BY RemDef, Zenon
              <7>1. pc'[q] = RemainderID
                BY RemDef, Zenon
              <7>2. c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2
            <6>2. CASE pc[q] = "F1"
              <7> USE <6>2
              <7> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY RemDef, Zenon
              <7>1. pc'[q] = "F1"
                BY RemDef, Zenon
              <7>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2
            <6>3. CASE pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
              <7> USE <6>3
              <7> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                BY RemDef, Zenon
              <7>1. CASE q = p
                <8> USE <7>1
                <8>1. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r'[q]
                  BY SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                  BY <8>1, Zenon
                <8> QED
                  BY <8>2
              <7> SUFFICES ASSUME q # p
                           PROVE  c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                BY <7>1
              <7>2. pc'[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                BY RemDef, Zenon DEF KeyInBktAtAddr
              <7>3. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
                BY <7>2,  SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7>4. arg[q].key = arg'[q].key /\ arg[q].key \in KeyDomain
                BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
              <7>5. c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                BY <7>3, <7>4, <6>B
              <7> QED
                BY <7>3, <7>5
            <6>4. CASE pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
              <7> USE <6>4
              <7> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                BY RemDef, Zenon
              <7>1. CASE q = p
                <8> USE <7>1
                <8>1. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r'[q]
                  BY SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                  BY <8>1, Zenon
                <8> QED
                  BY <8>2
              <7> SUFFICES ASSUME q # p
                           PROVE  c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                BY <7>1
              <7>2. pc'[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                BY RemDef, Zenon DEF KeyInBktAtAddr
              <7>3. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                BY <7>2,  SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>3
            <6>5. CASE pc[q] = "F3"
              <7> USE <6>5
              <7> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY RemDef, Zenon
              <7>1. pc'[q] = "F3"
                BY RemDef, Zenon
              <7>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2 
            <6>6. CASE pc[q] \in {"I1", "I3", "I4"}
              <7> USE <6>6
              <7> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY RemDef, Zenon
              <7>1. pc'[q] \in {"I1", "I3", "I4"}
                BY RemDef, Zenon
              <7>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2 
            <6>7. CASE pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
              <7> USE <6>7
              <7> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                BY RemDef, Zenon
              <7>2. pc'[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                BY RemDef, Zenon DEF KeyInBktAtAddr
              <7>3. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
                BY <7>2,  SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7>4. arg[q].key = arg'[q].key /\ arg[q].key \in KeyDomain
                BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
              <7>5. c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                BY <7>3, <7>4, <6>B
              <7> QED
                BY <7>3, <7>5
            <6>8. CASE pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
              <7> USE <6>8
              <7> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY RemDef, Zenon
              <7>1. pc'[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                BY RemDef, Zenon DEF KeyInBktAtAddr
              <7>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2 
            <6>9. CASE pc[q] = "I5"
              <7> USE <6>9
              <7> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY RemDef, Zenon
              <7>1. pc'[q] = "I5"
                BY RemDef, Zenon 
              <7>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2 
            <6>10. CASE pc[q] \in {"U1", "U2", "U3", "U4"}
              <7> USE <6>10
              <7> SUFFICES c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY RemDef, Zenon
              <7>1. pc'[q] \in {"U1", "U2", "U3", "U4"}
                BY RemDef, Zenon
              <7>2. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2
            <6>11. CASE pc[q] = "U5" 
              <7> USE <6>11
              <7> SUFFICES c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY RemDef, Zenon
              <7>1. pc'[q] = "U5"
                BY RemDef, Zenon
              <7>2. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2
            <6>12. CASE pc[q] \in {"R1", "R3", "R4"}
              <7> USE <6>12
              <7> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY RemDef, Zenon
              <7>1. pc'[q] \in {"R1", "R3", "R4"}
                BY RemDef, Zenon
              <7>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2
            <6>13. CASE pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
              <7> USE <6>13
              <7> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY RemDef, Zenon
              <7>1. pc'[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                BY RemDef, Zenon DEF KeyInBktAtAddr
              <7>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2
            <6>14. CASE pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
              <7> USE <6>14
              <7> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                BY RemDef, Zenon
              <7>1. pc'[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                BY RemDef, Zenon DEF KeyInBktAtAddr
              <7>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2
            <6>15. CASE pc[q] = "R5"
              <7> USE <6>15
              <7> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY RemDef, Zenon
              <7>1. pc'[q] = "R5" 
                BY RemDef, Zenon
              <7>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2
            <6> QED
                BY RemDef, ZenonT(120),
                    <6>1, <6>2, <6>3, <6>4, <6>5, <6>6, <6>7, <6>8, <6>9, 
                    <6>10, <6>11, <6>12, <6>13, <6>14, <6>15
                DEF LineIDs
          <5> QED
            BY <5>1, <5>2, Zenon DEF S
        <4>2. c \in P
          BY <4>1 DEF InvL1
        <4>3. c \in Evolve(P)
          BY <4>2, EmptySeqEvolve
        <4> QED
          BY <4>3
      <3>9. CASE Line = U3(p)
        <4> USE <3>9
        <4> SUFFICES ASSUME NEW c \in ConfigDomain,
                            c \in S'
                     PROVE  c \in P'
          BY Zenon DEF InvL1, S
        <4>1. CASE bucket[p] = NULL
          <5> PICK addr \in Addrs : 
                   /\ addr \notin AllocAddrs
                   /\ AllocAddrs' = AllocAddrs \cup {addr}
                   /\ newbkt' = [newbkt EXCEPT ![p] = addr]
                   /\ MemLocs' = [MemLocs EXCEPT ![addr] = <<arg[p]>>]
            BY <4>1, Zenon DEF U3
          <5> /\ pc[p] = "U3"
              /\ pc' = [pc EXCEPT ![p] = "U4"]
              /\ UNCHANGED <<A, bucket, r, arg, ret>>
            BY Zenon DEF U3
          <5>1. c \in S
            <6>1. c.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL]
              <7>1. c.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]])' THEN ValOfKeyInBktAtAddr(k, A[Hash[k]])' ELSE NULL]
                BY Zenon, SPrimeRewrite DEF SPrime
              <7>2. \A k \in KeyDomain : KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
                <8> SUFFICES ASSUME NEW k \in KeyDomain
                             PROVE  KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
                  OBVIOUS
                <8>1. A'[Hash[k]] = A[Hash[k]]
                  BY Zenon
                <8>2. CASE A[Hash[k]] = NULL
                  BY <8>1, <8>2 DEF KeyInBktAtAddr
                <8> SUFFICES ASSUME A[Hash[k]] # NULL
                             PROVE  KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
                  BY <8>2
                <8>3. A[Hash[k]] \in AllocAddrs
                  BY HashDef, Zenon
                <8>4. A[Hash[k]] # addr
                  BY NULLDef, <8>3
                <8>5. \A a \in Addrs : a # addr => MemLocs'[a] = MemLocs[a]
                  BY Zenon
                <8>6. MemLocs'[A'[Hash[k]]] = MemLocs[A[Hash[k]]]
                  BY <8>1, <8>4, <8>5
                <8> QED
                  BY <8>6, Zenon DEF KeyInBktAtAddr
              <7>3. \A k \in KeyDomain : KeyInBktAtAddr(k, A[Hash[k]]) => (ValOfKeyInBktAtAddr(k, A[Hash[k]]) = ValOfKeyInBktAtAddr(k, A[Hash[k]])')
                <8> SUFFICES ASSUME NEW k \in KeyDomain,
                                    NEW bkt_arr,
                                    A[Hash[k]] # NULL,
                                    bkt_arr = MemLocs[A[Hash[k]]],
                                    \E index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
                             PROVE  ValOfKeyInBktAtAddr(k, A[Hash[k]]) = ValOfKeyInBktAtAddr(k, A[Hash[k]])'
                  BY Zenon DEF KeyInBktAtAddr
                <8>1. A'[Hash[k]] = A[Hash[k]]
                  BY Zenon
                <8>2. A[Hash[k]] \in AllocAddrs
                  BY HashDef, Zenon
                <8>3. A[Hash[k]] # addr
                  BY NULLDef, <8>2
                <8>4. \A a \in Addrs : a # addr => MemLocs'[a] = MemLocs[a]
                  BY Zenon
                <8>5. MemLocs'[A'[Hash[k]]] = MemLocs[A[Hash[k]]]
                  BY <8>1, <8>3, <8>4
                <8> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
                <8>6. ValOfKeyInBktAtAddr(k, A[Hash[k]]) = bkt_arr[idx].val
                  BY Zenon DEF ValOfKeyInBktAtAddr
                <8>7. ValOfKeyInBktAtAddr(k, A[Hash[k]])' = bkt_arr[idx].val
                  BY Isa, <8>5 DEF ValOfKeyInBktAtAddr
                <8> QED
                  BY <8>6, <8>7, Zenon
              <7> QED
                BY <7>1, <7>2, <7>3, Zenon
            <6>2. ASSUME NEW q \in ProcSet
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
              <7> USE <6>2
              <7>A. KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
                <8>1. bucket[q] = bucket'[q]
                  BY Zenon
                <8>2. CASE bucket[q] = NULL
                  BY <8>1, <8>2, Zenon DEF KeyInBktAtAddr
                <8> SUFFICES ASSUME bucket[q] # NULL
                             PROVE  KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY <8>2
                <8>3. bucket[q] \in AllocAddrs
                  BY NULLDef, Zenon
                <8>4. bucket[q] # addr
                  BY <8>3
                <8>5. \A a \in Addrs : a # addr => MemLocs'[a] = MemLocs[a]
                  BY Zenon
                <8>6. MemLocs'[bucket'[q]] = MemLocs[bucket[q]]
                  BY <8>1, <8>4, <8>5
                <8> QED
                  BY <8>6, Zenon DEF KeyInBktAtAddr
              <7>B. KeyInBktAtAddr(arg[q].key, bucket[q]) => (ValOfKeyInBktAtAddr(arg[q].key, bucket[q]) = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])')
                <8> SUFFICES ASSUME NEW bkt_arr,
                                    bkt_arr = MemLocs[bucket[q]],
                                    bucket[q] # NULL,
                                    \E index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
                             PROVE  ValOfKeyInBktAtAddr(arg[q].key, bucket[q]) = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY Zenon DEF KeyInBktAtAddr
                <8>1. bucket[q] = bucket'[q]
                  BY Zenon
                <8>2. bucket[q] \in AllocAddrs
                  BY NULLDef, Zenon
                <8>3. bucket[q] # addr
                  BY <8>2
                <8>4. \A a \in Addrs : a # addr => MemLocs'[a] = MemLocs[a]
                  BY Zenon
                <8>5. MemLocs'[bucket'[q]] = MemLocs[bucket[q]]
                  BY <8>1, <8>3, <8>4 
                <8> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
                <8>6. ValOfKeyInBktAtAddr(arg[q].key, bucket[q]) = bkt_arr[idx].val
                  BY Zenon DEF ValOfKeyInBktAtAddr
                <8>7. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = bkt_arr[idx].val
                  BY Isa, <8>5 DEF ValOfKeyInBktAtAddr
                <8> QED
                  BY <8>6, <8>7, Zenon
              <7>1. CASE pc[q] = RemainderID
                <8> USE <7>1
                <8> SUFFICES c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
                  BY RemDef, Zenon
                <8>1. pc'[q] = RemainderID
                  BY RemDef, Zenon
                <8>2. c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
                  BY <8>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2
              <7>2. CASE pc[q] = "F1"
                <8> USE <7>2
                <8> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY RemDef, Zenon
                <8>1. pc'[q] = "F1"
                  BY RemDef, Zenon
                <8>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY <8>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2  
              <7>3. CASE pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                <8> USE <7>3
                <8> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                  BY RemDef, Zenon
                <8>1. pc'[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY <7>A, RemDef, Zenon DEF KeyInBktAtAddr
                <8>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY <8>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8>3. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                  BY <7>B, Zenon
                <8> QED
                  BY <8>2, <8>3
              <7>4. CASE pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                <8> USE <7>4
                <8> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                  BY RemDef, Zenon
                <8>1. pc'[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY <7>A, RemDef, Zenon DEF KeyInBktAtAddr
                <8>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                  BY <8>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2
              <7>5. CASE pc[q] = "F3" 
                <8> USE <7>5
                <8> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                  BY RemDef, Zenon
                <8>1. pc'[q] = "F3"
                  BY RemDef, Zenon
                <8>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                  BY <8>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2
              <7>6. CASE pc[q] \in {"I1", "I3", "I4"}
                <8> USE <7>6
                <8> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY RemDef, Zenon
                <8>2. pc'[q] \in {"I1", "I3", "I4"}
                  BY RemDef, Zenon
                <8>3. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY <8>2,  SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>3
              <7>7. CASE pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                <8> USE <7>7
                <8> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                  BY RemDef, Zenon
                <8>1. pc'[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY <7>A, RemDef, Zenon DEF KeyInBktAtAddr
                <8>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY <8>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8>3. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                  BY <7>B, Zenon
                <8> QED
                  BY <8>2, <8>3
              <7>8. CASE pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                <8> USE <7>8
                <8> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY RemDef, Zenon
                <8>1. pc'[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY <7>A, RemDef, Zenon DEF KeyInBktAtAddr
                <8>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY <8>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2
              <7>9. CASE pc[q] = "I5"
                <8> USE <7>9
                <8> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                  BY RemDef, Zenon
                <8>1. pc'[q] = "I5"
                  BY RemDef, Zenon
                <8>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                  BY <8>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2
              <7>10. CASE pc[q] \in {"U1", "U2", "U3", "U4"}
                <8> USE <7>10
                <8> SUFFICES c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY RemDef, Zenon
                <8>1. pc'[q] \in {"U1", "U2", "U3", "U4"}
                  BY RemDef, Zenon
                <8>2. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY <8>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2
              <7>11. CASE pc[q] = "U5" 
                <8> USE <7>11
                <8> SUFFICES c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                  BY RemDef, Zenon
                <8>1. pc'[q] = "U5"
                  BY RemDef, Zenon
                <8>2. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                  BY <8>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2
              <7>12. CASE pc[q] \in {"R1", "R3", "R4"}
                <8> USE <7>12
                <8> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY RemDef, Zenon
                <8>1. pc'[q] \in {"R1", "R3", "R4"}
                  BY RemDef, Zenon
                <8>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY <8>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2
              <7>13. CASE pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                <8> USE <7>13
                <8> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY RemDef, Zenon
                <8>1. pc'[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY <7>A, RemDef, Zenon DEF KeyInBktAtAddr
                <8>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY <8>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2
              <7>14. CASE pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                <8> USE <7>14
                <8> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                  BY RemDef, Zenon
                <8>1. pc'[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY <7>A, RemDef, Zenon DEF KeyInBktAtAddr
                <8>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                  BY <8>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2
              <7>15. CASE pc[q] = "R5"
                <8> USE <7>15
                <8> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                  BY RemDef, Zenon
                <8>1. pc'[q] = "R5"
                  BY RemDef, Zenon
                <8>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                  BY <8>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2
              <7> QED
                  BY RemDef, ZenonT(120),
                     <7>1, <7>2, <7>3, <7>4, <7>5, <7>6, <7>7, <7>8, <7>9, 
                     <7>10, <7>11, <7>12, <7>13, <7>14, <7>15
                  DEF LineIDs
            <6> QED
              BY <6>1, <6>2, Zenon DEF S
          <5>2. c \in P
            BY <5>1 DEF InvL1
          <5>3. c \in Evolve(P)
            BY <5>2, EmptySeqEvolve
          <5> QED
            BY <5>3
        <4>2. CASE bucket[p] # NULL /\ r[p] = NULL
          <5> PICK addr \in Addrs : 
                   /\ addr \notin AllocAddrs
                   /\ AllocAddrs' = AllocAddrs \cup {addr}
                   /\ newbkt' = [newbkt EXCEPT ![p] = addr]
                   /\ MemLocs' = [MemLocs EXCEPT ![addr] = Append(MemLocs[bucket[p]], arg[p])]
            BY <4>2, Zenon DEF U3
          <5> /\ pc[p] = "U3"
              /\ pc' = [pc EXCEPT ![p] = "U4"]
              /\ UNCHANGED <<A, bucket, r, arg, ret>>
            BY Zenon DEF U3
          <5>1. c \in S
            <6>1. c.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL]
              <7>1. c.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]])' THEN ValOfKeyInBktAtAddr(k, A[Hash[k]])' ELSE NULL]
                BY Zenon, SPrimeRewrite DEF SPrime
              <7>2. \A k \in KeyDomain : KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
                <8> SUFFICES ASSUME NEW k \in KeyDomain
                             PROVE  KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
                  OBVIOUS
                <8>1. A'[Hash[k]] = A[Hash[k]]
                  BY Zenon
                <8>2. CASE A[Hash[k]] = NULL
                  BY <8>1, <8>2 DEF KeyInBktAtAddr
                <8> SUFFICES ASSUME A[Hash[k]] # NULL
                             PROVE  KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
                  BY <8>2
                <8>3. A[Hash[k]] \in AllocAddrs
                  BY HashDef, Zenon
                <8>4. A[Hash[k]] # addr
                  BY NULLDef, <8>3
                <8>5. \A a \in Addrs : a # addr => MemLocs'[a] = MemLocs[a]
                  BY Zenon
                <8>6. MemLocs'[A'[Hash[k]]] = MemLocs[A[Hash[k]]]
                  BY <8>1, <8>4, <8>5
                <8> QED
                  BY <8>6, Zenon DEF KeyInBktAtAddr
              <7>3. \A k \in KeyDomain : KeyInBktAtAddr(k, A[Hash[k]]) => (ValOfKeyInBktAtAddr(k, A[Hash[k]]) = ValOfKeyInBktAtAddr(k, A[Hash[k]])')
                <8> SUFFICES ASSUME NEW k \in KeyDomain,
                                    NEW bkt_arr,
                                    A[Hash[k]] # NULL,
                                    bkt_arr = MemLocs[A[Hash[k]]],
                                    \E index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
                             PROVE  ValOfKeyInBktAtAddr(k, A[Hash[k]]) = ValOfKeyInBktAtAddr(k, A[Hash[k]])'
                  BY Zenon DEF KeyInBktAtAddr
                <8>1. A'[Hash[k]] = A[Hash[k]]
                  BY Zenon
                <8>2. A[Hash[k]] \in AllocAddrs
                  BY HashDef, Zenon
                <8>3. A[Hash[k]] # addr
                  BY NULLDef, <8>2
                <8>4. \A a \in Addrs : a # addr => MemLocs'[a] = MemLocs[a]
                  BY Zenon
                <8>5. MemLocs'[A'[Hash[k]]] = MemLocs[A[Hash[k]]]
                  BY <8>1, <8>3, <8>4
                <8> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
                <8>6. ValOfKeyInBktAtAddr(k, A[Hash[k]]) = bkt_arr[idx].val
                  BY Zenon DEF ValOfKeyInBktAtAddr
                <8>7. ValOfKeyInBktAtAddr(k, A[Hash[k]])' = bkt_arr[idx].val
                  BY Isa, <8>5 DEF ValOfKeyInBktAtAddr
                <8> QED
                  BY <8>6, <8>7, Zenon
              <7> QED
                BY <7>1, <7>2, <7>3, Zenon
            <6>2. ASSUME NEW q \in ProcSet
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
              <7> USE <6>2
              <7>A. KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
                <8>1. bucket[q] = bucket'[q]
                  BY Zenon
                <8>2. CASE bucket[q] = NULL
                  BY <8>1, <8>2, Zenon DEF KeyInBktAtAddr
                <8> SUFFICES ASSUME bucket[q] # NULL
                             PROVE  KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY <8>2
                <8>3. bucket[q] \in AllocAddrs
                  BY NULLDef, Zenon
                <8>4. bucket[q] # addr
                  BY <8>3
                <8>5. \A a \in Addrs : a # addr => MemLocs'[a] = MemLocs[a]
                  BY Zenon
                <8>6. MemLocs'[bucket'[q]] = MemLocs[bucket[q]]
                  BY <8>1, <8>4, <8>5
                <8> QED
                  BY <8>6, Zenon DEF KeyInBktAtAddr
              <7>B. KeyInBktAtAddr(arg[q].key, bucket[q]) => (ValOfKeyInBktAtAddr(arg[q].key, bucket[q]) = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])')
                <8> SUFFICES ASSUME NEW bkt_arr,
                                    bkt_arr = MemLocs[bucket[q]],
                                    bucket[q] # NULL,
                                    \E index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
                             PROVE  ValOfKeyInBktAtAddr(arg[q].key, bucket[q]) = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY Zenon DEF KeyInBktAtAddr
                <8>1. bucket[q] = bucket'[q]
                  BY Zenon
                <8>2. bucket[q] \in AllocAddrs
                  BY NULLDef, Zenon
                <8>3. bucket[q] # addr
                  BY <8>2
                <8>4. \A a \in Addrs : a # addr => MemLocs'[a] = MemLocs[a]
                  BY Zenon
                <8>5. MemLocs'[bucket'[q]] = MemLocs[bucket[q]]
                  BY <8>1, <8>3, <8>4 
                <8> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
                <8>6. ValOfKeyInBktAtAddr(arg[q].key, bucket[q]) = bkt_arr[idx].val
                  BY Zenon DEF ValOfKeyInBktAtAddr
                <8>7. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = bkt_arr[idx].val
                  BY Isa, <8>5 DEF ValOfKeyInBktAtAddr
                <8> QED
                  BY <8>6, <8>7, Zenon
              <7>1. CASE pc[q] = RemainderID
                <8> USE <7>1
                <8> SUFFICES c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
                  BY RemDef, Zenon
                <8>1. pc'[q] = RemainderID
                  BY RemDef, Zenon
                <8>2. c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
                  BY <8>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2
              <7>2. CASE pc[q] = "F1"
                <8> USE <7>2
                <8> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY RemDef, Zenon
                <8>1. pc'[q] = "F1"
                  BY RemDef, Zenon
                <8>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY <8>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2  
              <7>3. CASE pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                <8> USE <7>3
                <8> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                  BY RemDef, Zenon
                <8>1. pc'[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY <7>A, RemDef, Zenon DEF KeyInBktAtAddr
                <8>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY <8>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8>3. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                  BY <7>B, Zenon
                <8> QED
                  BY <8>2, <8>3
              <7>4. CASE pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                <8> USE <7>4
                <8> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                  BY RemDef, Zenon
                <8>1. pc'[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY <7>A, RemDef, Zenon DEF KeyInBktAtAddr
                <8>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                  BY <8>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2
              <7>5. CASE pc[q] = "F3" 
                <8> USE <7>5
                <8> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                  BY RemDef, Zenon
                <8>1. pc'[q] = "F3"
                  BY RemDef, Zenon
                <8>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                  BY <8>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2
              <7>6. CASE pc[q] \in {"I1", "I3", "I4"}
                <8> USE <7>6
                <8> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY RemDef, Zenon
                <8>2. pc'[q] \in {"I1", "I3", "I4"}
                  BY RemDef, Zenon
                <8>3. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY <8>2,  SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>3
              <7>7. CASE pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                <8> USE <7>7
                <8> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                  BY RemDef, Zenon
                <8>1. pc'[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY <7>A, RemDef, Zenon DEF KeyInBktAtAddr
                <8>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY <8>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8>3. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                  BY <7>B, Zenon
                <8> QED
                  BY <8>2, <8>3
              <7>8. CASE pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                <8> USE <7>8
                <8> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY RemDef, Zenon
                <8>1. pc'[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY <7>A, RemDef, Zenon DEF KeyInBktAtAddr
                <8>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY <8>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2
              <7>9. CASE pc[q] = "I5"
                <8> USE <7>9
                <8> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                  BY RemDef, Zenon
                <8>1. pc'[q] = "I5"
                  BY RemDef, Zenon
                <8>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                  BY <8>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2
              <7>10. CASE pc[q] \in {"U1", "U2", "U3", "U4"}
                <8> USE <7>10
                <8> SUFFICES c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY RemDef, Zenon
                <8>1. pc'[q] \in {"U1", "U2", "U3", "U4"}
                  BY RemDef, Zenon
                <8>2. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY <8>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2
              <7>11. CASE pc[q] = "U5" 
                <8> USE <7>11
                <8> SUFFICES c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                  BY RemDef, Zenon
                <8>1. pc'[q] = "U5"
                  BY RemDef, Zenon
                <8>2. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                  BY <8>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2
              <7>12. CASE pc[q] \in {"R1", "R3", "R4"}
                <8> USE <7>12
                <8> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY RemDef, Zenon
                <8>1. pc'[q] \in {"R1", "R3", "R4"}
                  BY RemDef, Zenon
                <8>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY <8>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2
              <7>13. CASE pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                <8> USE <7>13
                <8> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY RemDef, Zenon
                <8>1. pc'[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY <7>A, RemDef, Zenon DEF KeyInBktAtAddr
                <8>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY <8>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2
              <7>14. CASE pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                <8> USE <7>14
                <8> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                  BY RemDef, Zenon
                <8>1. pc'[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY <7>A, RemDef, Zenon DEF KeyInBktAtAddr
                <8>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                  BY <8>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2
              <7>15. CASE pc[q] = "R5"
                <8> USE <7>15
                <8> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                  BY RemDef, Zenon
                <8>1. pc'[q] = "R5"
                  BY RemDef, Zenon
                <8>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                  BY <8>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2
              <7> QED
                  BY RemDef, ZenonT(120),
                     <7>1, <7>2, <7>3, <7>4, <7>5, <7>6, <7>7, <7>8, <7>9, 
                     <7>10, <7>11, <7>12, <7>13, <7>14, <7>15
                  DEF LineIDs
            <6> QED
              BY <6>1, <6>2, Zenon DEF S
          <5>2. c \in P
            BY <5>1 DEF InvL1
          <5>3. c \in Evolve(P)
            BY <5>2, EmptySeqEvolve
          <5> QED
            BY <5>3
        <4>3. CASE bucket[p] # NULL /\ r[p] # NULL
          <5> /\ pc[p] = "U3"
              /\ pc' = [pc EXCEPT ![p] = "U4"]
              /\ UNCHANGED <<A, bucket, r, arg, ret>>
            BY Zenon DEF U3
          <5>A. KeyInBktAtAddr(arg[p].key, bucket[p])
            BY <4>3 DEF BktOK
          <5>B. PICK i \in 1..Len(MemLocs[bucket[p]]) : MemLocs[bucket[p]][i].key = arg[p].key
            BY Zenon, <5>A DEF KeyInBktAtAddr
          <5>C. i = CHOOSE index \in 1..Len(MemLocs[bucket[p]]) : MemLocs[bucket[p]][index].key = arg[p].key
            BY <5>B
          <5>D. i = IdxInBktAtAddr(arg[p].key, bucket[p])
            BY Zenon, <5>C DEF IdxInBktAtAddr
          <5> PICK addr \in Addrs : 
                   /\ addr \notin AllocAddrs
                   /\ AllocAddrs' = AllocAddrs \cup {addr}
                   /\ newbkt' = [newbkt EXCEPT ![p] = addr]
                   /\ MemLocs' = [MemLocs EXCEPT ![addr] = [MemLocs[bucket[p]] EXCEPT ![i] = arg[p]]]
            BY <4>3, <5>D, Zenon DEF U3
          <5> /\ i \in 1..Len(MemLocs[bucket[p]]) 
              /\ MemLocs[bucket[p]][i].key = arg[p].key
            BY <5>B
          <5>1. c \in S
            <6>1. c.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL]
              <7>1. c.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]])' THEN ValOfKeyInBktAtAddr(k, A[Hash[k]])' ELSE NULL]
                BY Zenon, SPrimeRewrite DEF SPrime
              <7>2. \A k \in KeyDomain : KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
                <8> SUFFICES ASSUME NEW k \in KeyDomain
                             PROVE  KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
                  OBVIOUS
                <8>1. A'[Hash[k]] = A[Hash[k]]
                  BY Zenon
                <8>2. CASE A[Hash[k]] = NULL
                  BY <8>1, <8>2 DEF KeyInBktAtAddr
                <8> SUFFICES ASSUME A[Hash[k]] # NULL
                             PROVE  KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
                  BY <8>2
                <8>3. A[Hash[k]] \in AllocAddrs
                  BY HashDef, Zenon
                <8>4. A[Hash[k]] # addr
                  BY NULLDef, <8>3
                <8>5. \A a \in Addrs : a # addr => MemLocs'[a] = MemLocs[a]
                  BY Zenon
                <8>6. MemLocs'[A'[Hash[k]]] = MemLocs[A[Hash[k]]]
                  BY <8>1, <8>4, <8>5
                <8> QED
                  BY <8>6, Zenon DEF KeyInBktAtAddr
              <7>3. \A k \in KeyDomain : KeyInBktAtAddr(k, A[Hash[k]]) => (ValOfKeyInBktAtAddr(k, A[Hash[k]]) = ValOfKeyInBktAtAddr(k, A[Hash[k]])')
                <8> SUFFICES ASSUME NEW k \in KeyDomain,
                                    NEW bkt_arr,
                                    A[Hash[k]] # NULL,
                                    bkt_arr = MemLocs[A[Hash[k]]],
                                    \E index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
                             PROVE  ValOfKeyInBktAtAddr(k, A[Hash[k]]) = ValOfKeyInBktAtAddr(k, A[Hash[k]])'
                  BY Zenon DEF KeyInBktAtAddr
                <8>1. A'[Hash[k]] = A[Hash[k]]
                  BY Zenon
                <8>2. A[Hash[k]] \in AllocAddrs
                  BY HashDef, Zenon
                <8>3. A[Hash[k]] # addr
                  BY NULLDef, <8>2
                <8>4. \A a \in Addrs : a # addr => MemLocs'[a] = MemLocs[a]
                  BY Zenon
                <8>5. MemLocs'[A'[Hash[k]]] = MemLocs[A[Hash[k]]]
                  BY <8>1, <8>3, <8>4
                <8> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
                <8>6. ValOfKeyInBktAtAddr(k, A[Hash[k]]) = bkt_arr[idx].val
                  BY Zenon DEF ValOfKeyInBktAtAddr
                <8>7. ValOfKeyInBktAtAddr(k, A[Hash[k]])' = bkt_arr[idx].val
                  BY Isa, <8>5 DEF ValOfKeyInBktAtAddr
                <8> QED
                  BY <8>6, <8>7, Zenon
              <7> QED
                BY <7>1, <7>2, <7>3, Zenon
            <6>2. ASSUME NEW q \in ProcSet
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
              <7> USE <6>2
              <7>A. KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
                <8>1. bucket[q] = bucket'[q]
                  BY Zenon
                <8>2. CASE bucket[q] = NULL
                  BY <8>1, <8>2, Zenon DEF KeyInBktAtAddr
                <8> SUFFICES ASSUME bucket[q] # NULL
                             PROVE  KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY <8>2
                <8>3. bucket[q] \in AllocAddrs
                  BY NULLDef, Zenon
                <8>4. bucket[q] # addr
                  BY <8>3
                <8>5. \A a \in Addrs : a # addr => MemLocs'[a] = MemLocs[a]
                  BY Zenon
                <8>6. MemLocs'[bucket'[q]] = MemLocs[bucket[q]]
                  BY <8>1, <8>4, <8>5
                <8> QED
                  BY <8>6, Zenon DEF KeyInBktAtAddr
              <7>B. KeyInBktAtAddr(arg[q].key, bucket[q]) => (ValOfKeyInBktAtAddr(arg[q].key, bucket[q]) = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])')
                <8> SUFFICES ASSUME NEW bkt_arr,
                                    bkt_arr = MemLocs[bucket[q]],
                                    bucket[q] # NULL,
                                    \E index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
                             PROVE  ValOfKeyInBktAtAddr(arg[q].key, bucket[q]) = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY Zenon DEF KeyInBktAtAddr
                <8>1. bucket[q] = bucket'[q]
                  BY Zenon
                <8>2. bucket[q] \in AllocAddrs
                  BY NULLDef, Zenon
                <8>3. bucket[q] # addr
                  BY <8>2
                <8>4. \A a \in Addrs : a # addr => MemLocs'[a] = MemLocs[a]
                  BY Zenon
                <8>5. MemLocs'[bucket'[q]] = MemLocs[bucket[q]]
                  BY <8>1, <8>3, <8>4 
                <8> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
                <8>6. ValOfKeyInBktAtAddr(arg[q].key, bucket[q]) = bkt_arr[idx].val
                  BY Zenon DEF ValOfKeyInBktAtAddr
                <8>7. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = bkt_arr[idx].val
                  BY Isa, <8>5 DEF ValOfKeyInBktAtAddr
                <8> QED
                  BY <8>6, <8>7, Zenon
              <7>1. CASE pc[q] = RemainderID
                <8> USE <7>1
                <8> SUFFICES c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
                  BY RemDef, Zenon
                <8>1. pc'[q] = RemainderID
                  BY RemDef, Zenon
                <8>2. c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
                  BY <8>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2
              <7>2. CASE pc[q] = "F1"
                <8> USE <7>2
                <8> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY RemDef, Zenon
                <8>1. pc'[q] = "F1"
                  BY RemDef, Zenon
                <8>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY <8>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2  
              <7>3. CASE pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                <8> USE <7>3
                <8> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                  BY RemDef, Zenon
                <8>1. pc'[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY <7>A, RemDef, Zenon DEF KeyInBktAtAddr
                <8>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY <8>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8>3. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                  BY <7>B, Zenon
                <8> QED
                  BY <8>2, <8>3
              <7>4. CASE pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                <8> USE <7>4
                <8> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                  BY RemDef, Zenon
                <8>1. pc'[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY <7>A, RemDef, Zenon DEF KeyInBktAtAddr
                <8>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                  BY <8>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2
              <7>5. CASE pc[q] = "F3" 
                <8> USE <7>5
                <8> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                  BY RemDef, Zenon
                <8>1. pc'[q] = "F3"
                  BY RemDef, Zenon
                <8>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                  BY <8>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2
              <7>6. CASE pc[q] \in {"I1", "I3", "I4"}
                <8> USE <7>6
                <8> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY RemDef, Zenon
                <8>2. pc'[q] \in {"I1", "I3", "I4"}
                  BY RemDef, Zenon
                <8>3. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY <8>2,  SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>3
              <7>7. CASE pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                <8> USE <7>7
                <8> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                  BY RemDef, Zenon
                <8>1. pc'[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY <7>A, RemDef, Zenon DEF KeyInBktAtAddr
                <8>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY <8>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8>3. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                  BY <7>B, Zenon
                <8> QED
                  BY <8>2, <8>3
              <7>8. CASE pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                <8> USE <7>8
                <8> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY RemDef, Zenon
                <8>1. pc'[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY <7>A, RemDef, Zenon DEF KeyInBktAtAddr
                <8>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY <8>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2
              <7>9. CASE pc[q] = "I5"
                <8> USE <7>9
                <8> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                  BY RemDef, Zenon
                <8>1. pc'[q] = "I5"
                  BY RemDef, Zenon
                <8>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                  BY <8>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2
              <7>10. CASE pc[q] \in {"U1", "U2", "U3", "U4"}
                <8> USE <7>10
                <8> SUFFICES c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY RemDef, Zenon
                <8>1. pc'[q] \in {"U1", "U2", "U3", "U4"}
                  BY RemDef, Zenon
                <8>2. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY <8>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2
              <7>11. CASE pc[q] = "U5" 
                <8> USE <7>11
                <8> SUFFICES c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                  BY RemDef, Zenon
                <8>1. pc'[q] = "U5"
                  BY RemDef, Zenon
                <8>2. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                  BY <8>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2
              <7>12. CASE pc[q] \in {"R1", "R3", "R4"}
                <8> USE <7>12
                <8> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY RemDef, Zenon
                <8>1. pc'[q] \in {"R1", "R3", "R4"}
                  BY RemDef, Zenon
                <8>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY <8>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2
              <7>13. CASE pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                <8> USE <7>13
                <8> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY RemDef, Zenon
                <8>1. pc'[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY <7>A, RemDef, Zenon DEF KeyInBktAtAddr
                <8>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY <8>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2
              <7>14. CASE pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                <8> USE <7>14
                <8> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                  BY RemDef, Zenon
                <8>1. pc'[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY <7>A, RemDef, Zenon DEF KeyInBktAtAddr
                <8>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                  BY <8>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2
              <7>15. CASE pc[q] = "R5"
                <8> USE <7>15
                <8> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                  BY RemDef, Zenon
                <8>1. pc'[q] = "R5"
                  BY RemDef, Zenon
                <8>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                  BY <8>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2
              <7> QED
                  BY RemDef, ZenonT(120),
                     <7>1, <7>2, <7>3, <7>4, <7>5, <7>6, <7>7, <7>8, <7>9, 
                     <7>10, <7>11, <7>12, <7>13, <7>14, <7>15
                  DEF LineIDs
            <6> QED
              BY <6>1, <6>2, Zenon DEF S
          <5>2. c \in P
            BY <5>1 DEF InvL1
          <5>3. c \in Evolve(P)
            BY <5>2, EmptySeqEvolve
          <5> QED
            BY <5>3
        <4> QED
          BY <4>1, <4>2, <4>3
      <3>10. CASE Line = U4(p)
        <4> USE <3>10 DEF U4
        <4> SUFFICES ASSUME NEW c \in ConfigDomain,
                     c \in S'
                     PROVE c \in P'
          BY Zenon DEF InvL1, S
        <4>1. CASE A[Hash[arg[p].key]] = bucket[p]
          <5> USE <4>1
          <5> DEFINE c_pred == [state |-> [c.state EXCEPT ![arg[p].key] = 
                                           IF KeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]]) THEN ValOfKeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]]) ELSE NULL],
                                op    |-> c.op,
                                arg   |-> c.arg,
                                res   |-> [c.res EXCEPT ![p] = BOT]]
          <5>1. c_pred \in ConfigDomain
            <6>1. c_pred.state \in StateDomain
              <7>1. arg[p].key \in KeyDomain
                BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
              <7>2. CASE ~KeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]])
                BY <7>1, <7>2 DEF StateDomain, ConfigDomain
              <7> SUFFICES ASSUME KeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]])
                           PROVE  ValOfKeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]]) \in ValDomain
                BY <7>1, <7>2 DEF StateDomain, ConfigDomain
              <7>3. PICK idx \in 1..Len(MemLocs[A[Hash[arg[p].key]]]) : MemLocs[A[Hash[arg[p].key]]][idx].key = arg[p].key
                BY Zenon DEF KeyInBktAtAddr
              <7>4. idx = CHOOSE index \in 1..Len(MemLocs[A[Hash[arg[p].key]]]) : MemLocs[A[Hash[arg[p].key]]][index].key = arg[p].key
                BY <7>3
              <7>5. ValOfKeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]]) = MemLocs[A[Hash[arg[p].key]]][idx].val
                BY Zenon, <7>4 DEF ValOfKeyInBktAtAddr
              <7>6. A[Hash[arg[p].key]] # NULL
                BY Zenon DEF KeyInBktAtAddr
              <7>7. MemLocs[A[Hash[arg[p].key]]] \in Seq([key: KeyDomain, val: ValDomain])
                BY Zenon, HashDef, NULLDef, <7>6
              <7>8. MemLocs[A[Hash[arg[p].key]]][idx] \in [key: KeyDomain, val: ValDomain]
                BY Zenon, <7>3, <7>7, ElementOfSeq
              <7>9. MemLocs[A[Hash[arg[p].key]]][idx].val \in ValDomain
                BY <7>8
              <7> QED
                BY <7>5, <7>9
            <6>2. c_pred.op \in [ProcSet -> OpDomain]
              BY DEF ConfigDomain
            <6>3. c_pred.arg \in [ProcSet -> ArgDomain]
              BY DEF ConfigDomain
            <6>4. c_pred.res \in [ProcSet -> ResDomain]
              BY DEF ConfigDomain, ResDomain
            <6> QED
              BY <6>1, <6>2, <6>3, <6>4 DEF ConfigDomain
          <5>2. c_pred \in S
            <6>1. c_pred.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL]
              <7> SUFFICES ASSUME NEW k \in KeyDomain
                           PROVE  c_pred.state[k] = IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL
                BY Zenon, <5>1 DEF StateDomain, ConfigDomain
              <7>1. CASE k = arg[p].key
                <8>1. arg[p].key \in KeyDomain
                  BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
                <8> QED
                  BY <7>1, <8>1, Zenon DEF StateDomain, ConfigDomain
              <7>2. CASE k # arg[p].key /\ Hash[k] # Hash[arg[p].key]
                <8> USE <7>2
                <8>1. c.state = [key \in KeyDomain |-> IF KeyInBktAtAddr(key, A[Hash[key]])' THEN ValOfKeyInBktAtAddr(key, A[Hash[key]])' ELSE NULL]
                  BY SPrimeRewrite, Zenon DEF SPrime
                <8>2. A'[Hash[k]] = A[Hash[k]]
                  BY HashDef, Zenon
                <8>3. KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
                  BY <8>2, Zenon DEF KeyInBktAtAddr
                <8>4. ValOfKeyInBktAtAddr(k, A[Hash[k]]) = ValOfKeyInBktAtAddr(k, A[Hash[k]])'
                  <9> DEFINE bkt_arr == MemLocs'[A'[Hash[k]]]
                  <9> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
                  <9>1. ValOfKeyInBktAtAddr(k, A[Hash[k]])' = bkt_arr[idx].val
                    BY Zenon DEF ValOfKeyInBktAtAddr
                  <9>2. bkt_arr = MemLocs[A[Hash[k]]]
                    BY Zenon, <8>2
                  <9>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
                    BY Zenon
                  <9>4. ValOfKeyInBktAtAddr(k, A[Hash[k]]) = MemLocs[A[Hash[k]]][CHOOSE index \in 1..Len(MemLocs[A[Hash[k]]]) : MemLocs[A[Hash[k]]][index].key = k].val
                    BY Zenon DEF ValOfKeyInBktAtAddr
                  <9>5. ValOfKeyInBktAtAddr(k, A[Hash[k]]) = bkt_arr[idx].val
                    BY ZenonT(90), <9>2, <9>3, <9>4
                  <9> QED
                    BY Zenon, <9>1, <9>5
                <8> QED
                  BY <8>1, <8>3, <8>4
              <7>3. CASE k # arg[p].key /\ Hash[k] = Hash[arg[p].key]
                <8> USE <7>3
                <8>1. c.state = [key \in KeyDomain |-> IF KeyInBktAtAddr(key, A[Hash[key]])' 
                                                          THEN ValOfKeyInBktAtAddr(key, A[Hash[key]])' 
                                                          ELSE NULL]
                  BY SPrimeRewrite, Zenon DEF SPrime
                <8>2. c_pred.state[k] = IF KeyInBktAtAddr(k, A[Hash[k]])' 
                                           THEN ValOfKeyInBktAtAddr(k, A[Hash[k]])' 
                                           ELSE NULL
                  BY <8>1
                <8>3. MemLocs' = MemLocs
                  BY Zenon
                <8>4. bucket[p] = A[Hash[k]]
                  BY Zenon
                <8>5. arg[p].key \in KeyDomain
                  BY RemDef, Zenon DEF ArgsOf, LineIDtoOp
                <8>6. newbkt[p] = A'[Hash[k]]
                  BY Zenon, <8>5, HashDef
                <8>7. KeyInBktAtAddr(k, A[Hash[k]])' = KeyInBktAtAddr(k, newbkt[p])
                  BY <8>6, Zenon DEF KeyInBktAtAddr
                <8>8. ValOfKeyInBktAtAddr(k, A[Hash[k]])' = ValOfKeyInBktAtAddr(k, newbkt[p])
                  BY <8>6, Zenon DEF ValOfKeyInBktAtAddr
                <8>9. c_pred.state[k] = IF KeyInBktAtAddr(k, newbkt[p]) THEN ValOfKeyInBktAtAddr(k, newbkt[p]) ELSE NULL
                  BY <8>2, <8>7, <8>8, Zenon
                <8>10. /\ KeyInBktAtAddr(k, bucket[p]) = KeyInBktAtAddr(k, newbkt[p])
                       /\ KeyInBktAtAddr(k, bucket[p]) => (ValOfKeyInBktAtAddr(k, bucket[p]) = ValOfKeyInBktAtAddr(k, newbkt[p]))
                  BY Zenon DEF NewBktOK
                <8>11. c_pred.state[k] = IF KeyInBktAtAddr(k, bucket[p]) THEN ValOfKeyInBktAtAddr(k, bucket[p]) ELSE NULL
                  BY <8>9, <8>10, Zenon
                <8>12. c_pred.state[k] = IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL
                  BY <8>11, <8>6, Zenon
                <8> QED
                  BY <8>12, Zenon
              <7> QED
                BY <7>1, <7>2, <7>3
            <6>2. ASSUME NEW q \in ProcSet
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
              <7> USE <6>2
              <7>1. CASE pc[q] = RemainderID
                <8> USE <7>1
                <8> SUFFICES c_pred.op[q] = BOT /\ c_pred.arg[q] = BOT /\ c_pred.res[q] = BOT
                  BY RemDef, Zenon
                <8>1. q # p
                  BY RemDef, Zenon
                <8>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                  BY <8>1
                <8>3. pc'[q] = RemainderID
                  BY RemDef, Zenon
                <8>4. c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
                  BY <8>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2, <8>4
              <7>2. CASE pc[q] = "F1"
                <8> USE <7>2
                <8> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
                  BY RemDef, Zenon
                <8>1. q # p
                  BY RemDef, Zenon
                <8>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                  BY <8>1
                <8>3. pc'[q] = "F1"
                  BY RemDef, Zenon
                <8>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY <8>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2, <8>4
              <7>3. CASE pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                <8> USE <7>3
                <8> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                  BY RemDef, Zenon
                <8>1. q # p
                  BY RemDef, Zenon
                <8>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                  BY <8>1
                <8>3. pc'[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY RemDef, Zenon DEF KeyInBktAtAddr
                <8>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY <8>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                  <9> DEFINE bkt_arr == MemLocs'[bucket'[q]]
                  <9> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg'[q].key
                  <9>1. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = bkt_arr[idx].val
                    BY Zenon DEF ValOfKeyInBktAtAddr
                  <9>2. bkt_arr = MemLocs[bucket[q]]
                    BY Zenon
                  <9>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
                    BY Zenon
                  <9> QED
                    BY <9>1, <9>2, <9>3, Isa DEF ValOfKeyInBktAtAddr
                <8> QED
                  BY <8>2, <8>4, <8>5
              <7>4. CASE pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                <8> USE <7>4
                <8> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = NULL
                  BY RemDef, Zenon
                <8>1. q # p
                  BY RemDef, Zenon
                <8>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                  BY <8>1
                <8>3. pc'[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY RemDef, Zenon DEF KeyInBktAtAddr
                <8>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                  BY <8>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2, <8>4
              <7>5. CASE pc[q] = "F3"
                <8> USE <7>5
                <8> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
                  BY RemDef, Zenon
                <8>1. q # p
                  BY RemDef, Zenon
                <8>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                  BY <8>1
                <8>3. pc'[q] = "F3"
                  BY RemDef, Zenon
                <8>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                  BY <8>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2, <8>4 
              <7>6. CASE pc[q] \in {"I1", "I3", "I4"}
                <8> USE <7>6
                <8> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
                  BY RemDef, Zenon
                <8>A. CASE p = q
                  <9> USE <8>A
                  <9>1. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = BOT
                    BY <5>1 DEF ConfigDomain
                  <9>2. pc'[q] = "I5"
                    BY Zenon
                  <9>3. c.op[q] = "Insert" /\ c.arg[p] = arg[q]
                    BY <9>2, SPrimeRewrite, Zenon, RemDef DEF SPrime
                  <9> QED
                    BY <9>1, <9>3
                <8> SUFFICES ASSUME p # q
                             PROVE  c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
                  BY <8>A
                <8>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                  OBVIOUS
                <8>3. pc'[q] \in {"I1", "I3", "I4"}
                  BY RemDef, Zenon
                <8>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY <8>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2, <8>4
              <7>7. CASE pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                <8> USE <7>7
                <8> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                  BY RemDef, Zenon
                <8>1. q # p
                  BY RemDef, Zenon
                <8>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                  BY <8>1
                <8>3. pc'[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY RemDef, Zenon DEF KeyInBktAtAddr
                <8>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY <8>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                  <9> DEFINE bkt_arr == MemLocs'[bucket'[q]]
                  <9> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg'[q].key
                  <9>1. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = bkt_arr[idx].val
                    BY Zenon DEF ValOfKeyInBktAtAddr
                  <9>2. bkt_arr = MemLocs[bucket[q]]
                    BY Zenon
                  <9>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
                    BY Zenon
                  <9> QED
                    BY <9>1, <9>2, <9>3, Isa DEF ValOfKeyInBktAtAddr
                <8> QED
                  BY <8>2, <8>4, <8>5
              <7>8. CASE pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                <8> USE <7>8
                <8> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
                  BY RemDef, Zenon
                <8>1. q # p
                  BY RemDef, Zenon
                <8>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                  BY <8>1
                <8>3. pc'[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY RemDef, Zenon DEF KeyInBktAtAddr
                <8>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY <8>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2, <8>4
              <7>9. CASE pc[q] = "I5"
                <8> USE <7>9
                <8> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
                  BY RemDef, Zenon
                <8>1. q # p
                  BY RemDef, Zenon
                <8>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                  BY <8>1
                <8>3. pc'[q] = "I5"
                  BY RemDef, Zenon
                <8>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                  BY <8>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2, <8>4
              <7>10. CASE pc[q] \in {"U1", "U2", "U3", "U4"}
                <8> USE <7>10
                <8> SUFFICES c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
                  BY RemDef, Zenon
                <8>1. CASE q = p
                  <9> USE <8>1
                  <9>1. pc'[q] = "U5"
                    BY Zenon
                  <9>2. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r'[q]
                    BY <9>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
                  <9>3. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = BOT
                    BY DEF ConfigDomain 
                  <9> QED
                    BY <9>2, <9>3
                <8> SUFFICES ASSUME q # p
                             PROVE  c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
                  BY <8>1
                <8>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                  OBVIOUS
                <8>3. pc'[q] \in {"U1", "U2", "U3", "U4"}
                  BY RemDef, Zenon
                <8>4. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY <8>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2, <8>4
              <7>11. CASE pc[q] = "U5" 
                <8> USE <7>11
                <8> SUFFICES c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
                  BY RemDef, Zenon
                <8>1. q # p
                  BY RemDef, Zenon
                <8>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                  BY <8>1
                <8>3. pc'[q] = "U5"
                  BY RemDef, Zenon
                <8>4. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                  BY <8>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2, <8>4
              <7>12. CASE pc[q] \in {"R1", "R3", "R4"}
                <8> USE <7>12
                <8> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
                  BY RemDef, Zenon
                <8>1. q # p
                  BY RemDef, Zenon
                <8>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                  BY <8>1
                <8>3. pc'[q] \in {"R1", "R3", "R4"}
                  BY RemDef, Zenon
                <8>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY <8>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2, <8>4
              <7>13. CASE pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q]) 
                <8> USE <7>13
                <8> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
                  BY RemDef, Zenon
                <8>1. q # p
                  BY RemDef, Zenon
                <8>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                  BY <8>1
                <8>3. pc'[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY RemDef, Zenon DEF KeyInBktAtAddr
                <8>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY <8>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2, <8>4              
              <7>14. CASE pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                <8> USE <7>14
                <8> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = NULL
                  BY RemDef, Zenon
                <8>1. q # p
                  BY RemDef, Zenon
                <8>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                  BY <8>1
                <8>3. pc'[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY RemDef, Zenon DEF KeyInBktAtAddr
                <8>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                  BY <8>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2, <8>4    
              <7>15. CASE pc[q] = "R5"
                <8> USE <7>15
                <8> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
                  BY RemDef, Zenon
                <8>1. q # p
                  BY RemDef, Zenon
                <8>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                  BY <8>1
                <8>3. pc'[q] = "R5"
                  BY RemDef, Zenon
                <8>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                  BY <8>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2, <8>4
              <7> QED
                  BY RemDef, ZenonT(120),
                     <7>1, <7>2, <7>3, <7>4, <7>5, <7>6, <7>7, <7>8, <7>9, 
                     <7>10, <7>11, <7>12, <7>13, <7>14, <7>15
                  DEF LineIDs 
            <6> QED
              BY <5>1, <6>1, <6>2, Zenon DEF S
          <5>3. c_pred \in P
            BY <5>2 DEF InvL1
          <5>4. Delta(c_pred, p, c)
            <6>1. c_pred.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL]
              BY <5>1, <5>2, Zenon DEF S
            <6>2. c_pred.op[p] = "Upsert" /\ c_pred.arg[p] = arg[p] /\ c_pred.res[p] = BOT
              BY <5>1, <5>2, Zenon, RemDef DEF S
            <6>3. arg[p] \in ArgsOf("Upsert") /\ arg[p].key \in KeyDomain
              BY RemDef, Zenon DEF ArgsOf, LineIDtoOp 
            <6> SUFFICES /\ c.state = [c_pred.state EXCEPT ![arg[p].key] = arg[p].val]
                         /\ c.res = [c_pred.res EXCEPT ![p] = c_pred.state[arg[p].key]]
              BY <6>2, <6>3, Zenon DEF Delta
            <6> SUFFICES /\ c.state[arg[p].key] = arg[p].val
                         /\ c.res[p] = IF KeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]]) 
                                          THEN ValOfKeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]]) 
                                          ELSE NULL
              BY <5>2, <6>3, ZenonT(60) DEF ConfigDomain, StateDomain
            <6>4. c.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]])' THEN ValOfKeyInBktAtAddr(k, A[Hash[k]])' ELSE NULL]
              BY SPrimeRewrite, Zenon DEF SPrime
            <6>5. c.state[arg[p].key] = IF KeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]])' THEN ValOfKeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]])' ELSE NULL
              BY <6>4, <6>3, Zenon
            <6>6. newbkt[p] = A'[Hash[arg[p].key]]
              BY Zenon, HashDef, <6>3
            <6>7. MemLocs[A'[Hash[arg[p].key]]] = MemLocs[newbkt[p]]
              BY Zenon, <6>6
            <6>8. KeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]])' = KeyInBktAtAddr(arg[p].key, newbkt[p])
              BY Zenon, <6>6 DEF KeyInBktAtAddr
            <6>9. ValOfKeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]])' = 
              MemLocs[A'[Hash[arg[p].key]]][CHOOSE index \in 1..Len(MemLocs[A'[Hash[arg[p].key]]]) : MemLocs[A'[Hash[arg[p].key]]][index].key = arg[p].key].val
              BY Zenon DEF ValOfKeyInBktAtAddr
            <6>10. ValOfKeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]])' = 
              MemLocs[newbkt[p]][CHOOSE index \in 1..Len(MemLocs[newbkt[p]]) : MemLocs[newbkt[p]][index].key = arg[p].key].val
              BY <6>9, <6>7
            <6>11. ValOfKeyInBktAtAddr(arg[p].key, newbkt[p]) = 
              MemLocs[newbkt[p]][CHOOSE index \in 1..Len(MemLocs[newbkt[p]]) : MemLocs[newbkt[p]][index].key = arg[p].key].val
              BY Zenon DEF ValOfKeyInBktAtAddr
            <6>12. ValOfKeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]])' = ValOfKeyInBktAtAddr(arg[p].key, newbkt[p])
              BY <6>10, <6>11, Zenon
            <6>13. c.state[arg[p].key] = IF KeyInBktAtAddr(arg[p].key, newbkt[p]) THEN ValOfKeyInBktAtAddr(arg[p].key, newbkt[p]) ELSE NULL
              BY <6>5, <6>8, <6>12, Zenon
            <6>14. c.state[arg[p].key] = arg[p].val
              BY <6>13, Zenon DEF NewBktOK  
            <6>15. pc'[p] = "U5"
              BY Zenon
            <6>16. c.res[p] = r'[p]
              BY <6>15, SPrimeRewrite, RemDef, Zenon DEF SPrime
            <6>17. c.res[p] = IF KeyInBktAtAddr(arg[p].key, bucket[p]) THEN ValOfKeyInBktAtAddr(arg[p].key, bucket[p]) ELSE NULL
              BY <6>16, Zenon DEF BktOK
            <6>18. c.res[p] = IF KeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]]) THEN ValOfKeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]]) ELSE NULL
              BY <6>17, Zenon
            <6> QED
              BY <6>18, <6>14
          <5>5. c \in Evolve(P)
            BY <5>1, <5>3, <5>4, SingleDeltaEvolve
          <5> QED
            BY <5>5
        <4>2. CASE A[Hash[arg[p].key]] # bucket[p]
          <5> USE <4>2
          <5>0. ASSUME c \in S
                PROVE  c \in P'
            <6> USE <5>0
            <6>1. c \in P
              BY DEF InvL1
            <6>2. c \in Evolve(P)
              BY <6>1, EmptySeqEvolve
            <6> QED
              BY <6>2
          <5> SUFFICES c \in S
            BY <5>0
          <5>1. c.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL]
            <6>1. c.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]])' THEN ValOfKeyInBktAtAddr(k, A[Hash[k]])' ELSE NULL]
              BY Zenon, SPrimeRewrite DEF SPrime
            <6>2. \A k \in KeyDomain : KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
              BY Zenon DEF KeyInBktAtAddr
            <6>3. \A k \in KeyDomain : ValOfKeyInBktAtAddr(k, A[Hash[k]])' = ValOfKeyInBktAtAddr(k, A[Hash[k]])
              <7> SUFFICES ASSUME NEW k \in KeyDomain
                           PROVE  ValOfKeyInBktAtAddr(k, A[Hash[k]])' = ValOfKeyInBktAtAddr(k, A[Hash[k]])
                OBVIOUS
              <7> bkt_arr == MemLocs'[A'[Hash[k]]]
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
              <7>1. ValOfKeyInBktAtAddr(k, A[Hash[k]])' = bkt_arr[idx].val
                BY DEF ValOfKeyInBktAtAddr
              <7>2. bkt_arr = MemLocs[A[Hash[k]]]
                BY Zenon
              <7> QED
                BY <7>1, <7>2, ZenonT(30) DEF ValOfKeyInBktAtAddr
            <6> QED
              BY <6>1, <6>2, <6>3
          <5>2. ASSUME NEW q \in ProcSet
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
            <6> USE <5>2
            <6>A. \A k \in KeyDomain : KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, bucket[q])'
              BY Zenon DEF KeyInBktAtAddr
            <6>B. \A k \in KeyDomain : ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, bucket[q])
              <7> SUFFICES ASSUME NEW k \in KeyDomain
                           PROVE  ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, bucket[q])
                OBVIOUS
              <7> bkt_arr == MemLocs'[bucket'[q]]
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
              <7>1. ValOfKeyInBktAtAddr(k, bucket[q])' = bkt_arr[idx].val
                BY DEF ValOfKeyInBktAtAddr
              <7>2. bkt_arr = MemLocs[bucket[q]]
                BY Zenon
              <7> QED
                BY <7>1, <7>2, ZenonT(30) DEF ValOfKeyInBktAtAddr
            <6>1. CASE pc[q] = RemainderID
              <7> USE <6>1
              <7> SUFFICES c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
                BY RemDef, Zenon
              <7>1. pc'[q] = RemainderID
                BY RemDef, Zenon
              <7>2. c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2
            <6>2. CASE pc[q] = "F1"
              <7> USE <6>2
              <7> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY RemDef, Zenon
              <7>1. pc'[q] = "F1"
                BY RemDef, Zenon
              <7>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2
            <6>3. CASE pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
              <7> USE <6>3
              <7> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                BY RemDef, Zenon
              <7>1. pc'[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                BY RemDef, Zenon DEF KeyInBktAtAddr
              <7>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
                BY <7>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7>3. arg[q].key = arg'[q].key /\ arg[q].key \in KeyDomain
                BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
              <7>4. c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                BY <7>2, <7>3, <6>B
              <7> QED
                BY <7>2, <7>4
            <6>4. CASE pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
              <7> USE <6>4
              <7> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                BY RemDef, Zenon
              <7>2. pc'[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                BY RemDef, Zenon DEF KeyInBktAtAddr
              <7>3. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                BY <7>2,  SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>3
            <6>5. CASE pc[q] = "F3"
              <7> USE <6>5
              <7> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY RemDef, Zenon
              <7>1. pc'[q] = "F3"
                BY RemDef, Zenon
              <7>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2 
            <6>6. CASE pc[q] \in {"I1", "I3", "I4"}
              <7> USE <6>6
              <7> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY RemDef, Zenon
              <7>1. pc'[q] \in {"I1", "I3", "I4"}
                BY RemDef, Zenon
              <7>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2 
            <6>7. CASE pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
              <7> USE <6>7
              <7> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                BY RemDef, Zenon
              <7>1. CASE p = q
                <8> USE <7>1
                <8>1. c.op[p] = "Insert" /\ c.arg[p] = arg[p] /\ c.res[p] = r'[p]
                  BY SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8>2. r'[p] = ValOfKeyInBktAtAddr(arg[p].key, bucket[p])
                  BY Zenon
                <8> QED
                  BY <8>1, <8>2
              <7> SUFFICES ASSUME p # q
                           PROVE  c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                BY <7>1
              <7>2. pc'[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                BY RemDef, Zenon DEF KeyInBktAtAddr
              <7>3. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
                BY <7>2,  SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7>4. arg[q].key = arg'[q].key /\ arg[q].key \in KeyDomain
                BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
              <7>5. c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                BY <7>3, <7>4, <6>B
              <7> QED
                BY <7>3, <7>5
            <6>8. CASE pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
              <7> USE <6>8
              <7> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY RemDef, Zenon
              <7>1. CASE p = q
                <8> USE <7>1
                <8>1. c.op[p] = "Insert" /\ c.arg[p] = arg[p] /\ c.res[p] = BOT
                  BY SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>1
              <7> SUFFICES ASSUME p # q
                           PROVE  c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <7>1
              <7>2. pc'[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                BY RemDef, Zenon DEF KeyInBktAtAddr
              <7>3. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <7>2, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>3 
            <6>9. CASE pc[q] = "I5"
              <7> USE <6>9
              <7> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY RemDef, Zenon
              <7>1. pc'[q] = "I5"
                BY RemDef, Zenon 
              <7>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2 
            <6>10. CASE pc[q] \in {"U1", "U2", "U3", "U4"}
              <7> USE <6>10
              <7> SUFFICES c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY RemDef, Zenon
              <7>1. pc'[q] \in {"U1", "U2", "U3", "U4"}
                BY RemDef, Zenon
              <7>2. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2
            <6>11. CASE pc[q] = "U5" 
              <7> USE <6>11
              <7> SUFFICES c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY RemDef, Zenon
              <7>1. pc'[q] = "U5"
                BY RemDef, Zenon
              <7>2. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2
            <6>12. CASE pc[q] \in {"R1", "R3", "R4"}
              <7> USE <6>12
              <7> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY RemDef, Zenon
              <7>1. pc'[q] \in {"R1", "R3", "R4"}
                BY RemDef, Zenon
              <7>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2
            <6>13. CASE pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
              <7> USE <6>13
              <7> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY RemDef, Zenon
              <7>1. pc'[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                BY RemDef, Zenon DEF KeyInBktAtAddr
              <7>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2
            <6>14. CASE pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
              <7> USE <6>14
              <7> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                BY RemDef, Zenon
              <7>1. pc'[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                BY RemDef, Zenon DEF KeyInBktAtAddr
              <7>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2
            <6>15. CASE pc[q] = "R5"
              <7> USE <6>15
              <7> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY RemDef, Zenon
              <7>1. pc'[q] = "R5" 
                BY RemDef, Zenon
              <7>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2
            <6> QED
                BY RemDef, ZenonT(120),
                    <6>1, <6>2, <6>3, <6>4, <6>5, <6>6, <6>7, <6>8, <6>9, 
                    <6>10, <6>11, <6>12, <6>13, <6>14, <6>15
                DEF LineIDs
          <5> QED
            BY <5>1, <5>2, Zenon DEF S
        <4> QED
          BY <4>1, <4>2
      <3>11. CASE Line = R1(p)
        <4> USE <3>11 DEF R1
        <4> SUFFICES ASSUME NEW c \in ConfigDomain,
                            c \in S'
                     PROVE  c \in P'
          BY Zenon DEF InvL1, S
        <4>1. CASE ~KeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]])
          <5> USE <4>1
          <5> c_pred == [state |-> c.state,
                         op    |-> c.op,
                         arg   |-> c.arg,
                         res   |-> [c.res EXCEPT ![p] = BOT]]
          <5>1. c_pred \in ConfigDomain
            <6>1. c_pred.state \in StateDomain
              BY DEF ConfigDomain
            <6>2. c_pred.op \in [ProcSet -> OpDomain]
              BY DEF ConfigDomain
            <6>3. c_pred.arg \in [ProcSet -> ArgDomain]
              BY DEF ConfigDomain
            <6>4. c_pred.res \in [ProcSet -> ResDomain]
              BY DEF ConfigDomain, ResDomain
            <6> QED
              BY <6>1, <6>2, <6>3, <6>4 DEF ConfigDomain
          <5>2. c_pred \in S
            <6>1. c_pred.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL]
              <7>1. c_pred.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]])'
                                                           THEN ValOfKeyInBktAtAddr(k, A[Hash[k]])'
                                                           ELSE NULL]
                BY SPrimeRewrite, Zenon DEF SPrime
              <7>2. \A k \in KeyDomain : /\ KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
                                         /\ ValOfKeyInBktAtAddr(k, A[Hash[k]]) = ValOfKeyInBktAtAddr(k, A[Hash[k]])'
                <8> SUFFICES ASSUME NEW k \in KeyDomain
                             PROVE  /\ KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
                                    /\ ValOfKeyInBktAtAddr(k, A[Hash[k]]) = ValOfKeyInBktAtAddr(k, A[Hash[k]])'
                  OBVIOUS
                <8>1. KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
                  BY Zenon DEF KeyInBktAtAddr
                <8>2. ValOfKeyInBktAtAddr(k, A[Hash[k]]) = ValOfKeyInBktAtAddr(k, A[Hash[k]])'
                  <9> DEFINE bkt_arr == MemLocs'[A'[Hash[k]]]
                  <9> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
                  <9>1. ValOfKeyInBktAtAddr(k, A[Hash[k]])' = bkt_arr[idx].val
                    BY Zenon DEF ValOfKeyInBktAtAddr
                  <9>2. bkt_arr = MemLocs[A[Hash[k]]]
                    BY Zenon
                  <9>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
                    BY Zenon
                  <9> QED
                    BY <9>1, <9>2, <9>3, Isa DEF ValOfKeyInBktAtAddr
                <8>3. QED
                  BY <8>1, <8>2
              <7> QED
                BY <7>1, <7>2 
            <6>2. ASSUME NEW q \in ProcSet
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
              <7> USE <6>2
              <7>1. CASE pc[q] = RemainderID
                <8> USE <7>1
                <8> SUFFICES c_pred.op[q] = BOT /\ c_pred.arg[q] = BOT /\ c_pred.res[q] = BOT
                  BY RemDef, Zenon
                <8>1. q # p
                  BY RemDef, Zenon
                <8>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                  BY <8>1
                <8>3. pc'[q] = RemainderID
                  BY RemDef, Zenon
                <8>4. c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
                  BY <8>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2, <8>4
              <7>2. CASE pc[q] = "F1"
                <8> USE <7>2
                <8> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
                  BY RemDef, Zenon
                <8>1. q # p
                  BY RemDef, Zenon
                <8>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                  BY <8>1
                <8>3. pc'[q] = "F1"
                  BY RemDef, Zenon
                <8>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY <8>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2, <8>4
              <7>3. CASE pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                <8> USE <7>3
                <8> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                  BY RemDef, Zenon
                <8>1. q # p
                  BY RemDef, Zenon
                <8>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                  BY <8>1
                <8>3. pc'[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY RemDef, Zenon DEF KeyInBktAtAddr
                <8>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY <8>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                  <9> DEFINE bkt_arr == MemLocs'[bucket'[q]]
                  <9> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg'[q].key
                  <9>1. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = bkt_arr[idx].val
                    BY Zenon DEF ValOfKeyInBktAtAddr
                  <9>2. bkt_arr = MemLocs[bucket[q]]
                    BY Zenon
                  <9>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
                    BY Zenon
                  <9> QED
                    BY <9>1, <9>2, <9>3, Isa DEF ValOfKeyInBktAtAddr
                <8> QED
                  BY <8>2, <8>4, <8>5
              <7>4. CASE pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                <8> USE <7>4
                <8> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = NULL
                  BY RemDef, Zenon
                <8>1. q # p
                  BY RemDef, Zenon
                <8>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                  BY <8>1
                <8>3. pc'[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY RemDef, Zenon DEF KeyInBktAtAddr
                <8>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                  BY <8>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2, <8>4
              <7>5. CASE pc[q] = "F3" 
                <8> USE <7>5
                <8> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
                  BY RemDef, Zenon
                <8>1. q # p
                  BY RemDef, Zenon
                <8>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                  BY <8>1
                <8>3. pc'[q] = "F3"
                  BY RemDef, Zenon
                <8>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                  BY <8>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2, <8>4
              <7>6. CASE pc[q] \in {"I1", "I3", "I4"}
                <8> USE <7>6
                <8> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
                  BY RemDef, Zenon
                <8>1. q # p
                  BY RemDef, Zenon
                <8>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                  BY <8>1
                <8>3. pc'[q] \in {"I1", "I3", "I4"}
                  BY RemDef, Zenon
                <8>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY <8>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2, <8>4
              <7>7. CASE pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                <8> USE <7>7
                <8> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                  BY RemDef, Zenon
                <8>1. q # p
                  BY RemDef, Zenon
                <8>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                  BY <8>1
                <8>3. pc'[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY RemDef, Zenon DEF KeyInBktAtAddr
                <8>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY <8>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                  <9> DEFINE bkt_arr == MemLocs'[bucket'[q]]
                  <9> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg'[q].key
                  <9>1. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = bkt_arr[idx].val
                    BY Zenon DEF ValOfKeyInBktAtAddr
                  <9>2. bkt_arr = MemLocs[bucket[q]]
                    BY Zenon
                  <9>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
                    BY Zenon
                  <9> QED
                    BY <9>1, <9>2, <9>3, Isa DEF ValOfKeyInBktAtAddr
                <8> QED
                  BY <8>2, <8>4, <8>5
              <7>8. CASE pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                <8> USE <7>8
                <8> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
                  BY RemDef, Zenon
                <8>1. q # p
                  BY RemDef, Zenon
                <8>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                  BY <8>1
                <8>3. pc'[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY RemDef, Zenon DEF KeyInBktAtAddr
                <8>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY <8>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2, <8>4
              <7>9. CASE pc[q] = "I5"
                <8> USE <7>9
                <8> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
                  BY RemDef, Zenon
                <8>1. q # p
                  BY RemDef, Zenon
                <8>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                  BY <8>1
                <8>3. pc'[q] = "I5"
                  BY RemDef, Zenon
                <8>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                  BY <8>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2, <8>4
              <7>10. CASE pc[q] \in {"U1", "U2", "U3", "U4"}
                <8> USE <7>10
                <8> SUFFICES c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
                  BY RemDef, Zenon
                <8>1. q # p
                  BY RemDef, Zenon
                <8>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                  BY <8>1
                <8>3. pc'[q] \in {"U1", "U2", "U3", "U4"}
                  BY RemDef, Zenon
                <8>4. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY <8>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2, <8>4
              <7>11. CASE pc[q] = "U5" 
                <8> USE <7>11
                <8> SUFFICES c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
                  BY RemDef, Zenon
                <8>1. q # p
                  BY RemDef, Zenon
                <8>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                  BY <8>1
                <8>3. pc'[q] = "U5"
                  BY RemDef, Zenon
                <8>4. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                  BY <8>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2, <8>4
              <7>12. CASE pc[q] \in {"R1", "R3", "R4"}
                <8> USE <7>12
                <8> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
                  BY RemDef, Zenon
                <8>1. CASE q = p
                  <9> USE <8>1
                  <9>1. pc'[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                    BY RemDef, Zenon DEF KeyInBktAtAddr
                  <9>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                    BY <9>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
                  <9>3. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = BOT
                    BY Zenon DEF ConfigDomain  
                  <9> QED
                    BY <9>2, <9>3
                <8> SUFFICES ASSUME q # p
                             PROVE  c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
                  BY <8>1
                <8>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                  OBVIOUS
                <8>3. pc'[q] \in {"R1", "R3", "R4"}
                  BY RemDef, Zenon
                <8>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY <8>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2, <8>4
              <7>13. CASE pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q]) 
                <8> USE <7>13
                <8> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
                  BY RemDef, Zenon
                <8>1. q # p
                  BY RemDef, Zenon
                <8>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                  BY <8>1
                <8>3. pc'[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY RemDef, Zenon DEF KeyInBktAtAddr
                <8>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY <8>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2, <8>4              
              <7>14. CASE pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                <8> USE <7>14
                <8> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = NULL
                  BY RemDef, Zenon
                <8>1. q # p
                  BY RemDef, Zenon
                <8>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                  BY <8>1
                <8>3. pc'[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY RemDef, Zenon DEF KeyInBktAtAddr
                <8>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                  BY <8>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2, <8>4    
              <7>15. CASE pc[q] = "R5"
                <8> USE <7>15
                <8> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
                  BY RemDef, Zenon
                <8>1. q # p
                  BY RemDef, Zenon
                <8>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                  BY <8>1
                <8>3. pc'[q] = "R5"
                  BY RemDef, Zenon
                <8>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                  BY <8>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2, <8>4
              <7> QED
                  BY RemDef, ZenonT(120),
                     <7>1, <7>2, <7>3, <7>4, <7>5, <7>6, <7>7, <7>8, <7>9, 
                     <7>10, <7>11, <7>12, <7>13, <7>14, <7>15
                  DEF LineIDs
            <6> QED
              BY <5>1, <6>1, <6>2, Zenon DEF S
          <5>3. c_pred \in P
            BY <5>2 DEF InvL1
          <5>4. Delta(c_pred, p, c)
            <6>1. c_pred.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL]
              BY <5>1, <5>2, Zenon DEF S
            <6>2. c_pred.op[p] = "Remove" /\ c_pred.arg[p] = arg[p] /\ c_pred.res[p] = BOT
              BY <5>1, <5>2, Zenon, RemDef DEF S
            <6>3. arg[p] \in ArgsOf("Remove") /\ arg[p].key \in KeyDomain
              BY RemDef, Zenon DEF ArgsOf, LineIDtoOp 
            <6> SUFFICES /\ c.state = [c_pred.state EXCEPT ![arg[p].key] = NULL]
                         /\ c.res = [c_pred.res EXCEPT ![p] = c_pred.state[arg[p].key]]
              BY <6>2, <6>3, Zenon DEF Delta
            <6> SUFFICES /\ c.state[arg[p].key] = NULL
                         /\ c.res[p] = IF KeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]]) 
                                          THEN ValOfKeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]]) 
                                          ELSE NULL
              BY <5>2, <6>3, ZenonT(60) DEF ConfigDomain, StateDomain
            <6>4. c.state[arg[p].key] = NULL
              BY <6>1, <6>2, <6>3, Zenon
            <6> SUFFICES c.res[p] = NULL
              BY <6>4, Zenon  
            <6>5. pc'[p] = "R2" /\ ~KeyInBktAtAddr(arg[p].key, bucket[p])'
              BY Zenon DEF KeyInBktAtAddr
            <6>6. c.res[p] = NULL
              BY <6>5, SPrimeRewrite, RemDef, Zenon DEF SPrime
            <6> QED  
              BY <6>6
          <5>5. c \in Evolve(P)
            BY <5>1, <5>3, <5>4, SingleDeltaEvolve
          <5> QED
            BY <5>5
        <4>2. CASE KeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]])
          <5> USE <4>2
          <5>1. c \in S
            <6>A. \A k \in KeyDomain : KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
              BY Zenon, HashDef DEF KeyInBktAtAddr
            <6>B. \A k \in KeyDomain : ValOfKeyInBktAtAddr(k, A[Hash[k]]) = ValOfKeyInBktAtAddr(k, A[Hash[k]])'
              <7> SUFFICES ASSUME NEW k \in KeyDomain
                           PROVE  ValOfKeyInBktAtAddr(k, A[Hash[k]]) = ValOfKeyInBktAtAddr(k, A[Hash[k]])'
                OBVIOUS
              <7> DEFINE bkt_arr == MemLocs'[A'[Hash[k]]]
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
              <7>1. ValOfKeyInBktAtAddr(k, A[Hash[k]])' = bkt_arr[idx].val
                BY Zenon DEF ValOfKeyInBktAtAddr
              <7>2. bkt_arr = MemLocs[A[Hash[k]]] /\ A'[Hash[k]] = A[Hash[k]]
                BY Zenon
              <7> QED
                BY <7>1, <7>2 DEF ValOfKeyInBktAtAddr
            <6>1. c.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) 
                                                    THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) 
                                                    ELSE NULL]
              <7>1. c.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]])' THEN ValOfKeyInBktAtAddr(k, A[Hash[k]])' ELSE NULL]
                BY SPrimeRewrite, Zenon DEF SPrime
              <7> QED
                BY <6>A, <6>B, <7>1
            <6>2. ASSUME NEW q \in ProcSet
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
              <7> USE <6>2
              <7>1. CASE pc[q] = RemainderID
                <8> USE <7>1
                <8> SUFFICES c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
                  BY RemDef, Zenon
                <8>1. pc'[q] = RemainderID
                  BY RemDef, Zenon
                <8>2. c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
                  BY <8>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2
              <7>2. CASE pc[q] = "F1"
                <8> USE <7>2
                <8> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY RemDef, Zenon
                <8>1. pc'[q] = "F1"
                  BY RemDef, Zenon
                <8>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY <8>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2    
              <7>3. CASE pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                <8> USE <7>3
                <8> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                  BY RemDef, Zenon
                <8>1. pc'[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY RemDef, Zenon DEF KeyInBktAtAddr
                <8>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY <8>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8>3. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                  <9> DEFINE bkt_arr == MemLocs'[bucket'[q]]
                  <9> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg'[q].key
                  <9>1. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = bkt_arr[idx].val
                    BY Zenon DEF ValOfKeyInBktAtAddr
                  <9>2. bkt_arr = MemLocs[bucket[q]]
                    BY Zenon
                  <9>3. arg'[q].key = arg[q].key
                    BY Zenon
                  <9> QED
                    BY <9>1, <9>2, <9>3, Isa DEF ValOfKeyInBktAtAddr
                <8> QED
                  BY <8>2, <8>3
              <7>4. CASE pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                <8> USE <7>4
                <8> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                  BY RemDef, Zenon
                <8>1. pc'[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY RemDef, Zenon DEF KeyInBktAtAddr
                <8>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                  BY <8>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2
              <7>5. CASE pc[q] = "F3"
                <8> USE <7>5
                <8> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                  BY RemDef, Zenon
                <8>1. pc'[q] = "F3"
                  BY RemDef, Zenon
                <8>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                  BY <8>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2 
              <7>6. CASE pc[q] \in {"I1", "I3", "I4"}
                <8> USE <7>6
                <8> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY RemDef, Zenon
                <8>2. pc'[q] \in {"I1", "I3", "I4"}
                  BY RemDef, Zenon
                <8>3. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY <8>2, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>3 
              <7>7. CASE pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                <8> USE <7>7
                <8> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                  BY RemDef, Zenon
                <8>1. pc'[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY RemDef, Zenon DEF KeyInBktAtAddr
                <8>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY <8>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8>3. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                  <9> DEFINE bkt_arr == MemLocs'[bucket'[q]]
                  <9> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg'[q].key
                  <9>1. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = bkt_arr[idx].val
                    BY Zenon DEF ValOfKeyInBktAtAddr
                  <9>2. bkt_arr = MemLocs[bucket[q]]
                    BY Zenon
                  <9>3. arg'[q].key = arg[q].key
                    BY Zenon
                  <9> QED
                    BY <9>1, <9>2, <9>3, Isa DEF ValOfKeyInBktAtAddr
                <8> QED
                  BY <8>2, <8>3
              <7>8. CASE pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                <8> USE <7>8
                <8> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY RemDef, Zenon
                <8>1. pc'[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY RemDef, Zenon DEF KeyInBktAtAddr
                <8>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY <8>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2
              <7>9. CASE pc[q] = "I5"
                <8> USE <7>9
                <8> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                  BY RemDef, Zenon
                <8>1. pc'[q] = "I5"
                  BY RemDef, Zenon
                <8>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                  BY <8>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2 
              <7>10. CASE pc[q] \in {"U1", "U2", "U3", "U4"}
                <8> USE <7>10
                <8> SUFFICES c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY RemDef, Zenon
                <8>1. pc'[q] \in {"U1", "U2", "U3", "U4"}
                  BY RemDef, Zenon
                <8>2. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY <8>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2 
              <7>11. CASE pc[q] = "U5" 
                <8> USE <7>11
                <8> SUFFICES c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                  BY RemDef, Zenon
                <8>1. pc'[q] = "U5"
                  BY RemDef, Zenon
                <8>2. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                  BY <8>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2 
              <7>12. CASE pc[q] \in {"R1", "R3", "R4"}
                <8> USE <7>12
                <8> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY RemDef, Zenon
                <8>1. CASE p = q
                  <9> USE <8>1
                  <9>1. arg[q].key = arg'[q].key /\ bucket'[q] = A[Hash[arg[q].key]]
                    BY Zenon
                  <9>2. pc'[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                    BY <9>1, Zenon DEF KeyInBktAtAddr
                  <9>3. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                    BY <9>2, SPrimeRewrite, Zenon, RemDef DEF SPrime
                  <9> QED
                    BY <9>3
                <8> SUFFICES ASSUME p # q
                             PROVE  c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY <8>1
                <8>2. pc'[q] \in {"R1", "R3", "R4"}
                  BY RemDef, Zenon
                <8>3. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY <8>2, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>3 
              <7>13. CASE pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                <8> USE <7>13
                <8> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY RemDef, Zenon
                <8>1. pc'[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY RemDef, Zenon DEF KeyInBktAtAddr
                <8>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY <8>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2
              <7>14. CASE pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                <8> USE <7>14
                <8> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                  BY RemDef, Zenon
                <8>1. pc'[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY RemDef, Zenon DEF KeyInBktAtAddr
                <8>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                  BY <8>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2
              <7>15. CASE pc[q] = "R5"
                <8> USE <7>15
                <8> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                  BY RemDef, Zenon
                <8>1. pc'[q] = "R5"
                  BY RemDef, Zenon
                <8>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                  BY <8>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2 
              <7> QED
                BY RemDef, ZenonT(120),
                   <7>1, <7>2, <7>3, <7>4, <7>5, <7>6, <7>7, <7>8, <7>9, 
                   <7>10, <7>11, <7>12, <7>13, <7>14, <7>15
                DEF LineIDs
            <6> QED
              BY <6>1, <6>2, Zenon DEF S
          <5>2. c \in P
            BY <5>1 DEF InvL1
          <5>3. c \in Evolve(P)
            BY <5>2, EmptySeqEvolve
          <5> QED
            BY <5>3
        <4> QED
          BY <4>1, <4>2
      <3>12. CASE Line = R2(p)
        <4> USE <3>12 DEF R2
        <4> SUFFICES ASSUME NEW c \in ConfigDomain,
                            c \in S'
                     PROVE  c \in P'
          BY Zenon DEF InvL1, S
        <4>1. c \in S
          <5>1. c.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL]
            <6>1. c.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]])' THEN ValOfKeyInBktAtAddr(k, A[Hash[k]])' ELSE NULL]
              BY Zenon, SPrimeRewrite DEF SPrime
            <6>2. \A k \in KeyDomain : KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
              BY Zenon DEF KeyInBktAtAddr
            <6>3. \A k \in KeyDomain : ValOfKeyInBktAtAddr(k, A[Hash[k]])' = ValOfKeyInBktAtAddr(k, A[Hash[k]])
              <7> SUFFICES ASSUME NEW k \in KeyDomain
                           PROVE  ValOfKeyInBktAtAddr(k, A[Hash[k]])' = ValOfKeyInBktAtAddr(k, A[Hash[k]])
                OBVIOUS
              <7> bkt_arr == MemLocs'[A'[Hash[k]]]
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
              <7>1. ValOfKeyInBktAtAddr(k, A[Hash[k]])' = bkt_arr[idx].val
                BY DEF ValOfKeyInBktAtAddr
              <7>2. bkt_arr = MemLocs[A[Hash[k]]]
                BY Zenon
              <7> QED
                BY <7>1, <7>2, ZenonT(30) DEF ValOfKeyInBktAtAddr
            <6> QED
              BY <6>1, <6>2, <6>3
          <5>2. ASSUME NEW q \in ProcSet
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
            <6> USE <5>2
            <6>A. \A k \in KeyDomain : KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, bucket[q])'
              BY Zenon DEF KeyInBktAtAddr
            <6>B. \A k \in KeyDomain : ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, bucket[q])
              <7> SUFFICES ASSUME NEW k \in KeyDomain
                           PROVE  ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, bucket[q])
                OBVIOUS
              <7> bkt_arr == MemLocs'[bucket'[q]]
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
              <7>1. ValOfKeyInBktAtAddr(k, bucket[q])' = bkt_arr[idx].val
                BY DEF ValOfKeyInBktAtAddr
              <7>2. bkt_arr = MemLocs[bucket[q]]
                BY Zenon
              <7> QED
                BY <7>1, <7>2, ZenonT(30) DEF ValOfKeyInBktAtAddr
            <6>1. CASE pc[q] = RemainderID
              <7> USE <6>1
              <7> SUFFICES c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
                BY RemDef, Zenon
              <7>1. pc'[q] = RemainderID
                BY RemDef, Zenon
              <7>2. c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2
            <6>2. CASE pc[q] = "F1"
              <7> USE <6>2
              <7> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY RemDef, Zenon
              <7>1. pc'[q] = "F1"
                BY RemDef, Zenon
              <7>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2
            <6>3. CASE pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
              <7> USE <6>3
              <7> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                BY RemDef, Zenon
              <7>1. CASE q = p
                <8> USE <7>1
                <8>1. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r'[q]
                  BY SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                  BY <8>1, Zenon
                <8> QED
                  BY <8>2
              <7> SUFFICES ASSUME q # p
                           PROVE  c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                BY <7>1
              <7>2. pc'[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                BY RemDef, Zenon DEF KeyInBktAtAddr
              <7>3. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
                BY <7>2,  SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7>4. arg[q].key = arg'[q].key /\ arg[q].key \in KeyDomain
                BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
              <7>5. c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                BY <7>3, <7>4, <6>B
              <7> QED
                BY <7>3, <7>5
            <6>4. CASE pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
              <7> USE <6>4
              <7> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                BY RemDef, Zenon
              <7>1. CASE q = p
                <8> USE <7>1
                <8>1. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r'[q]
                  BY SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                  BY <8>1, Zenon
                <8> QED
                  BY <8>2
              <7> SUFFICES ASSUME q # p
                           PROVE  c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                BY <7>1
              <7>2. pc'[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                BY RemDef, Zenon DEF KeyInBktAtAddr
              <7>3. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                BY <7>2,  SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>3
            <6>5. CASE pc[q] = "F3"
              <7> USE <6>5
              <7> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY RemDef, Zenon
              <7>1. pc'[q] = "F3"
                BY RemDef, Zenon
              <7>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2 
            <6>6. CASE pc[q] \in {"I1", "I3", "I4"}
              <7> USE <6>6
              <7> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY RemDef, Zenon
              <7>1. pc'[q] \in {"I1", "I3", "I4"}
                BY RemDef, Zenon
              <7>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2 
            <6>7. CASE pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
              <7> USE <6>7
              <7> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                BY RemDef, Zenon
              <7>2. pc'[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                BY RemDef, Zenon DEF KeyInBktAtAddr
              <7>3. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
                BY <7>2,  SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7>4. arg[q].key = arg'[q].key /\ arg[q].key \in KeyDomain
                BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
              <7>5. c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                BY <7>3, <7>4, <6>B
              <7> QED
                BY <7>3, <7>5
            <6>8. CASE pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
              <7> USE <6>8
              <7> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY RemDef, Zenon
              <7>1. pc'[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                BY RemDef, Zenon DEF KeyInBktAtAddr
              <7>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2 
            <6>9. CASE pc[q] = "I5"
              <7> USE <6>9
              <7> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY RemDef, Zenon
              <7>1. pc'[q] = "I5"
                BY RemDef, Zenon 
              <7>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2 
            <6>10. CASE pc[q] \in {"U1", "U2", "U3", "U4"}
              <7> USE <6>10
              <7> SUFFICES c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY RemDef, Zenon
              <7>1. pc'[q] \in {"U1", "U2", "U3", "U4"}
                BY RemDef, Zenon
              <7>2. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2
            <6>11. CASE pc[q] = "U5" 
              <7> USE <6>11
              <7> SUFFICES c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY RemDef, Zenon
              <7>1. pc'[q] = "U5"
                BY RemDef, Zenon
              <7>2. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2
            <6>12. CASE pc[q] \in {"R1", "R3", "R4"}
              <7> USE <6>12
              <7> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY RemDef, Zenon
              <7>1. pc'[q] \in {"R1", "R3", "R4"}
                BY RemDef, Zenon
              <7>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2
            <6>13. CASE pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
              <7> USE <6>13
              <7> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY RemDef, Zenon
              <7>1. CASE p = q
                <8> USE <7>1
                <8>1. c.op[p] = "Remove" /\ c.arg[p] = arg[p] /\ c.res[p] = BOT
                  BY SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>1
              <7> SUFFICES ASSUME p # q
                           PROVE  c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <7>1
              <7>2. pc'[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                BY RemDef, Zenon DEF KeyInBktAtAddr
              <7>3. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <7>2, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>3
            <6>14. CASE pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
              <7> USE <6>14
              <7> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                BY RemDef, Zenon
              <7>1. CASE p = q
                <8> USE <7>1
                <8>1. r'[p] = NULL
                  BY Zenon
                <8>2. c.op[p] = "Remove" /\ c.arg[p] = arg[p] /\ c.res[p] = NULL
                  BY SPrimeRewrite, Zenon, RemDef, <8>1 DEF SPrime
                <8> QED
                  BY <8>2
              <7> SUFFICES ASSUME p # q
                           PROVE  c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                BY <7>1
              <7>2. pc'[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                BY RemDef, Zenon DEF KeyInBktAtAddr
              <7>3. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                BY <7>2, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>3
            <6>15. CASE pc[q] = "R5"
              <7> USE <6>15
              <7> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY RemDef, Zenon
              <7>1. pc'[q] = "R5" 
                BY RemDef, Zenon
              <7>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2
            <6> QED
                BY RemDef, ZenonT(120),
                    <6>1, <6>2, <6>3, <6>4, <6>5, <6>6, <6>7, <6>8, <6>9, 
                    <6>10, <6>11, <6>12, <6>13, <6>14, <6>15
                DEF LineIDs
          <5> QED
            BY <5>1, <5>2, Zenon DEF S
        <4>2. c \in P
          BY <4>1 DEF InvL1
        <4>3. c \in Evolve(P)
          BY <4>2, EmptySeqEvolve
        <4> QED
          BY <4>3
      <3>13. CASE Line = R3(p)
        <4> USE <3>13
        <4> SUFFICES ASSUME NEW c \in ConfigDomain,
                            c \in S'
                     PROVE  c \in P'
          BY Zenon DEF InvL1, S
        <4> /\ pc[p] = "R3" 
            /\ pc' = [pc EXCEPT ![p] = "R4"]
            /\ UNCHANGED <<A, bucket, r, arg, ret>>
          BY Zenon DEF R3
        <4>A. KeyInBktAtAddr(arg[p].key, bucket[p])
          BY DEF BktOK
        <4>B. PICK i \in 1..Len(MemLocs[bucket[p]]) : MemLocs[bucket[p]][i].key = arg[p].key
          BY Zenon, <4>A DEF KeyInBktAtAddr
        <4>C. i = CHOOSE index \in 1..Len(MemLocs[bucket[p]]) : MemLocs[bucket[p]][index].key = arg[p].key
          BY <4>B
        <4>D. i = IdxInBktAtAddr(arg[p].key, bucket[p])
          BY Zenon, <4>C DEF IdxInBktAtAddr
        <4> PICK addr \in Addrs :
                 /\ addr \notin AllocAddrs
                 /\ AllocAddrs' = AllocAddrs \cup {addr}
                 /\ newbkt' = [newbkt EXCEPT ![p] = addr]
                 /\ MemLocs' = [MemLocs EXCEPT ![addr] = SubSeq(MemLocs[bucket[p]], 1, i-1) \o SubSeq(MemLocs[bucket[p]], i+1, Len(MemLocs[bucket[p]]))]
          BY <4>D, Zenon DEF R3
        <4> /\ i \in 1..Len(MemLocs[bucket[p]])
            /\ MemLocs[bucket[p]][i].key = arg[p].key
          BY <4>B
        <4>1. c \in S
          <5>1. c.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL]
            <6>1. c.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]])' THEN ValOfKeyInBktAtAddr(k, A[Hash[k]])' ELSE NULL]
              BY Zenon, SPrimeRewrite DEF SPrime
            <6>2. \A k \in KeyDomain : KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
              <7> SUFFICES ASSUME NEW k \in KeyDomain
                           PROVE  KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
                OBVIOUS
              <7>1. A'[Hash[k]] = A[Hash[k]]
                BY Zenon
              <7>2. CASE A[Hash[k]] = NULL
                BY <7>1, <7>2 DEF KeyInBktAtAddr
              <7> SUFFICES ASSUME A[Hash[k]] # NULL
                           PROVE  KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
                BY <7>2
              <7>3. A[Hash[k]] \in AllocAddrs
                BY HashDef, Zenon
              <7>4. A[Hash[k]] # addr
                BY NULLDef, <7>3
              <7>5. \A a \in Addrs : a # addr => MemLocs'[a] = MemLocs[a]
                BY Zenon
              <7>6. MemLocs'[A'[Hash[k]]] = MemLocs[A[Hash[k]]]
                BY <7>1, <7>4, <7>5
              <7> QED
                BY <7>6, Zenon DEF KeyInBktAtAddr
            <6>3. \A k \in KeyDomain : KeyInBktAtAddr(k, A[Hash[k]]) => (ValOfKeyInBktAtAddr(k, A[Hash[k]]) = ValOfKeyInBktAtAddr(k, A[Hash[k]])')
              <7> SUFFICES ASSUME NEW k \in KeyDomain,
                                  NEW bkt_arr,
                                  A[Hash[k]] # NULL,
                                  bkt_arr = MemLocs[A[Hash[k]]],
                                  \E index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
                           PROVE  ValOfKeyInBktAtAddr(k, A[Hash[k]]) = ValOfKeyInBktAtAddr(k, A[Hash[k]])'
                BY Zenon DEF KeyInBktAtAddr
              <7>1. A'[Hash[k]] = A[Hash[k]]
                BY Zenon
              <7>2. A[Hash[k]] \in AllocAddrs
                BY HashDef, Zenon
              <7>3. A[Hash[k]] # addr
                BY NULLDef, <7>2
              <7>4. \A a \in Addrs : a # addr => MemLocs'[a] = MemLocs[a]                 
                BY Zenon
              <7>5. MemLocs'[A'[Hash[k]]] = MemLocs[A[Hash[k]]]
                BY <7>1, <7>3, <7>4
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
              <7>6. ValOfKeyInBktAtAddr(k, A[Hash[k]]) = bkt_arr[idx].val
                BY Zenon DEF ValOfKeyInBktAtAddr
              <7>7. ValOfKeyInBktAtAddr(k, A[Hash[k]])' = bkt_arr[idx].val
                BY Isa, <7>5 DEF ValOfKeyInBktAtAddr
              <7> QED
                BY <7>6, <7>7, Zenon
            <6> QED
              BY <6>1, <6>2, <6>3, Zenon
          <5>2. ASSUME NEW q \in ProcSet
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
            <6> USE <5>2
            <6>A. KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
              <7>1. bucket[q] = bucket'[q]
                BY Zenon
              <7>2. CASE bucket[q] = NULL
                BY <7>1, <7>2, Zenon DEF KeyInBktAtAddr
              <7> SUFFICES ASSUME bucket[q] # NULL
                           PROVE  KeyInBktAtAddr(arg[q].key, bucket[q]) = KeyInBktAtAddr(arg[q].key, bucket[q])'
                BY <7>2
              <7>3. bucket[q] \in AllocAddrs
                BY NULLDef, Zenon
              <7>4. bucket[q] # addr
                BY <7>3
              <7>5. \A a \in Addrs : a # addr => MemLocs'[a] = MemLocs[a]
                BY Zenon
              <7>6. MemLocs'[bucket'[q]] = MemLocs[bucket[q]]
                BY <7>1, <7>4, <7>5
              <7> QED
                BY <7>6, Zenon DEF KeyInBktAtAddr
            <6>B. KeyInBktAtAddr(arg[q].key, bucket[q]) => (ValOfKeyInBktAtAddr(arg[q].key, bucket[q]) = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])')
              <7> SUFFICES ASSUME NEW bkt_arr,
                                  bkt_arr = MemLocs[bucket[q]],
                                  bucket[q] # NULL,
                                  \E index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
                           PROVE  ValOfKeyInBktAtAddr(arg[q].key, bucket[q]) = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
                BY Zenon DEF KeyInBktAtAddr
              <7>1. bucket[q] = bucket'[q]
                BY Zenon
              <7>2. bucket[q] \in AllocAddrs
                BY NULLDef, Zenon
              <7>3. bucket[q] # addr
                BY <7>2
              <7>4. \A a \in Addrs : a # addr => MemLocs'[a] = MemLocs[a]
                BY Zenon
              <7>5. MemLocs'[bucket'[q]] = MemLocs[bucket[q]]
                BY <7>1, <7>3, <7>4 
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
              <7>6. ValOfKeyInBktAtAddr(arg[q].key, bucket[q]) = bkt_arr[idx].val
                BY Zenon DEF ValOfKeyInBktAtAddr
              <7>7. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = bkt_arr[idx].val
                BY Isa, <7>5 DEF ValOfKeyInBktAtAddr
              <7> QED
                BY <7>6, <7>7, Zenon
            <6>1. CASE pc[q] = RemainderID
              <7> USE <6>1
              <7> SUFFICES c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
                BY RemDef, Zenon
              <7>1. pc'[q] = RemainderID
                BY RemDef, Zenon
              <7>2. c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2
            <6>2. CASE pc[q] = "F1"
              <7> USE <6>2
              <7> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY RemDef, Zenon
              <7>1. pc'[q] = "F1"
                BY RemDef, Zenon
              <7>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2  
            <6>3. CASE pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
              <7> USE <6>3
              <7> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                BY RemDef, Zenon
              <7>1. pc'[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                BY <6>A, RemDef, Zenon DEF KeyInBktAtAddr
              <7>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
                BY <7>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7>3. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                BY <6>B, Zenon
              <7> QED
                BY <7>2, <7>3
            <6>4. CASE pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
              <7> USE <6>4
              <7> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                BY RemDef, Zenon
              <7>1. pc'[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                BY <6>A, RemDef, Zenon DEF KeyInBktAtAddr
              <7>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                BY <7>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2
            <6>5. CASE pc[q] = "F3" 
              <7> USE <6>5
              <7> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY RemDef, Zenon
              <7>1. pc'[q] = "F3"
                BY RemDef, Zenon
              <7>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2
            <6>6. CASE pc[q] \in {"I1", "I3", "I4"}
              <7> USE <6>6
              <7> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY RemDef, Zenon
              <7>2. pc'[q] \in {"I1", "I3", "I4"}
                BY RemDef, Zenon
              <7>3. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <7>2,  SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>3
            <6>7. CASE pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
              <7> USE <6>7
              <7> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                BY RemDef, Zenon
              <7>1. pc'[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                BY <6>A, RemDef, Zenon DEF KeyInBktAtAddr
              <7>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
                BY <7>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7>3. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                BY <6>B, Zenon
              <7> QED
                BY <7>2, <7>3
            <6>8. CASE pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
              <7> USE <6>8
              <7> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY RemDef, Zenon
              <7>1. pc'[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                BY <6>A, RemDef, Zenon DEF KeyInBktAtAddr
              <7>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <7>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2
            <6>9. CASE pc[q] = "I5"
              <7> USE <6>9
              <7> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY RemDef, Zenon
              <7>1. pc'[q] = "I5"
                BY RemDef, Zenon
              <7>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2
            <6>10. CASE pc[q] \in {"U1", "U2", "U3", "U4"}
              <7> USE <6>10
              <7> SUFFICES c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY RemDef, Zenon
              <7>1. pc'[q] \in {"U1", "U2", "U3", "U4"}
                BY RemDef, Zenon
              <7>2. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2
            <6>11. CASE pc[q] = "U5" 
              <7> USE <6>11
              <7> SUFFICES c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY RemDef, Zenon
              <7>1. pc'[q] = "U5"
                BY RemDef, Zenon
              <7>2. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2
            <6>12. CASE pc[q] \in {"R1", "R3", "R4"}
              <7> USE <6>12
              <7> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY RemDef, Zenon
              <7>1. pc'[q] \in {"R1", "R3", "R4"}
                BY RemDef, Zenon
              <7>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2
            <6>13. CASE pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
              <7> USE <6>13
              <7> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY RemDef, Zenon
              <7>1. pc'[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                BY <6>A, RemDef, Zenon DEF KeyInBktAtAddr
              <7>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <7>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime               
              <7> QED
                BY <7>2
            <6>14. CASE pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
              <7> USE <6>14
              <7> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                BY RemDef, Zenon
              <7>1. pc'[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                BY <6>A, RemDef, Zenon DEF KeyInBktAtAddr
              <7>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                BY <7>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2
            <6>15. CASE pc[q] = "R5"
              <7> USE <6>15
              <7> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY RemDef, Zenon
              <7>1. pc'[q] = "R5"
                BY RemDef, Zenon
              <7>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2
            <6> QED
                BY RemDef, ZenonT(120),
                   <6>1, <6>2, <6>3, <6>4, <6>5, <6>6, <6>7, <6>8, <6>9, 
                   <6>10, <6>11, <6>12, <6>13, <6>14, <6>15
                DEF LineIDs
          <5> QED
            BY <5>1, <5>2, Zenon DEF S
        <4>2. c \in P
          BY <4>1 DEF InvL1
        <4>3. c \in Evolve(P)
          BY <4>2, EmptySeqEvolve
        <4> QED
          BY <4>3
      <3>14. CASE Line = R4(p)
        <4> USE <3>14 DEF R4
        <4> SUFFICES ASSUME NEW c \in ConfigDomain,
                     c \in S'
                     PROVE c \in P'
          BY Zenon DEF InvL1, S
        <4>1. CASE A[Hash[arg[p].key]] = bucket[p]
          <5> USE <4>1
          <5> DEFINE c_pred == [state |-> [c.state EXCEPT ![arg[p].key] = ValOfKeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]])],
                                op    |-> c.op,
                                arg   |-> c.arg,
                                res   |-> [c.res EXCEPT ![p] = BOT]]
          <5>1. c_pred \in ConfigDomain
            <6>1. c_pred.state \in StateDomain
              <7>1. arg[p].key \in KeyDomain
                BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
              <7> KeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]])
                BY Zenon DEF BktOK
              <7> SUFFICES ValOfKeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]]) \in ValDomain
                BY <7>1 DEF StateDomain, ConfigDomain
              <7>2. PICK idx \in 1..Len(MemLocs[A[Hash[arg[p].key]]]) : MemLocs[A[Hash[arg[p].key]]][idx].key = arg[p].key
                BY Zenon DEF KeyInBktAtAddr
              <7>3. idx = CHOOSE index \in 1..Len(MemLocs[A[Hash[arg[p].key]]]) : MemLocs[A[Hash[arg[p].key]]][index].key = arg[p].key
                BY <7>2
              <7>4. ValOfKeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]]) = MemLocs[A[Hash[arg[p].key]]][idx].val
                BY Zenon, <7>3 DEF ValOfKeyInBktAtAddr
              <7>5. A[Hash[arg[p].key]] # NULL
                BY Zenon DEF KeyInBktAtAddr
              <7>6. MemLocs[A[Hash[arg[p].key]]] \in Seq([key: KeyDomain, val: ValDomain])
                BY Zenon, HashDef, NULLDef, <7>5
              <7>7. MemLocs[A[Hash[arg[p].key]]][idx] \in [key: KeyDomain, val: ValDomain]
                BY Zenon, <7>2, <7>6, ElementOfSeq
              <7>8. MemLocs[A[Hash[arg[p].key]]][idx].val \in ValDomain
                BY <7>7
              <7> QED
                BY <7>4, <7>8
            <6>2. c_pred.op \in [ProcSet -> OpDomain]
              BY DEF ConfigDomain
            <6>3. c_pred.arg \in [ProcSet -> ArgDomain]
              BY DEF ConfigDomain
            <6>4. c_pred.res \in [ProcSet -> ResDomain]
              BY DEF ConfigDomain, ResDomain
            <6> QED
              BY <6>1, <6>2, <6>3, <6>4 DEF ConfigDomain
          <5>2. c_pred \in S
            <6>1. c_pred.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL]
              <7> SUFFICES ASSUME NEW k \in KeyDomain
                           PROVE  c_pred.state[k] = IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL
                BY Zenon, <5>1 DEF StateDomain, ConfigDomain
              <7>1. CASE k = arg[p].key
                <8>1. arg[p].key \in KeyDomain
                  BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
                <8>2. KeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]]) 
                  BY Zenon DEF BktOK
                <8>3. c_pred.state[arg[p].key] = ValOfKeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]])
                  BY <8>1, Zenon DEF StateDomain, ConfigDomain
                <8> QED
                  BY <7>1, <8>2, <8>3 DEF StateDomain, ConfigDomain
              <7>2. CASE k # arg[p].key /\ Hash[k] # Hash[arg[p].key]
                <8> USE <7>2
                <8>1. c.state = [key \in KeyDomain |-> IF KeyInBktAtAddr(key, A[Hash[key]])' THEN ValOfKeyInBktAtAddr(key, A[Hash[key]])' ELSE NULL]
                  BY SPrimeRewrite, Zenon DEF SPrime
                <8>2. A'[Hash[k]] = A[Hash[k]]
                  BY HashDef, Zenon
                <8>3. KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
                  BY <8>2, Zenon DEF KeyInBktAtAddr
                <8>4. ValOfKeyInBktAtAddr(k, A[Hash[k]]) = ValOfKeyInBktAtAddr(k, A[Hash[k]])'
                  <9> DEFINE bkt_arr == MemLocs'[A'[Hash[k]]]
                  <9> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
                  <9>1. ValOfKeyInBktAtAddr(k, A[Hash[k]])' = bkt_arr[idx].val
                    BY Zenon DEF ValOfKeyInBktAtAddr
                  <9>2. bkt_arr = MemLocs[A[Hash[k]]]
                    BY Zenon, <8>2
                  <9>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
                    BY Zenon
                  <9>4. ValOfKeyInBktAtAddr(k, A[Hash[k]]) = MemLocs[A[Hash[k]]][CHOOSE index \in 1..Len(MemLocs[A[Hash[k]]]) : MemLocs[A[Hash[k]]][index].key = k].val
                    BY Zenon DEF ValOfKeyInBktAtAddr
                  <9>5. ValOfKeyInBktAtAddr(k, A[Hash[k]]) = bkt_arr[idx].val
                    BY ZenonT(90), <9>2, <9>3, <9>4
                  <9> QED
                    BY Zenon, <9>1, <9>5
                <8> QED
                  BY <8>1, <8>3, <8>4
              <7>3. CASE k # arg[p].key /\ Hash[k] = Hash[arg[p].key]
                <8> USE <7>3
                <8>1. c.state = [key \in KeyDomain |-> IF KeyInBktAtAddr(key, A[Hash[key]])' 
                                                          THEN ValOfKeyInBktAtAddr(key, A[Hash[key]])' 
                                                          ELSE NULL]
                  BY SPrimeRewrite, Zenon DEF SPrime
                <8>2. c_pred.state[k] = IF KeyInBktAtAddr(k, A[Hash[k]])' 
                                           THEN ValOfKeyInBktAtAddr(k, A[Hash[k]])' 
                                           ELSE NULL
                  BY <8>1
                <8>3. MemLocs' = MemLocs
                  BY Zenon
                <8>4. bucket[p] = A[Hash[k]]
                  BY Zenon
                <8>5. arg[p].key \in KeyDomain
                  BY RemDef, Zenon DEF ArgsOf, LineIDtoOp
                <8>6. newbkt[p] = A'[Hash[k]]
                  BY Zenon, <8>5, HashDef
                <8>7. KeyInBktAtAddr(k, A[Hash[k]])' = KeyInBktAtAddr(k, newbkt[p])
                  BY <8>6, Zenon DEF KeyInBktAtAddr
                <8>8. ValOfKeyInBktAtAddr(k, A[Hash[k]])' = ValOfKeyInBktAtAddr(k, newbkt[p])
                  BY <8>6, Zenon DEF ValOfKeyInBktAtAddr
                <8>9. c_pred.state[k] = IF KeyInBktAtAddr(k, newbkt[p]) THEN ValOfKeyInBktAtAddr(k, newbkt[p]) ELSE NULL
                  BY <8>2, <8>7, <8>8, Zenon
                <8>10. /\ KeyInBktAtAddr(k, bucket[p]) = KeyInBktAtAddr(k, newbkt[p])
                       /\ KeyInBktAtAddr(k, bucket[p]) => (ValOfKeyInBktAtAddr(k, bucket[p]) = ValOfKeyInBktAtAddr(k, newbkt[p]))
                  BY Zenon DEF NewBktOK
                <8>11. c_pred.state[k] = IF KeyInBktAtAddr(k, bucket[p]) THEN ValOfKeyInBktAtAddr(k, bucket[p]) ELSE NULL
                  BY <8>9, <8>10, Zenon
                <8>12. c_pred.state[k] = IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL
                  BY <8>11, <8>6, Zenon
                <8> QED
                  BY <8>12, Zenon
              <7> QED
                BY <7>1, <7>2, <7>3
            <6>2. ASSUME NEW q \in ProcSet
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
              <7> USE <6>2
              <7>1. CASE pc[q] = RemainderID
                <8> USE <7>1
                <8> SUFFICES c_pred.op[q] = BOT /\ c_pred.arg[q] = BOT /\ c_pred.res[q] = BOT
                  BY RemDef, Zenon
                <8>1. q # p
                  BY RemDef, Zenon
                <8>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                  BY <8>1
                <8>3. pc'[q] = RemainderID
                  BY RemDef, Zenon
                <8>4. c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
                  BY <8>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2, <8>4
              <7>2. CASE pc[q] = "F1"
                <8> USE <7>2
                <8> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
                  BY RemDef, Zenon
                <8>1. q # p
                  BY RemDef, Zenon
                <8>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                  BY <8>1
                <8>3. pc'[q] = "F1"
                  BY RemDef, Zenon
                <8>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY <8>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2, <8>4
              <7>3. CASE pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                <8> USE <7>3
                <8> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                  BY RemDef, Zenon
                <8>1. q # p
                  BY RemDef, Zenon
                <8>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                  BY <8>1
                <8>3. pc'[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY RemDef, Zenon DEF KeyInBktAtAddr
                <8>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY <8>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                  <9> DEFINE bkt_arr == MemLocs'[bucket'[q]]
                  <9> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg'[q].key
                  <9>1. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = bkt_arr[idx].val
                    BY Zenon DEF ValOfKeyInBktAtAddr
                  <9>2. bkt_arr = MemLocs[bucket[q]]
                    BY Zenon
                  <9>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
                    BY Zenon
                  <9> QED
                    BY <9>1, <9>2, <9>3, Isa DEF ValOfKeyInBktAtAddr
                <8> QED
                  BY <8>2, <8>4, <8>5
              <7>4. CASE pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                <8> USE <7>4
                <8> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = NULL
                  BY RemDef, Zenon
                <8>1. q # p
                  BY RemDef, Zenon
                <8>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                  BY <8>1
                <8>3. pc'[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY RemDef, Zenon DEF KeyInBktAtAddr
                <8>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                  BY <8>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2, <8>4
              <7>5. CASE pc[q] = "F3"
                <8> USE <7>5
                <8> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
                  BY RemDef, Zenon
                <8>1. q # p
                  BY RemDef, Zenon
                <8>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                  BY <8>1
                <8>3. pc'[q] = "F3"
                  BY RemDef, Zenon
                <8>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                  BY <8>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2, <8>4 
              <7>6. CASE pc[q] \in {"I1", "I3", "I4"}
                <8> USE <7>6
                <8> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
                  BY RemDef, Zenon
                <8>A. CASE p = q
                  <9> USE <8>A
                  <9>1. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = BOT
                    BY <5>1 DEF ConfigDomain
                  <9>2. pc'[q] = "I5"
                    BY Zenon
                  <9>3. c.op[q] = "Insert" /\ c.arg[p] = arg[q]
                    BY <9>2, SPrimeRewrite, Zenon, RemDef DEF SPrime
                  <9> QED
                    BY <9>1, <9>3
                <8> SUFFICES ASSUME p # q
                             PROVE  c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
                  BY <8>A
                <8>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                  OBVIOUS
                <8>3. pc'[q] \in {"I1", "I3", "I4"}
                  BY RemDef, Zenon
                <8>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY <8>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2, <8>4
              <7>7. CASE pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
                <8> USE <7>7
                <8> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                  BY RemDef, Zenon
                <8>1. q # p
                  BY RemDef, Zenon
                <8>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                  BY <8>1
                <8>3. pc'[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY RemDef, Zenon DEF KeyInBktAtAddr
                <8>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY <8>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                  <9> DEFINE bkt_arr == MemLocs'[bucket'[q]]
                  <9> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg'[q].key
                  <9>1. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = bkt_arr[idx].val
                    BY Zenon DEF ValOfKeyInBktAtAddr
                  <9>2. bkt_arr = MemLocs[bucket[q]]
                    BY Zenon
                  <9>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
                    BY Zenon
                  <9> QED
                    BY <9>1, <9>2, <9>3, Isa DEF ValOfKeyInBktAtAddr
                <8> QED
                  BY <8>2, <8>4, <8>5
              <7>8. CASE pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                <8> USE <7>8
                <8> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
                  BY RemDef, Zenon
                <8>1. q # p
                  BY RemDef, Zenon
                <8>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                  BY <8>1
                <8>3. pc'[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY RemDef, Zenon DEF KeyInBktAtAddr
                <8>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY <8>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2, <8>4
              <7>9. CASE pc[q] = "I5"
                <8> USE <7>9
                <8> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
                  BY RemDef, Zenon
                <8>1. q # p
                  BY RemDef, Zenon
                <8>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                  BY <8>1
                <8>3. pc'[q] = "I5"
                  BY RemDef, Zenon
                <8>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                  BY <8>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2, <8>4
              <7>10. CASE pc[q] \in {"U1", "U2", "U3", "U4"}
                <8> USE <7>10
                <8> SUFFICES c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
                  BY RemDef, Zenon
                <8>1. q # p
                  BY Zenon
                <8>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                  BY <8>1
                <8>3. pc'[q] \in {"U1", "U2", "U3", "U4"}
                  BY RemDef, Zenon
                <8>4. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY <8>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2, <8>4
              <7>11. CASE pc[q] = "U5" 
                <8> USE <7>11
                <8> SUFFICES c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
                  BY RemDef, Zenon
                <8>1. q # p
                  BY RemDef, Zenon
                <8>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                  BY <8>1
                <8>3. pc'[q] = "U5"
                  BY RemDef, Zenon
                <8>4. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                  BY <8>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2, <8>4
              <7>12. CASE pc[q] \in {"R1", "R3", "R4"}
                <8> USE <7>12
                <8> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
                  BY RemDef, Zenon
                <8>1. CASE q = p
                  <9> USE <8>1
                  <9>1. pc'[q] = "R5"
                    BY Zenon
                  <9>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r'[q]
                    BY <9>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
                  <9>3. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = BOT
                    BY DEF ConfigDomain 
                  <9> QED
                    BY <9>2, <9>3
                <8> SUFFICES ASSUME q # p
                             PROVE  c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
                  BY <8>1
                <8>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                  OBVIOUS
                <8>3. pc'[q] \in {"R1", "R3", "R4"}
                  BY RemDef, Zenon
                <8>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY <8>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2, <8>4
              <7>13. CASE pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q]) 
                <8> USE <7>13
                <8> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
                  BY RemDef, Zenon
                <8>1. q # p
                  BY RemDef, Zenon
                <8>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                  BY <8>1
                <8>3. pc'[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY RemDef, Zenon DEF KeyInBktAtAddr
                <8>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                  BY <8>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2, <8>4              
              <7>14. CASE pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
                <8> USE <7>14
                <8> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = NULL
                  BY RemDef, Zenon
                <8>1. q # p
                  BY RemDef, Zenon
                <8>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                  BY <8>1
                <8>3. pc'[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                  BY RemDef, Zenon DEF KeyInBktAtAddr
                <8>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                  BY <8>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2, <8>4    
              <7>15. CASE pc[q] = "R5"
                <8> USE <7>15
                <8> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
                  BY RemDef, Zenon
                <8>1. q # p
                  BY RemDef, Zenon
                <8>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                  BY <8>1
                <8>3. pc'[q] = "R5"
                  BY RemDef, Zenon
                <8>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                  BY <8>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>2, <8>4
              <7> QED
                  BY RemDef, ZenonT(120),
                     <7>1, <7>2, <7>3, <7>4, <7>5, <7>6, <7>7, <7>8, <7>9, 
                     <7>10, <7>11, <7>12, <7>13, <7>14, <7>15
                  DEF LineIDs 
            <6> QED
              BY <5>1, <6>1, <6>2, Zenon DEF S
          <5>3. c_pred \in P
            BY <5>2 DEF InvL1
          <5>4. Delta(c_pred, p, c)
            <6>1. c_pred.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL]
              BY <5>1, <5>2, Zenon DEF S
            <6>2. c_pred.op[p] = "Remove" /\ c_pred.arg[p] = arg[p] /\ c_pred.res[p] = BOT
              BY <5>1, <5>2, Zenon, RemDef DEF S
            <6>3. arg[p] \in ArgsOf("Remove") /\ arg[p].key \in KeyDomain
              BY RemDef, Zenon DEF ArgsOf, LineIDtoOp 
            <6> SUFFICES /\ c.state = [c_pred.state EXCEPT ![arg[p].key] = NULL]
                         /\ c.res = [c_pred.res EXCEPT ![p] = c_pred.state[arg[p].key]]
              BY <6>2, <6>3, Zenon DEF Delta
            <6> SUFFICES /\ c.state[arg[p].key] = NULL
                         /\ c.res = [c_pred.res EXCEPT ![p] = c_pred.state[arg[p].key]]
              BY <6>2, <6>3, Zenon DEF ConfigDomain, StateDomain
            <6>A. c_pred.state[arg[p].key] = IF KeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]]) 
                                             THEN ValOfKeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]]) 
                                             ELSE NULL
              BY <6>1, <6>2, <6>3, Zenon DEF ConfigDomain, StateDomain
            <6> SUFFICES /\ c.state[arg[p].key] = NULL
                         /\ c.res[p] = IF KeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]]) 
                                          THEN ValOfKeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]]) 
                                          ELSE NULL
              BY <5>2, <6>A, Zenon DEF ConfigDomain
            <6>X. KeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]]) 
              BY Zenon DEF BktOK
            <6> SUFFICES /\ c.state[arg[p].key] = NULL
                         /\ c.res[p] = ValOfKeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]]) 
              BY Zenon, <6>X 
            <6>4. c.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]])' THEN ValOfKeyInBktAtAddr(k, A[Hash[k]])' ELSE NULL]
              BY SPrimeRewrite, Zenon DEF SPrime
            <6>5. c.state[arg[p].key] = IF KeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]])' THEN ValOfKeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]])' ELSE NULL
              BY <6>4, <6>3, Zenon
            <6>6. newbkt[p] = A'[Hash[arg[p].key]]
              BY Zenon, HashDef, <6>3
            <6>7. MemLocs[A'[Hash[arg[p].key]]] = MemLocs[newbkt[p]]
              BY Zenon, <6>6
            <6>8. KeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]])' = KeyInBktAtAddr(arg[p].key, newbkt[p])
              BY Zenon, <6>6 DEF KeyInBktAtAddr
            <6>B. ~KeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]])'
              BY Zenon, <6>8 DEF NewBktOK
            <6>C. c.state[arg[p].key] = NULL
              BY Zenon, <6>5, <6>B
            <6>15. pc'[p] = "R5"
              BY Zenon
            <6>16. c.res[p] = r'[p]
              BY <6>15, SPrimeRewrite, RemDef, Zenon DEF SPrime
            <6>17. c.res[p] = ValOfKeyInBktAtAddr(arg[p].key, bucket[p])
              BY <6>16, Zenon DEF BktOK
            <6>18. c.res[p] = ValOfKeyInBktAtAddr(arg[p].key, A[Hash[arg[p].key]])
              BY <6>17, Zenon
            <6> QED
              BY <6>18, <6>C
          <5>5. c \in Evolve(P)
            BY <5>1, <5>3, <5>4, SingleDeltaEvolve
          <5> QED
            BY <5>5
        <4>2. CASE A[Hash[arg[p].key]] # bucket[p]
          <5> USE <4>2
          <5>0. ASSUME c \in S
                PROVE  c \in P'
            <6> USE <5>0
            <6>1. c \in P
              BY DEF InvL1
            <6>2. c \in Evolve(P)
              BY <6>1, EmptySeqEvolve
            <6> QED
              BY <6>2
          <5> SUFFICES c \in S
            BY <5>0
          <5>1. c.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL]
            <6>1. c.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]])' THEN ValOfKeyInBktAtAddr(k, A[Hash[k]])' ELSE NULL]
              BY Zenon, SPrimeRewrite DEF SPrime
            <6>2. \A k \in KeyDomain : KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
              BY Zenon DEF KeyInBktAtAddr
            <6>3. \A k \in KeyDomain : ValOfKeyInBktAtAddr(k, A[Hash[k]])' = ValOfKeyInBktAtAddr(k, A[Hash[k]])
              <7> SUFFICES ASSUME NEW k \in KeyDomain
                           PROVE  ValOfKeyInBktAtAddr(k, A[Hash[k]])' = ValOfKeyInBktAtAddr(k, A[Hash[k]])
                OBVIOUS
              <7> bkt_arr == MemLocs'[A'[Hash[k]]]
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
              <7>1. ValOfKeyInBktAtAddr(k, A[Hash[k]])' = bkt_arr[idx].val
                BY DEF ValOfKeyInBktAtAddr
              <7>2. bkt_arr = MemLocs[A[Hash[k]]]
                BY Zenon
              <7> QED
                BY <7>1, <7>2, ZenonT(30) DEF ValOfKeyInBktAtAddr
            <6> QED
              BY <6>1, <6>2, <6>3
          <5>2. ASSUME NEW q \in ProcSet
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
            <6> USE <5>2
            <6>A. \A k \in KeyDomain : KeyInBktAtAddr(k, bucket[q]) = KeyInBktAtAddr(k, bucket[q])'
              BY Zenon DEF KeyInBktAtAddr
            <6>B. \A k \in KeyDomain : ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, bucket[q])
              <7> SUFFICES ASSUME NEW k \in KeyDomain
                           PROVE  ValOfKeyInBktAtAddr(k, bucket[q])' = ValOfKeyInBktAtAddr(k, bucket[q])
                OBVIOUS
              <7> bkt_arr == MemLocs'[bucket'[q]]
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
              <7>1. ValOfKeyInBktAtAddr(k, bucket[q])' = bkt_arr[idx].val
                BY DEF ValOfKeyInBktAtAddr
              <7>2. bkt_arr = MemLocs[bucket[q]]
                BY Zenon
              <7> QED
                BY <7>1, <7>2, ZenonT(30) DEF ValOfKeyInBktAtAddr
            <6>1. CASE pc[q] = RemainderID
              <7> USE <6>1
              <7> SUFFICES c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
                BY RemDef, Zenon
              <7>1. pc'[q] = RemainderID
                BY RemDef, Zenon
              <7>2. c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2
            <6>2. CASE pc[q] = "F1"
              <7> USE <6>2
              <7> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY RemDef, Zenon
              <7>1. pc'[q] = "F1"
                BY RemDef, Zenon
              <7>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2
            <6>3. CASE pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
              <7> USE <6>3
              <7> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                BY RemDef, Zenon
              <7>1. pc'[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                BY RemDef, Zenon DEF KeyInBktAtAddr
              <7>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
                BY <7>1,  SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7>3. arg[q].key = arg'[q].key /\ arg[q].key \in KeyDomain
                BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
              <7>4. c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                BY <7>2, <7>3, <6>B
              <7> QED
                BY <7>2, <7>4
            <6>4. CASE pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
              <7> USE <6>4
              <7> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                BY RemDef, Zenon
              <7>2. pc'[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                BY RemDef, Zenon DEF KeyInBktAtAddr
              <7>3. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                BY <7>2,  SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>3
            <6>5. CASE pc[q] = "F3"
              <7> USE <6>5
              <7> SUFFICES c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY RemDef, Zenon
              <7>1. pc'[q] = "F3"
                BY RemDef, Zenon
              <7>2. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2 
            <6>6. CASE pc[q] \in {"I1", "I3", "I4"}
              <7> USE <6>6
              <7> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY RemDef, Zenon
              <7>1. pc'[q] \in {"I1", "I3", "I4"}
                BY RemDef, Zenon
              <7>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2 
            <6>7. CASE pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
              <7> USE <6>7
              <7> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                BY RemDef, Zenon
              <7>1. CASE p = q
                <8> USE <7>1
                <8>1. c.op[p] = "Insert" /\ c.arg[p] = arg[p] /\ c.res[p] = r'[p]
                  BY SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8>2. r'[p] = ValOfKeyInBktAtAddr(arg[p].key, bucket[p])
                  BY Zenon
                <8> QED
                  BY <8>1, <8>2
              <7> SUFFICES ASSUME p # q
                           PROVE  c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                BY <7>1
              <7>2. pc'[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                BY RemDef, Zenon DEF KeyInBktAtAddr
              <7>3. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
                BY <7>2,  SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7>4. arg[q].key = arg'[q].key /\ arg[q].key \in KeyDomain
                BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
              <7>5. c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                BY <7>3, <7>4, <6>B
              <7> QED
                BY <7>3, <7>5
            <6>8. CASE pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
              <7> USE <6>8
              <7> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY RemDef, Zenon
              <7>1. CASE p = q
                <8> USE <7>1
                <8>1. c.op[p] = "Insert" /\ c.arg[p] = arg[p] /\ c.res[p] = BOT
                  BY SPrimeRewrite, Zenon, RemDef DEF SPrime
                <8> QED
                  BY <8>1
              <7> SUFFICES ASSUME p # q
                           PROVE  c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <7>1
              <7>2. pc'[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                BY RemDef, Zenon DEF KeyInBktAtAddr
              <7>3. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <7>2, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>3 
            <6>9. CASE pc[q] = "I5"
              <7> USE <6>9
              <7> SUFFICES c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY RemDef, Zenon
              <7>1. pc'[q] = "I5"
                BY RemDef, Zenon 
              <7>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2 
            <6>10. CASE pc[q] \in {"U1", "U2", "U3", "U4"}
              <7> USE <6>10
              <7> SUFFICES c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY RemDef, Zenon
              <7>1. pc'[q] \in {"U1", "U2", "U3", "U4"}
                BY RemDef, Zenon
              <7>2. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2
            <6>11. CASE pc[q] = "U5" 
              <7> USE <6>11
              <7> SUFFICES c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY RemDef, Zenon
              <7>1. pc'[q] = "U5"
                BY RemDef, Zenon
              <7>2. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2
            <6>12. CASE pc[q] \in {"R1", "R3", "R4"}
              <7> USE <6>12
              <7> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY RemDef, Zenon
              <7>1. pc'[q] \in {"R1", "R3", "R4"}
                BY RemDef, Zenon
              <7>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2
            <6>13. CASE pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
              <7> USE <6>13
              <7> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY RemDef, Zenon
              <7>1. pc'[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                BY RemDef, Zenon DEF KeyInBktAtAddr
              <7>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2
            <6>14. CASE pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
              <7> USE <6>14
              <7> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                BY RemDef, Zenon
              <7>1. pc'[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                BY RemDef, Zenon DEF KeyInBktAtAddr
              <7>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2
            <6>15. CASE pc[q] = "R5"
              <7> USE <6>15
              <7> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY RemDef, Zenon
              <7>1. pc'[q] = "R5" 
                BY RemDef, Zenon
              <7>2. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY <7>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2
            <6> QED
                BY RemDef, ZenonT(120),
                    <6>1, <6>2, <6>3, <6>4, <6>5, <6>6, <6>7, <6>8, <6>9, 
                    <6>10, <6>11, <6>12, <6>13, <6>14, <6>15
                DEF LineIDs
          <5> QED
            BY <5>1, <5>2, Zenon DEF S
        <4> QED
          BY <4>1, <4>2
      <3> QED
        BY Zenon, <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, 
                  <3>7, <3>8, <3>9, <3>10, <3>11, <3>12, <3>13, <3>14 DEF IntLines
    <2>3. CASE RetLine(p)
      <3> SUFFICES ASSUME NEW Line \in RetLines(p), Line,
                          P' = Filter(Evolve(P), p, ret'[p])
                   PROVE  InvL1'
        BY <2>3 DEF RetLine
      <3>1. CASE Line = F3(p)
        <4> USE <3>1 DEF F3
        <4> SUFFICES ASSUME NEW c \in ConfigDomain,
                            c \in S'
                     PROVE  c \in P'
          BY Zenon DEF InvL1, S
        <4> DEFINE c_pred == [state |-> c.state,
                              op    |-> [c.op EXCEPT ![p] = "Find"],
                              arg   |-> [c.arg EXCEPT ![p] = arg[p]],
                              res   |-> [c.res EXCEPT ![p] = r[p]]]
        <4>1. c_pred \in ConfigDomain
          <5>1. c_pred.state \in StateDomain
            BY DEF ConfigDomain
          <5>2. c_pred.op \in [ProcSet -> OpDomain]
            BY DEF ConfigDomain, OpDomain
          <5>3. c_pred.arg \in [ProcSet -> ArgDomain]
            BY DEF ConfigDomain, ArgDomain
          <5>4. c_pred.res \in [ProcSet -> ResDomain]
            BY DEF ConfigDomain, ResDomain
          <5> QED
            BY <5>1, <5>2, <5>3, <5>4 DEF ConfigDomain
        <4>2. c_pred \in S
          <5>1. c_pred.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL]
            <6>1. c_pred.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]])' THEN ValOfKeyInBktAtAddr(k, A[Hash[k]])' ELSE NULL]
              BY Zenon, SPrimeRewrite DEF SPrime
            <6>2. \A k \in KeyDomain : KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
              BY Zenon DEF KeyInBktAtAddr
            <6>3. \A k \in KeyDomain : ValOfKeyInBktAtAddr(k, A[Hash[k]])' = ValOfKeyInBktAtAddr(k, A[Hash[k]])
              <7> SUFFICES ASSUME NEW k \in KeyDomain
                           PROVE  ValOfKeyInBktAtAddr(k, A[Hash[k]])' = ValOfKeyInBktAtAddr(k, A[Hash[k]])
                OBVIOUS
              <7> bkt_arr == MemLocs'[A'[Hash[k]]]
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
              <7>1. ValOfKeyInBktAtAddr(k, A[Hash[k]])' = bkt_arr[idx].val
                BY DEF ValOfKeyInBktAtAddr
              <7>2. bkt_arr = MemLocs[A[Hash[k]]]
                BY Zenon
              <7> QED
                BY <7>1, <7>2, ZenonT(30) DEF ValOfKeyInBktAtAddr
            <6> QED
              BY <6>1, <6>2, <6>3
          <5>2. ASSUME NEW q \in ProcSet
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
            <6> USE <5>2
            <6>1. CASE pc[q] = RemainderID
              <7> SUFFICES c_pred.op[q] = BOT /\ c_pred.arg[q] = BOT /\ c_pred.res[q] = BOT
                BY <6>1, RemDef, Zenon
              <7>1. q # p
                BY <6>1, RemDef, Zenon
              <7>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                BY <7>1
              <7>3. pc'[q] = RemainderID
                BY <6>1, RemDef, Zenon
              <7>4. c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
                BY <7>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2, <7>4
            <6>2. CASE pc[q] = "F1"
              <7> USE <6>2
              <7> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
                BY RemDef, Zenon
              <7>1. q # p
                BY RemDef, Zenon
              <7>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                BY <7>1
              <7>3. pc'[q] = "F1"
                BY RemDef, Zenon
              <7>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <7>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2, <7>4
            <6>3. CASE pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
              <7> USE <6>3
              <7> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                BY RemDef, Zenon
              <7>1. q # p
                BY RemDef, Zenon
              <7>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                BY <7>1
              <7>3. pc'[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                BY RemDef, Zenon DEF KeyInBktAtAddr
              <7>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
                BY <7>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                <8> DEFINE bkt_arr == MemLocs'[bucket'[q]]
                <8> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg'[q].key
                <8>1. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = bkt_arr[idx].val
                  BY Zenon DEF ValOfKeyInBktAtAddr
                <8>2. bkt_arr = MemLocs[bucket[q]]
                  BY Zenon
                <8>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
                  BY Zenon
                <8> QED
                  BY <8>1, <8>2, <8>3, Isa DEF ValOfKeyInBktAtAddr
              <7> QED
                BY <7>2, <7>4, <7>5
            <6>4. CASE pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
              <7> USE <6>4
              <7> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = NULL
                BY RemDef, Zenon
              <7>1. q # p
                BY RemDef, Zenon
              <7>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                BY <7>1
              <7>3. pc'[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                BY RemDef, Zenon DEF KeyInBktAtAddr
              <7>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                BY <7>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2, <7>4
            <6>5. CASE pc[q] = "F3"
              <7> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
                BY <6>5, RemDef, Zenon
              <7>1. CASE q = p
                BY <7>1 DEF ConfigDomain
              <7> SUFFICES ASSUME q # p
                           PROVE  c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
                BY <7>1
              <7>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                OBVIOUS
              <7>3. pc'[q] = "F3"
                BY <6>5, RemDef, Zenon
              <7>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY <7>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2, <7>4
            <6>6. CASE pc[q] \in {"I1", "I3", "I4"}
              <7> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
                BY <6>6, RemDef, Zenon
              <7>1. q # p
                BY <6>6, RemDef, Zenon
              <7>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                BY <7>1
              <7>3. pc'[q] \in {"I1", "I3", "I4"}
                BY <6>6, RemDef, Zenon
              <7>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <7>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2, <7>4
            <6>7. CASE pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
              <7> USE <6>7
              <7> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                BY RemDef, Zenon
              <7>1. q # p
                BY RemDef, Zenon
              <7>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                BY <7>1
              <7>3. pc'[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                BY RemDef, Zenon DEF KeyInBktAtAddr
              <7>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
                BY <7>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                <8> DEFINE bkt_arr == MemLocs'[bucket'[q]]
                <8> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg'[q].key
                <8>1. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = bkt_arr[idx].val
                  BY Zenon DEF ValOfKeyInBktAtAddr
                <8>2. bkt_arr = MemLocs[bucket[q]]
                  BY Zenon
                <8>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
                  BY Zenon
                <8> QED
                  BY <8>1, <8>2, <8>3, Isa DEF ValOfKeyInBktAtAddr
              <7> QED
                BY <7>2, <7>4, <7>5
            <6>8. CASE pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
              <7> USE <6>8
              <7> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
                BY RemDef, Zenon
              <7>1. q # p
                BY RemDef, Zenon
              <7>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                BY <7>1
              <7>3. pc'[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                BY RemDef, Zenon DEF KeyInBktAtAddr
              <7>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <7>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2, <7>4
            <6>9. CASE pc[q] = "I5"
              <7> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
                BY <6>9, RemDef, Zenon
              <7>1. q # p
                BY <6>9, RemDef, Zenon
              <7>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                BY <7>1
              <7>3. pc'[q] = "I5"
                BY <6>9, RemDef, Zenon
              <7>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY <7>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2, <7>4
            <6>10. CASE pc[q] \in {"U1", "U2", "U3", "U4"}
              <7> USE <6>10
              <7> SUFFICES c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
                BY RemDef, Zenon
              <7>1. q # p
                BY RemDef, Zenon
              <7>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                BY <7>1
              <7>3. pc'[q] \in {"U1", "U2", "U3", "U4"}
                BY RemDef, Zenon
              <7>4. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <7>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2, <7>4
            <6>11. CASE pc[q] = "U5"
              <7> USE <6>11
              <7> SUFFICES c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
                BY RemDef, Zenon
              <7>1. q # p
                BY RemDef, Zenon
              <7>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                BY <7>1
              <7>3. pc'[q] = "U5"
                BY RemDef, Zenon
              <7>4. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY <7>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2, <7>4
            <6>12. CASE pc[q] \in {"R1", "R3", "R4"}
              <7> USE <6>12
              <7> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
                BY RemDef, Zenon
              <7>1. q # p
                BY RemDef, Zenon
              <7>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                BY <7>1
              <7>3. pc'[q] \in {"R1", "R3", "R4"}
                BY RemDef, Zenon
              <7>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <7>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2, <7>4
            <6>13. CASE pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
              <7> USE <6>13
              <7> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
                BY RemDef, Zenon
              <7>1. q # p
                BY RemDef, Zenon
              <7>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                BY <7>1
              <7>3. pc'[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                BY RemDef, Zenon DEF KeyInBktAtAddr
              <7>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <7>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2, <7>4
            <6>14. CASE pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
              <7> USE <6>14
              <7> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = NULL
                BY RemDef, Zenon
              <7>1. q # p
                BY RemDef, Zenon
              <7>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                BY <7>1
              <7>3. pc'[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                BY RemDef, Zenon DEF KeyInBktAtAddr
              <7>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                BY <7>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2, <7>4
            <6>15. CASE pc[q] = "R5"
              <7> USE <6>15
              <7> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
                BY RemDef, Zenon
              <7>1. q # p
                BY RemDef, Zenon
              <7>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                BY <7>1
              <7>3. pc'[q] = "R5"
                BY RemDef, Zenon
              <7>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY <7>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2, <7>4
            <6> QED
              BY RemDef, ZenonT(120),
                 <6>1, <6>2, <6>3, <6>4, <6>5, <6>6, <6>7, <6>8, <6>9, 
                 <6>10, <6>11, <6>12, <6>13, <6>14, <6>15
              DEF LineIDs
          <5> QED
            BY <4>1, <5>1, <5>2, Zenon DEF S
        <4>3. c_pred \in P
          BY <4>2 DEF InvL1
        <4>4. c_pred \in Evolve(P)
          BY <4>1, <4>3, EmptySeqEvolve
        <4>5. c_pred.res[p] = ret'[p]
          BY Zenon DEF ConfigDomain
        <4>6. c.op[p] = BOT /\ c.arg[p] = BOT /\ c.res[p] = BOT
          BY Zenon, SPrimeRewrite, RemDef DEF SPrime
        <4>7. c.op = [c_pred.op EXCEPT ![p] = BOT]
          BY Zenon, <4>6 DEF ConfigDomain
        <4>8. c.arg = [c_pred.arg EXCEPT ![p] = BOT]
          BY Zenon, <4>6 DEF ConfigDomain
        <4>9. c.res = [c_pred.res EXCEPT ![p] = BOT]
          BY Zenon, <4>6 DEF ConfigDomain
        <4>10. c.state = c_pred.state
          OBVIOUS
        <4>11. c \in Filter(Evolve(P), p, ret'[p])
          BY <4>4, <4>5, <4>7, <4>8, <4>9, <4>10, Zenon DEF Filter
        <4> QED
          BY <4>11
      <3>2. CASE Line = I5(p)
        <4> USE <3>2 DEF I5
        <4> SUFFICES ASSUME NEW c \in ConfigDomain,
                            c \in S'
                     PROVE  c \in P'
          BY Zenon DEF InvL1, S
        <4> DEFINE c_pred == [state |-> c.state,
                              op    |-> [c.op EXCEPT ![p] = "Insert"],
                              arg   |-> [c.arg EXCEPT ![p] = arg[p]],
                              res   |-> [c.res EXCEPT ![p] = r[p]]]
        <4>1. c_pred \in ConfigDomain
          <5>1. c_pred.state \in StateDomain
            BY DEF ConfigDomain
          <5>2. c_pred.op \in [ProcSet -> OpDomain]
            BY DEF ConfigDomain, OpDomain
          <5>3. c_pred.arg \in [ProcSet -> ArgDomain]
            BY DEF ConfigDomain, ArgDomain
          <5>4. c_pred.res \in [ProcSet -> ResDomain]
            BY DEF ConfigDomain, ResDomain
          <5> QED
            BY <5>1, <5>2, <5>3, <5>4 DEF ConfigDomain
        <4>2. c_pred \in S
          <5>1. c_pred.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL]
            <6>1. c_pred.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]])' THEN ValOfKeyInBktAtAddr(k, A[Hash[k]])' ELSE NULL]
              BY Zenon, SPrimeRewrite DEF SPrime
            <6>2. \A k \in KeyDomain : KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
              BY Zenon DEF KeyInBktAtAddr
            <6>3. \A k \in KeyDomain : ValOfKeyInBktAtAddr(k, A[Hash[k]])' = ValOfKeyInBktAtAddr(k, A[Hash[k]])
              <7> SUFFICES ASSUME NEW k \in KeyDomain
                           PROVE  ValOfKeyInBktAtAddr(k, A[Hash[k]])' = ValOfKeyInBktAtAddr(k, A[Hash[k]])
                OBVIOUS
              <7> bkt_arr == MemLocs'[A'[Hash[k]]]
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
              <7>1. ValOfKeyInBktAtAddr(k, A[Hash[k]])' = bkt_arr[idx].val
                BY DEF ValOfKeyInBktAtAddr
              <7>2. bkt_arr = MemLocs[A[Hash[k]]]
                BY Zenon
              <7> QED
                BY <7>1, <7>2, ZenonT(30) DEF ValOfKeyInBktAtAddr
            <6> QED
              BY <6>1, <6>2, <6>3
          <5>2. ASSUME NEW q \in ProcSet
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
            <6> USE <5>2
            <6>1. CASE pc[q] = RemainderID
              <7> SUFFICES c_pred.op[q] = BOT /\ c_pred.arg[q] = BOT /\ c_pred.res[q] = BOT
                BY <6>1, RemDef, Zenon
              <7>1. q # p
                BY <6>1, RemDef, Zenon
              <7>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                BY <7>1
              <7>3. pc'[q] = RemainderID
                BY <6>1, RemDef, Zenon
              <7>4. c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
                BY <7>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2, <7>4
            <6>2. CASE pc[q] = "F1"
              <7> USE <6>2
              <7> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
                BY RemDef, Zenon
              <7>1. q # p
                BY RemDef, Zenon
              <7>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                BY <7>1
              <7>3. pc'[q] = "F1"
                BY RemDef, Zenon
              <7>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <7>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2, <7>4
            <6>3. CASE pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
              <7> USE <6>3
              <7> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                BY RemDef, Zenon
              <7>1. q # p
                BY RemDef, Zenon
              <7>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                BY <7>1
              <7>3. pc'[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                BY RemDef, Zenon DEF KeyInBktAtAddr
              <7>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
                BY <7>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                <8> DEFINE bkt_arr == MemLocs'[bucket'[q]]
                <8> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg'[q].key
                <8>1. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = bkt_arr[idx].val
                  BY Zenon DEF ValOfKeyInBktAtAddr
                <8>2. bkt_arr = MemLocs[bucket[q]]
                  BY Zenon
                <8>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
                  BY Zenon
                <8> QED
                  BY <8>1, <8>2, <8>3, Isa DEF ValOfKeyInBktAtAddr
              <7> QED
                BY <7>2, <7>4, <7>5
            <6>4. CASE pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
              <7> USE <6>4
              <7> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = NULL
                BY RemDef, Zenon
              <7>1. q # p
                BY RemDef, Zenon
              <7>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                BY <7>1
              <7>3. pc'[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                BY RemDef, Zenon DEF KeyInBktAtAddr
              <7>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                BY <7>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2, <7>4
            <6>5. CASE pc[q] = "F3"
              <7> USE <6>5
              <7> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
                BY <6>5, RemDef, Zenon
              <7>1. q # p
                BY RemDef, Zenon
              <7>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                BY <7>1
              <7>3. pc'[q] = "F3"
                BY <6>5, RemDef, Zenon
              <7>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY <7>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2, <7>4
            <6>6. CASE pc[q] \in {"I1", "I3", "I4"}
              <7> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
                BY <6>6, RemDef, Zenon
              <7>1. q # p
                BY <6>6, RemDef, Zenon
              <7>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                BY <7>1
              <7>3. pc'[q] \in {"I1", "I3", "I4"}
                BY <6>6, RemDef, Zenon
              <7>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <7>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2, <7>4
            <6>7. CASE pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
              <7> USE <6>7
              <7> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                BY RemDef, Zenon
              <7>1. q # p
                BY RemDef, Zenon
              <7>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                BY <7>1
              <7>3. pc'[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                BY RemDef, Zenon DEF KeyInBktAtAddr
              <7>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
                BY <7>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                <8> DEFINE bkt_arr == MemLocs'[bucket'[q]]
                <8> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg'[q].key
                <8>1. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = bkt_arr[idx].val
                  BY Zenon DEF ValOfKeyInBktAtAddr
                <8>2. bkt_arr = MemLocs[bucket[q]]
                  BY Zenon
                <8>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
                  BY Zenon
                <8> QED
                  BY <8>1, <8>2, <8>3, Isa DEF ValOfKeyInBktAtAddr
              <7> QED
                BY <7>2, <7>4, <7>5
            <6>8. CASE pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
              <7> USE <6>8
              <7> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
                BY RemDef, Zenon
              <7>1. q # p
                BY RemDef, Zenon
              <7>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                BY <7>1
              <7>3. pc'[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                BY RemDef, Zenon DEF KeyInBktAtAddr
              <7>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <7>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2, <7>4
            <6>9. CASE pc[q] = "I5"
              <7> USE <6>9
              <7> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
                BY <6>9, RemDef, Zenon
              <7>1. CASE q = p
                BY <7>1 DEF ConfigDomain
              <7> SUFFICES ASSUME q # p
                           PROVE  c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
                BY <7>1
              <7>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                OBVIOUS
              <7>3. pc'[q] = "I5"
                BY <6>9, RemDef, Zenon
              <7>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY <7>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2, <7>4
            <6>10. CASE pc[q] \in {"U1", "U2", "U3", "U4"}
              <7> USE <6>10
              <7> SUFFICES c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
                BY RemDef, Zenon
              <7>1. q # p
                BY RemDef, Zenon
              <7>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                BY <7>1
              <7>3. pc'[q] \in {"U1", "U2", "U3", "U4"}
                BY RemDef, Zenon
              <7>4. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <7>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2, <7>4
            <6>11. CASE pc[q] = "U5"
              <7> USE <6>11
              <7> SUFFICES c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
                BY RemDef, Zenon
              <7>1. q # p
                BY RemDef, Zenon
              <7>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                BY <7>1
              <7>3. pc'[q] = "U5"
                BY RemDef, Zenon
              <7>4. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY <7>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2, <7>4
            <6>12. CASE pc[q] \in {"R1", "R3", "R4"}
              <7> USE <6>12
              <7> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
                BY RemDef, Zenon
              <7>1. q # p
                BY RemDef, Zenon
              <7>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                BY <7>1
              <7>3. pc'[q] \in {"R1", "R3", "R4"}
                BY RemDef, Zenon
              <7>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <7>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2, <7>4
            <6>13. CASE pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
              <7> USE <6>13
              <7> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
                BY RemDef, Zenon
              <7>1. q # p
                BY RemDef, Zenon
              <7>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                BY <7>1
              <7>3. pc'[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                BY RemDef, Zenon DEF KeyInBktAtAddr
              <7>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <7>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2, <7>4
            <6>14. CASE pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
              <7> USE <6>14
              <7> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = NULL
                BY RemDef, Zenon
              <7>1. q # p
                BY RemDef, Zenon
              <7>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                BY <7>1
              <7>3. pc'[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                BY RemDef, Zenon DEF KeyInBktAtAddr
              <7>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                BY <7>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2, <7>4
            <6>15. CASE pc[q] = "R5"
              <7> USE <6>15
              <7> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
                BY RemDef, Zenon
              <7>1. q # p
                BY RemDef, Zenon
              <7>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                BY <7>1
              <7>3. pc'[q] = "R5"
                BY RemDef, Zenon
              <7>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY <7>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2, <7>4
            <6> QED
              BY RemDef, ZenonT(120),
                 <6>1, <6>2, <6>3, <6>4, <6>5, <6>6, <6>7, <6>8, <6>9, 
                 <6>10, <6>11, <6>12, <6>13, <6>14, <6>15
              DEF LineIDs
          <5> QED
            BY <4>1, <5>1, <5>2, Zenon DEF S
        <4>3. c_pred \in P
          BY <4>2 DEF InvL1
        <4>4. c_pred \in Evolve(P)
          BY <4>1, <4>3, EmptySeqEvolve
        <4>5. c_pred.res[p] = ret'[p]
          BY Zenon DEF ConfigDomain
        <4>6. c.op[p] = BOT /\ c.arg[p] = BOT /\ c.res[p] = BOT
          BY Zenon, SPrimeRewrite, RemDef DEF SPrime
        <4>7. c.op = [c_pred.op EXCEPT ![p] = BOT]
          BY Zenon, <4>6 DEF ConfigDomain
        <4>8. c.arg = [c_pred.arg EXCEPT ![p] = BOT]
          BY Zenon, <4>6 DEF ConfigDomain
        <4>9. c.res = [c_pred.res EXCEPT ![p] = BOT]
          BY Zenon, <4>6 DEF ConfigDomain
        <4>10. c.state = c_pred.state
          OBVIOUS
        <4>11. c \in Filter(Evolve(P), p, ret'[p])
          BY <4>4, <4>5, <4>7, <4>8, <4>9, <4>10, Zenon DEF Filter
        <4> QED
          BY <4>11
      <3>3. CASE Line = U5(p)
        <4> USE <3>3 DEF U5
        <4> SUFFICES ASSUME NEW c \in ConfigDomain,
                            c \in S'
                     PROVE  c \in P'
          BY Zenon DEF InvL1, S
        <4> DEFINE c_pred == [state |-> c.state,
                              op    |-> [c.op EXCEPT ![p] = "Upsert"],
                              arg   |-> [c.arg EXCEPT ![p] = arg[p]],
                              res   |-> [c.res EXCEPT ![p] = r[p]]]
        <4>1. c_pred \in ConfigDomain
          <5>1. c_pred.state \in StateDomain
            BY DEF ConfigDomain
          <5>2. c_pred.op \in [ProcSet -> OpDomain]
            BY DEF ConfigDomain, OpDomain
          <5>3. c_pred.arg \in [ProcSet -> ArgDomain]
            BY DEF ConfigDomain, ArgDomain
          <5>4. c_pred.res \in [ProcSet -> ResDomain]
            BY DEF ConfigDomain, ResDomain
          <5> QED
            BY <5>1, <5>2, <5>3, <5>4 DEF ConfigDomain
        <4>2. c_pred \in S
          <5>1. c_pred.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL]
            <6>1. c_pred.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]])' THEN ValOfKeyInBktAtAddr(k, A[Hash[k]])' ELSE NULL]
              BY Zenon, SPrimeRewrite DEF SPrime
            <6>2. \A k \in KeyDomain : KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
              BY Zenon DEF KeyInBktAtAddr
            <6>3. \A k \in KeyDomain : ValOfKeyInBktAtAddr(k, A[Hash[k]])' = ValOfKeyInBktAtAddr(k, A[Hash[k]])
              <7> SUFFICES ASSUME NEW k \in KeyDomain
                           PROVE  ValOfKeyInBktAtAddr(k, A[Hash[k]])' = ValOfKeyInBktAtAddr(k, A[Hash[k]])
                OBVIOUS
              <7> bkt_arr == MemLocs'[A'[Hash[k]]]
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
              <7>1. ValOfKeyInBktAtAddr(k, A[Hash[k]])' = bkt_arr[idx].val
                BY DEF ValOfKeyInBktAtAddr
              <7>2. bkt_arr = MemLocs[A[Hash[k]]]
                BY Zenon
              <7> QED
                BY <7>1, <7>2, ZenonT(30) DEF ValOfKeyInBktAtAddr
            <6> QED
              BY <6>1, <6>2, <6>3
          <5>2. ASSUME NEW q \in ProcSet
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
            <6> USE <5>2
            <6>1. CASE pc[q] = RemainderID
              <7> SUFFICES c_pred.op[q] = BOT /\ c_pred.arg[q] = BOT /\ c_pred.res[q] = BOT
                BY <6>1, RemDef, Zenon
              <7>1. q # p
                BY <6>1, RemDef, Zenon
              <7>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                BY <7>1
              <7>3. pc'[q] = RemainderID
                BY <6>1, RemDef, Zenon
              <7>4. c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
                BY <7>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2, <7>4
            <6>2. CASE pc[q] = "F1"
              <7> USE <6>2
              <7> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
                BY RemDef, Zenon
              <7>1. q # p
                BY RemDef, Zenon
              <7>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                BY <7>1
              <7>3. pc'[q] = "F1"
                BY RemDef, Zenon
              <7>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <7>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2, <7>4
            <6>3. CASE pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
              <7> USE <6>3
              <7> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                BY RemDef, Zenon
              <7>1. q # p
                BY RemDef, Zenon
              <7>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                BY <7>1
              <7>3. pc'[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                BY RemDef, Zenon DEF KeyInBktAtAddr
              <7>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
                BY <7>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                <8> DEFINE bkt_arr == MemLocs'[bucket'[q]]
                <8> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg'[q].key
                <8>1. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = bkt_arr[idx].val
                  BY Zenon DEF ValOfKeyInBktAtAddr
                <8>2. bkt_arr = MemLocs[bucket[q]]
                  BY Zenon
                <8>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
                  BY Zenon
                <8> QED
                  BY <8>1, <8>2, <8>3, Isa DEF ValOfKeyInBktAtAddr
              <7> QED
                BY <7>2, <7>4, <7>5
            <6>4. CASE pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
              <7> USE <6>4
              <7> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = NULL
                BY RemDef, Zenon
              <7>1. q # p
                BY RemDef, Zenon
              <7>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                BY <7>1
              <7>3. pc'[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                BY RemDef, Zenon DEF KeyInBktAtAddr
              <7>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                BY <7>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2, <7>4
            <6>5. CASE pc[q] = "F3"
              <7> USE <6>5
              <7> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
                BY <6>5, RemDef, Zenon
              <7>1. q # p
                BY RemDef, Zenon
              <7>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                BY <7>1
              <7>3. pc'[q] = "F3"
                BY <6>5, RemDef, Zenon
              <7>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY <7>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2, <7>4
            <6>6. CASE pc[q] \in {"I1", "I3", "I4"}
              <7> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
                BY <6>6, RemDef, Zenon
              <7>1. q # p
                BY <6>6, RemDef, Zenon
              <7>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                BY <7>1
              <7>3. pc'[q] \in {"I1", "I3", "I4"}
                BY <6>6, RemDef, Zenon
              <7>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <7>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2, <7>4
            <6>7. CASE pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
              <7> USE <6>7
              <7> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                BY RemDef, Zenon
              <7>1. q # p
                BY RemDef, Zenon
              <7>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                BY <7>1
              <7>3. pc'[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                BY RemDef, Zenon DEF KeyInBktAtAddr
              <7>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
                BY <7>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                <8> DEFINE bkt_arr == MemLocs'[bucket'[q]]
                <8> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg'[q].key
                <8>1. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = bkt_arr[idx].val
                  BY Zenon DEF ValOfKeyInBktAtAddr
                <8>2. bkt_arr = MemLocs[bucket[q]]
                  BY Zenon
                <8>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
                  BY Zenon
                <8> QED
                  BY <8>1, <8>2, <8>3, Isa DEF ValOfKeyInBktAtAddr
              <7> QED
                BY <7>2, <7>4, <7>5
            <6>8. CASE pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
              <7> USE <6>8
              <7> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
                BY RemDef, Zenon
              <7>1. q # p
                BY RemDef, Zenon
              <7>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                BY <7>1
              <7>3. pc'[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                BY RemDef, Zenon DEF KeyInBktAtAddr
              <7>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <7>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2, <7>4
            <6>9. CASE pc[q] = "I5"
              <7> USE <6>9
              <7> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
                BY <6>9, RemDef, Zenon
              <7>1. q # p
                BY RemDef, Zenon
              <7>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                BY <7>1
              <7>3. pc'[q] = "I5"
                BY <6>9, RemDef, Zenon
              <7>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY <7>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2, <7>4
            <6>10. CASE pc[q] \in {"U1", "U2", "U3", "U4"}
              <7> USE <6>10
              <7> SUFFICES c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
                BY RemDef, Zenon
              <7>1. q # p
                BY RemDef, Zenon
              <7>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                BY <7>1
              <7>3. pc'[q] \in {"U1", "U2", "U3", "U4"}
                BY RemDef, Zenon
              <7>4. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <7>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2, <7>4
            <6>11. CASE pc[q] = "U5"
              <7> USE <6>11
              <7> SUFFICES c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
                BY RemDef, Zenon
              <7>1. CASE q = p
                BY <7>1 DEF ConfigDomain
              <7> SUFFICES ASSUME q # p
                           PROVE  c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
                BY <7>1
              <7>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                OBVIOUS
              <7>3. pc'[q] = "U5"
                BY RemDef, Zenon
              <7>4. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY <7>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2, <7>4
            <6>12. CASE pc[q] \in {"R1", "R3", "R4"}
              <7> USE <6>12
              <7> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
                BY RemDef, Zenon
              <7>1. q # p
                BY RemDef, Zenon
              <7>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                BY <7>1
              <7>3. pc'[q] \in {"R1", "R3", "R4"}
                BY RemDef, Zenon
              <7>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <7>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2, <7>4
            <6>13. CASE pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
              <7> USE <6>13
              <7> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
                BY RemDef, Zenon
              <7>1. q # p
                BY RemDef, Zenon
              <7>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                BY <7>1
              <7>3. pc'[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                BY RemDef, Zenon DEF KeyInBktAtAddr
              <7>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <7>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2, <7>4
            <6>14. CASE pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
              <7> USE <6>14
              <7> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = NULL
                BY RemDef, Zenon
              <7>1. q # p
                BY RemDef, Zenon
              <7>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                BY <7>1
              <7>3. pc'[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                BY RemDef, Zenon DEF KeyInBktAtAddr
              <7>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                BY <7>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2, <7>4
            <6>15. CASE pc[q] = "R5"
              <7> USE <6>15
              <7> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
                BY RemDef, Zenon
              <7>1. q # p
                BY RemDef, Zenon
              <7>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                BY <7>1
              <7>3. pc'[q] = "R5"
                BY RemDef, Zenon
              <7>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY <7>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2, <7>4
            <6> QED
              BY RemDef, ZenonT(120),
                 <6>1, <6>2, <6>3, <6>4, <6>5, <6>6, <6>7, <6>8, <6>9, 
                 <6>10, <6>11, <6>12, <6>13, <6>14, <6>15
              DEF LineIDs
          <5> QED
            BY <4>1, <5>1, <5>2, Zenon DEF S
        <4>3. c_pred \in P
          BY <4>2 DEF InvL1
        <4>4. c_pred \in Evolve(P)
          BY <4>1, <4>3, EmptySeqEvolve
        <4>5. c_pred.res[p] = ret'[p]
          BY Zenon DEF ConfigDomain
        <4>6. c.op[p] = BOT /\ c.arg[p] = BOT /\ c.res[p] = BOT
          BY Zenon, SPrimeRewrite, RemDef DEF SPrime
        <4>7. c.op = [c_pred.op EXCEPT ![p] = BOT]
          BY Zenon, <4>6 DEF ConfigDomain
        <4>8. c.arg = [c_pred.arg EXCEPT ![p] = BOT]
          BY Zenon, <4>6 DEF ConfigDomain
        <4>9. c.res = [c_pred.res EXCEPT ![p] = BOT]
          BY Zenon, <4>6 DEF ConfigDomain
        <4>10. c.state = c_pred.state
          OBVIOUS
        <4>11. c \in Filter(Evolve(P), p, ret'[p])
          BY <4>4, <4>5, <4>7, <4>8, <4>9, <4>10, Zenon DEF Filter
        <4> QED
          BY <4>11
      <3>4. CASE Line = R5(p) 
        <4> USE <3>4 DEF R5
        <4> SUFFICES ASSUME NEW c \in ConfigDomain,
                            c \in S'
                     PROVE  c \in P'
          BY Zenon DEF InvL1, S
        <4> DEFINE c_pred == [state |-> c.state,
                              op    |-> [c.op EXCEPT ![p] = "Remove"],
                              arg   |-> [c.arg EXCEPT ![p] = arg[p]],
                              res   |-> [c.res EXCEPT ![p] = r[p]]]
        <4>1. c_pred \in ConfigDomain
          <5>1. c_pred.state \in StateDomain
            BY DEF ConfigDomain
          <5>2. c_pred.op \in [ProcSet -> OpDomain]
            BY DEF ConfigDomain, OpDomain
          <5>3. c_pred.arg \in [ProcSet -> ArgDomain]
            BY DEF ConfigDomain, ArgDomain
          <5>4. c_pred.res \in [ProcSet -> ResDomain]
            BY DEF ConfigDomain, ResDomain
          <5> QED
            BY <5>1, <5>2, <5>3, <5>4 DEF ConfigDomain
        <4>2. c_pred \in S
          <5>1. c_pred.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]]) THEN ValOfKeyInBktAtAddr(k, A[Hash[k]]) ELSE NULL]
            <6>1. c_pred.state = [k \in KeyDomain |-> IF KeyInBktAtAddr(k, A[Hash[k]])' THEN ValOfKeyInBktAtAddr(k, A[Hash[k]])' ELSE NULL]
              BY Zenon, SPrimeRewrite DEF SPrime
            <6>2. \A k \in KeyDomain : KeyInBktAtAddr(k, A[Hash[k]]) = KeyInBktAtAddr(k, A[Hash[k]])'
              BY Zenon DEF KeyInBktAtAddr
            <6>3. \A k \in KeyDomain : ValOfKeyInBktAtAddr(k, A[Hash[k]])' = ValOfKeyInBktAtAddr(k, A[Hash[k]])
              <7> SUFFICES ASSUME NEW k \in KeyDomain
                           PROVE  ValOfKeyInBktAtAddr(k, A[Hash[k]])' = ValOfKeyInBktAtAddr(k, A[Hash[k]])
                OBVIOUS
              <7> bkt_arr == MemLocs'[A'[Hash[k]]]
              <7> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
              <7>1. ValOfKeyInBktAtAddr(k, A[Hash[k]])' = bkt_arr[idx].val
                BY DEF ValOfKeyInBktAtAddr
              <7>2. bkt_arr = MemLocs[A[Hash[k]]]
                BY Zenon
              <7> QED
                BY <7>1, <7>2, ZenonT(30) DEF ValOfKeyInBktAtAddr
            <6> QED
              BY <6>1, <6>2, <6>3
          <5>2. ASSUME NEW q \in ProcSet
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
            <6> USE <5>2
            <6>1. CASE pc[q] = RemainderID
              <7> SUFFICES c_pred.op[q] = BOT /\ c_pred.arg[q] = BOT /\ c_pred.res[q] = BOT
                BY <6>1, RemDef, Zenon
              <7>1. q # p
                BY <6>1, RemDef, Zenon
              <7>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                BY <7>1
              <7>3. pc'[q] = RemainderID
                BY <6>1, RemDef, Zenon
              <7>4. c.op[q] = BOT /\ c.arg[q] = BOT /\ c.res[q] = BOT
                BY <7>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2, <7>4
            <6>2. CASE pc[q] = "F1"
              <7> USE <6>2
              <7> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
                BY RemDef, Zenon
              <7>1. q # p
                BY RemDef, Zenon
              <7>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                BY <7>1
              <7>3. pc'[q] = "F1"
                BY RemDef, Zenon
              <7>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <7>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2, <7>4
            <6>3. CASE pc[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
              <7> USE <6>3
              <7> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                BY RemDef, Zenon
              <7>1. q # p
                BY RemDef, Zenon
              <7>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                BY <7>1
              <7>3. pc'[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                BY RemDef, Zenon DEF KeyInBktAtAddr
              <7>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
                BY <7>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                <8> DEFINE bkt_arr == MemLocs'[bucket'[q]]
                <8> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg'[q].key
                <8>1. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = bkt_arr[idx].val
                  BY Zenon DEF ValOfKeyInBktAtAddr
                <8>2. bkt_arr = MemLocs[bucket[q]]
                  BY Zenon
                <8>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
                  BY Zenon
                <8> QED
                  BY <8>1, <8>2, <8>3, Isa DEF ValOfKeyInBktAtAddr
              <7> QED
                BY <7>2, <7>4, <7>5
            <6>4. CASE pc[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
              <7> USE <6>4
              <7> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = NULL
                BY RemDef, Zenon
              <7>1. q # p
                BY RemDef, Zenon
              <7>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                BY <7>1
              <7>3. pc'[q] = "F2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                BY RemDef, Zenon DEF KeyInBktAtAddr
              <7>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                BY <7>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2, <7>4
            <6>5. CASE pc[q] = "F3"
              <7> USE <6>5
              <7> SUFFICES c_pred.op[q] = "Find" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
                BY <6>5, RemDef, Zenon
              <7>1. q # p
                BY RemDef, Zenon
              <7>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                BY <7>1
              <7>3. pc'[q] = "F3"
                BY <6>5, RemDef, Zenon
              <7>4. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY <7>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2, <7>4
            <6>6. CASE pc[q] \in {"I1", "I3", "I4"}
              <7> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
                BY <6>6, RemDef, Zenon
              <7>1. q # p
                BY <6>6, RemDef, Zenon
              <7>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                BY <7>1
              <7>3. pc'[q] \in {"I1", "I3", "I4"}
                BY <6>6, RemDef, Zenon
              <7>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <7>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2, <7>4
            <6>7. CASE pc[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
              <7> USE <6>7
              <7> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                BY RemDef, Zenon
              <7>1. q # p
                BY RemDef, Zenon
              <7>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                BY <7>1
              <7>3. pc'[q] = "I2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                BY RemDef, Zenon DEF KeyInBktAtAddr
              <7>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
                BY <7>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7>5. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
                <8> DEFINE bkt_arr == MemLocs'[bucket'[q]]
                <8> DEFINE idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg'[q].key
                <8>1. ValOfKeyInBktAtAddr(arg[q].key, bucket[q])' = bkt_arr[idx].val
                  BY Zenon DEF ValOfKeyInBktAtAddr
                <8>2. bkt_arr = MemLocs[bucket[q]]
                  BY Zenon
                <8>3. idx = CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = arg[q].key
                  BY Zenon
                <8> QED
                  BY <8>1, <8>2, <8>3, Isa DEF ValOfKeyInBktAtAddr
              <7> QED
                BY <7>2, <7>4, <7>5
            <6>8. CASE pc[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
              <7> USE <6>8
              <7> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
                BY RemDef, Zenon
              <7>1. q # p
                BY RemDef, Zenon
              <7>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                BY <7>1
              <7>3. pc'[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                BY RemDef, Zenon DEF KeyInBktAtAddr
              <7>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <7>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2, <7>4
            <6>9. CASE pc[q] = "I5"
              <7> USE <6>9
              <7> SUFFICES c_pred.op[q] = "Insert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
                BY <6>9, RemDef, Zenon
              <7>1. q # p
                BY RemDef, Zenon
              <7>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                BY <7>1
              <7>3. pc'[q] = "I5"
                BY <6>9, RemDef, Zenon
              <7>4. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY <7>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2, <7>4
            <6>10. CASE pc[q] \in {"U1", "U2", "U3", "U4"}
              <7> USE <6>10
              <7> SUFFICES c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
                BY RemDef, Zenon
              <7>1. q # p
                BY RemDef, Zenon
              <7>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                BY <7>1
              <7>3. pc'[q] \in {"U1", "U2", "U3", "U4"}
                BY RemDef, Zenon
              <7>4. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <7>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2, <7>4
            <6>11. CASE pc[q] = "U5"
              <7> USE <6>11
              <7> SUFFICES c_pred.op[q] = "Upsert" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
                BY RemDef, Zenon
              <7>1. q # p
                BY Zenon
              <7>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                BY <7>1
              <7>3. pc'[q] = "U5"
                BY RemDef, Zenon
              <7>4. c.op[q] = "Upsert" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY <7>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2, <7>4
            <6>12. CASE pc[q] \in {"R1", "R3", "R4"}
              <7> USE <6>12
              <7> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
                BY RemDef, Zenon
              <7>1. q # p
                BY RemDef, Zenon
              <7>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                BY <7>1
              <7>3. pc'[q] \in {"R1", "R3", "R4"}
                BY RemDef, Zenon
              <7>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <7>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2, <7>4
            <6>13. CASE pc[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])
              <7> USE <6>13
              <7> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = BOT
                BY RemDef, Zenon
              <7>1. q # p
                BY RemDef, Zenon
              <7>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                BY <7>1
              <7>3. pc'[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
                BY RemDef, Zenon DEF KeyInBktAtAddr
              <7>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
                BY <7>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2, <7>4
            <6>14. CASE pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
              <7> USE <6>14
              <7> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = NULL
                BY RemDef, Zenon
              <7>1. q # p
                BY RemDef, Zenon
              <7>2. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                BY <7>1
              <7>3. pc'[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
                BY RemDef, Zenon DEF KeyInBktAtAddr
              <7>4. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
                BY <7>3, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>2, <7>4
            <6>15. CASE pc[q] = "R5"
              <7> USE <6>15
              <7> SUFFICES c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
                BY RemDef, Zenon
              <7>1. CASE q = p 
                BY <7>1 DEF ConfigDomain
              <7> SUFFICES ASSUME q # p
                           PROVE  c_pred.op[q] = "Remove" /\ c_pred.arg[q] = arg[q] /\ c_pred.res[q] = r[q]
                BY <7>1
              <7>2. q # p
                OBVIOUS
              <7>3. c_pred.op[q] = c.op[q] /\ c_pred.arg[q] = c.arg[q] /\ c_pred.res[q] = c.res[q]
                OBVIOUS
              <7>4. pc'[q] = "R5"
                BY RemDef, Zenon
              <7>5. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = r[q]
                BY <7>4, SPrimeRewrite, Zenon, RemDef DEF SPrime
              <7> QED
                BY <7>3, <7>5
            <6> QED
              BY RemDef, ZenonT(120),
                 <6>1, <6>2, <6>3, <6>4, <6>5, <6>6, <6>7, <6>8, <6>9, 
                 <6>10, <6>11, <6>12, <6>13, <6>14, <6>15
              DEF LineIDs
          <5> QED
            BY <4>1, <5>1, <5>2, Zenon DEF S
        <4>3. c_pred \in P
          BY <4>2 DEF InvL1
        <4>4. c_pred \in Evolve(P)
          BY <4>1, <4>3, EmptySeqEvolve
        <4>5. c_pred.res[p] = ret'[p]
          BY Zenon DEF ConfigDomain
        <4>6. c.op[p] = BOT /\ c.arg[p] = BOT /\ c.res[p] = BOT
          BY Zenon, SPrimeRewrite, RemDef DEF SPrime
        <4>7. c.op = [c_pred.op EXCEPT ![p] = BOT]
          BY Zenon, <4>6 DEF ConfigDomain
        <4>8. c.arg = [c_pred.arg EXCEPT ![p] = BOT]
          BY Zenon, <4>6 DEF ConfigDomain
        <4>9. c.res = [c_pred.res EXCEPT ![p] = BOT]
          BY Zenon, <4>6 DEF ConfigDomain
        <4>10. c.state = c_pred.state
          OBVIOUS
        <4>11. c \in Filter(Evolve(P), p, ret'[p])
          BY <4>4, <4>5, <4>7, <4>8, <4>9, <4>10, Zenon DEF Filter
        <4> QED
          BY <4>11
      <3> QED
        BY Zenon, <3>1, <3>2, <3>3, <3>4 DEF RetLines
    <2> QED
      BY <1>1, <2>1, <2>2, <2>3
  <1>2. CASE UNCHANGED vars
    <2> UNCHANGED <<A, MemLocs, AllocAddrs, bucket, newbkt, r, pc, arg, ret, P>>
      BY <1>2 DEF vars, algvars
    <2> SUFFICES ASSUME NEW c \in ConfigDomain,
                        c \in S'
                 PROVE  c \in P'
      BY Zenon DEF InvL1, S
    <2>1. c \in S
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
          <5>2. pc'[q] = "F2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>3. c.op[q] = "Find" /\ c.arg[q] = arg[q] /\ c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])'
            BY <5>2,  SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5>4. arg[q].key = arg'[q].key /\ arg[q].key \in KeyDomain
            BY Zenon, RemDef DEF ArgsOf, LineIDtoOp
          <5>5. c.res[q] = ValOfKeyInBktAtAddr(arg[q].key, bucket[q])
            BY <5>3, <5>4, <4>B
          <5> QED
            BY <5>3, <5>5
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
          <5>1. pc'[q] = "I2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>2. c.op[q] = "Insert" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>1, SPrimeRewrite, Zenon, RemDef DEF SPrime
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
          <5>2. pc'[q] = "R2" /\ KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>3. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = BOT
            BY <5>2, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>3
        <4>14. CASE pc[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])
          <5> USE <4>14
          <5> SUFFICES c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
            BY RemDef, Zenon
          <5>2. pc'[q] = "R2" /\ ~KeyInBktAtAddr(arg[q].key, bucket[q])'
            BY RemDef, Zenon DEF KeyInBktAtAddr
          <5>3. c.op[q] = "Remove" /\ c.arg[q] = arg[q] /\ c.res[q] = NULL
            BY <5>2, SPrimeRewrite, Zenon, RemDef DEF SPrime
          <5> QED
            BY <5>3
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
      BY <2>1 DEF InvL1
  <1> QED
    BY <1>1, <1>2

===========================================================================
\* Modification History
\* Last modified Thu Aug 08 11:43:33 EDT 2024 by uguryavuz
\* Created Thu Aug 08 09:43:24 EDT 2024 by uguryavuz
