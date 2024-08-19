----------------------------- MODULE PHash_Impl -----------------------------
EXTENDS   UnorderedMap_Type, Integers, Sequences, FiniteSets
CONSTANT  RemainderID, Hash, Addrs, N
VARIABLES pc, A, MemLocs, AllocAddrs, bucket, newbkt, r, arg, ret
vars == <<pc, A, MemLocs, AllocAddrs, bucket, newbkt, r, arg, ret>>

KeyInBktAtAddr(k, addr) ==
  LET
    bkt_arr == MemLocs[addr]
  IN
    /\ addr # NULL
    /\ \E index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
    
IdxInBktAtAddr(k, addr) ==
  LET
    bkt_arr == MemLocs[addr]
  IN
    CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
                
ValOfKeyInBktAtAddr(k, addr) ==
  LET 
    bkt_arr == MemLocs[addr]
    idx == CHOOSE index \in 1..Len(bkt_arr) : bkt_arr[index].key = k
  IN
    bkt_arr[idx].val

F1(p) == /\ pc[p] = "F1"
         /\ bucket' = [bucket EXCEPT ![p] = A[Hash[arg[p].key]]]
         /\ pc' = [pc EXCEPT ![p] = "F2"]
         /\ UNCHANGED <<A, MemLocs, AllocAddrs, newbkt, r, arg, ret>>

F2(p) == /\ pc[p] = "F2"
         /\ IF KeyInBktAtAddr(arg[p].key, bucket[p]) 
               THEN r' = [r EXCEPT ![p] = ValOfKeyInBktAtAddr(arg[p].key, bucket[p])]
               ELSE r' = [r EXCEPT ![p] = NULL]
         /\ pc' = [pc EXCEPT ![p] = "F3"]
         /\ UNCHANGED <<A, MemLocs, AllocAddrs, bucket, newbkt, arg, ret>>

F3(p) == /\ pc[p] = "F3"
         /\ pc' = [pc EXCEPT ![p] = RemainderID]
         /\ UNCHANGED <<A, MemLocs, AllocAddrs, bucket, newbkt, r, arg>>
         /\ ret' = [ret EXCEPT ![p] = r[p]]

I1(p) == /\ pc[p] = "I1"
         /\ bucket' = [bucket EXCEPT ![p] = A[Hash[arg[p].key]]]
         /\ pc' = [pc EXCEPT ![p] = "I2"]
         /\ UNCHANGED <<A, MemLocs, AllocAddrs, newbkt, r, arg, ret>>

I2(p) == /\ pc[p] = "I2"
         /\ IF KeyInBktAtAddr(arg[p].key, bucket[p]) 
               THEN /\ r' = [r EXCEPT ![p] = ValOfKeyInBktAtAddr(arg[p].key, bucket[p])]
                    /\ pc' = [pc EXCEPT ![p] = "I5"]
               ELSE /\ r' = [r EXCEPT ![p] = NULL]
                    /\ pc' = [pc EXCEPT ![p] = "I3"]
         /\ UNCHANGED <<A, MemLocs, AllocAddrs, bucket, newbkt, arg, ret>>

I3(p) == /\ pc[p] = "I3"
         /\ \E addr \in Addrs : 
            /\ addr \notin AllocAddrs
            /\ AllocAddrs' = AllocAddrs \cup {addr}
            /\ newbkt' = [newbkt EXCEPT ![p] = addr]
            /\ IF bucket[p] = NULL
                  THEN MemLocs' = [MemLocs EXCEPT ![addr] = <<arg[p]>>]
                  ELSE MemLocs' = [MemLocs EXCEPT ![addr] = Append(MemLocs[bucket[p]], arg[p])]
         /\ pc' = [pc EXCEPT ![p] = "I4"]
         /\ UNCHANGED <<A, bucket, r, arg, ret>>

I4(p) == /\ pc[p] = "I4"
         /\ IF A[Hash[arg[p].key]] = bucket[p]
               THEN /\ A' = [A EXCEPT ![Hash[arg[p].key]] = newbkt[p]]
                    /\ pc' = [pc EXCEPT ![p] = "I5"]
               ELSE /\ A' = A
                    /\ pc' = [pc EXCEPT ![p] = "I1"]
         /\ UNCHANGED <<MemLocs, AllocAddrs, bucket, newbkt, r, arg, ret>>

I5(p) == /\ pc[p] = "I5"
         /\ pc' = [pc EXCEPT ![p] = RemainderID]
         /\ UNCHANGED <<A, MemLocs, AllocAddrs, bucket, newbkt, r, arg>>
         /\ ret' = [ret EXCEPT ![p] = r[p]]

U1(p) == /\ pc[p] = "U1"
         /\ bucket' = [bucket EXCEPT ![p] = A[Hash[arg[p].key]]]
         /\ pc' = [pc EXCEPT ![p] = "U2"]
         /\ UNCHANGED <<A, MemLocs, AllocAddrs, newbkt, r, arg, ret>>

U2(p) == /\ pc[p] = "U2"
         /\ IF KeyInBktAtAddr(arg[p].key, bucket[p]) 
               THEN r' = [r EXCEPT ![p] = ValOfKeyInBktAtAddr(arg[p].key, bucket[p])]
               ELSE r' = [r EXCEPT ![p] = NULL]
         /\ pc' = [pc EXCEPT ![p] = "U3"]
         /\ UNCHANGED <<A, MemLocs, AllocAddrs, bucket, newbkt, arg, ret>>

U3(p) == /\ pc[p] = "U3"
         /\ \E addr \in Addrs : 
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
         /\ pc' = [pc EXCEPT ![p] = "U4"]
         /\ UNCHANGED <<A, bucket, r, arg, ret>>

U4(p) == /\ pc[p] = "U4"
         /\ IF A[Hash[arg[p].key]] = bucket[p]
               THEN /\ A' = [A EXCEPT ![Hash[arg[p].key]] = newbkt[p]]
                    /\ pc' = [pc EXCEPT ![p] = "U5"]
               ELSE /\ A' = A
                    /\ pc' = [pc EXCEPT ![p] = "U1"]
         /\ UNCHANGED <<MemLocs, AllocAddrs, bucket, newbkt, r, arg, ret>>

U5(p) == /\ pc[p] = "U5"
         /\ pc' = [pc EXCEPT ![p] = RemainderID]
         /\ UNCHANGED <<A, MemLocs, AllocAddrs, bucket, newbkt, r, arg>>
         /\ ret' = [ret EXCEPT ![p] = r[p]]

R1(p) == /\ pc[p] = "R1"
         /\ bucket' = [bucket EXCEPT ![p] = A[Hash[arg[p].key]]]
         /\ pc' = [pc EXCEPT ![p] = "R2"]
         /\ UNCHANGED <<A, MemLocs, AllocAddrs, newbkt, r, arg, ret>>

R2(p) == /\ pc[p] = "R2"
         /\ IF KeyInBktAtAddr(arg[p].key, bucket[p]) 
               THEN /\ r' = [r EXCEPT ![p] = ValOfKeyInBktAtAddr(arg[p].key, bucket[p])]
                    /\ pc' = [pc EXCEPT ![p] = "R3"]
               ELSE /\ r' = [r EXCEPT ![p] = NULL]
                    /\ pc' = [pc EXCEPT ![p] = "R5"]
         /\ UNCHANGED <<A, MemLocs, AllocAddrs, bucket, newbkt, arg, ret>>

R3(p) == /\ pc[p] = "R3"
         /\ \E addr \in Addrs : 
            /\ addr \notin AllocAddrs
            /\ AllocAddrs' = AllocAddrs \cup {addr}
            /\ newbkt' = [newbkt EXCEPT ![p] = addr]
            /\ LET idx == IdxInBktAtAddr(arg[p].key, bucket[p])
                   bucket_arr == MemLocs[bucket[p]] IN
               MemLocs' = [MemLocs EXCEPT ![addr] = SubSeq(bucket_arr, 1, idx-1) \o SubSeq(bucket_arr, idx+1, Len(bucket_arr))]
         /\ pc' = [pc EXCEPT ![p] = "R4"]
         /\ UNCHANGED <<A, bucket, r, arg, ret>>

R4(p) == /\ pc[p] = "R4"
         /\ IF A[Hash[arg[p].key]] = bucket[p]
               THEN /\ A' = [A EXCEPT ![Hash[arg[p].key]] = newbkt[p]]
                    /\ pc' = [pc EXCEPT ![p] = "R5"]
               ELSE /\ A' = A
                    /\ pc' = [pc EXCEPT ![p] = "R1"]
         /\ UNCHANGED <<MemLocs, AllocAddrs, bucket, newbkt, r, arg, ret>>

R5(p) == /\ pc[p] = "R5"
         /\ pc' = [pc EXCEPT ![p] = RemainderID]
         /\ UNCHANGED <<A, MemLocs, AllocAddrs, bucket, newbkt, r, arg>>
         /\ ret' = [ret EXCEPT ![p] = r[p]]

\* Initial configuration
Init == /\ pc = [p \in ProcSet |-> RemainderID]
        /\ A = [idx \in 1..N |-> NULL]
        /\ MemLocs = [addr \in Addrs |-> <<>>]
        /\ AllocAddrs = {}
        /\ bucket = [p \in ProcSet |-> NULL]
        /\ newbkt = [p \in ProcSet |-> NULL]
        /\ r \in [ProcSet -> ValDomain \cup {NULL}]
        /\ arg \in [ProcSet -> ArgDomain]
        /\ ret = [p \in ProcSet |-> NULL]

OpToInvocLine(op) == CASE op = "Find"   -> "F1"
                       [] op = "Insert" -> "I1"
                       [] op = "Upsert" -> "U1"
                       [] op = "Remove" -> "R1"

LineIDtoOp(id) == CASE id \in {"F1", "F2", "F3"} -> "Find"
                    [] id \in {"I1", "I2", "I3", "I4", "I5"} -> "Insert"
                    [] id \in {"U1", "U2", "U3", "U4", "U5"} -> "Upsert"
                    [] id \in {"R1", "R2", "R3", "R4", "R5"} -> "Remove"

LineIDs == {RemainderID,
            "F1", "F2", "F3",
            "I1", "I2", "I3", "I4", "I5",
            "U1", "U2", "U3", "U4", "U5",
            "R1", "R2", "R3", "R4", "R5"}

IntLines(p) == {F1(p), F2(p), 
                I1(p), I2(p), I3(p), I4(p), 
                U1(p), U2(p), U3(p), U4(p),
                R1(p), R2(p), R3(p), R4(p)}

RetLines(p) == {F3(p), I5(p), U5(p), R5(p)}

=============================================================================
\* Modification History
\* Last modified Tue Aug 06 09:22:31 EDT 2024 by uguryavuz
\* Created Mon Jul 08 07:31:45 EST 2024 by uyavuz
