--------------------------- MODULE PHash_Proof1_HO ---------------------------
EXTENDS  PHash_Impl, SequenceTheorems, FiniteSets, TLAPS
INSTANCE Augmentation

ASSUME HashDef == Hash \in [KeyDomain -> 1..N]
ASSUME NDef    == N \in Nat \ {0}
ASSUME NULLDef == /\ NULL \notin Addrs
                  /\ NULL \notin ValDomain
ASSUME RemDef  == RemainderID = "Remainder"
                                      
InvokeLine(p) == /\ pc[p] = RemainderID
                 /\ \E op \in OpNames :
                       /\ pc' = [pc EXCEPT ![p] = OpToInvocLine(op)]
                       /\ \E new_arg \in ArgsOf(op) : arg' = [arg EXCEPT ![p] = new_arg]
                 /\ UNCHANGED <<A, MemLocs, AllocAddrs, bucket, newbkt, r, ret>>

InvocnAction == \E p \in ProcSet : InvokeLine(p)
IntermAction == \E p \in ProcSet : \E LineAction \in IntLines(p) : LineAction
ReturnAction == \E p \in ProcSet : \E LineAction \in RetLines(p) : LineAction

Next == \/ InvocnAction
        \/ IntermAction
        \/ ReturnAction
        
Spec == Init /\ [][Next]_vars

AddrsInv  == \A p \in ProcSet : pc[p] \in {"I4", "U4", "R4"}
               => /\ \A q \in ProcSet : (p # q => (newbkt[p] # bucket[q] /\ newbkt[p] # newbkt[q]))
                  /\ \A idx \in 1..N  : (A[idx] # newbkt[p])
                  /\ newbkt[p] # bucket[p]
                  /\ newbkt[p] \in AllocAddrs

BktInv    == \A p \in ProcSet : 
                  /\ pc[p] \in {"I3", "I4"} => (~KeyInBktAtAddr(arg[p].key, bucket[p]) /\ r[p] = NULL)
                  /\ pc[p] \in {"U3", "U4"} => (IF KeyInBktAtAddr(arg[p].key, bucket[p])
                                                   THEN (r[p] = ValOfKeyInBktAtAddr(arg[p].key, bucket[p]) /\ r[p] # NULL)
                                                   ELSE  r[p] = NULL)
                  /\ pc[p] \in {"R3", "R4"} => (/\ KeyInBktAtAddr(arg[p].key, bucket[p]) 
                                                /\ r[p] = ValOfKeyInBktAtAddr(arg[p].key, bucket[p]) 
                                                /\ r[p] # NULL)

NewBktInv == \A p \in ProcSet : 
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

UniqInv   == \A addr \in AllocAddrs : LET bucket_arr == MemLocs[addr] IN
                                      \A j1, j2 \in 1..Len(bucket_arr) : bucket_arr[j1].key = bucket_arr[j2].key => j1 = j2

TypeOK    == /\ pc \in [ProcSet -> LineIDs]
             /\ A \in [1..N -> AllocAddrs \union {NULL}]
             /\ MemLocs \in [Addrs -> Seq([key: KeyDomain, val: ValDomain])]
             /\ AllocAddrs \in SUBSET Addrs
             /\ bucket \in [ProcSet -> AllocAddrs \union {NULL}]
             /\ newbkt \in [ProcSet -> AllocAddrs \union {NULL}]
             /\ r \in [ProcSet -> ValDomain \union {NULL}]
             /\ arg \in [ProcSet -> ArgDomain]
             /\ ret \in [ProcSet -> RetDomain]
             /\ \A p \in ProcSet : (pc[p] # RemainderID) => arg[p] \in ArgsOf(LineIDtoOp(pc[p]))

Inv == /\ AddrsInv
       /\ BktInv
       /\ NewBktInv
       /\ UniqInv
       /\ TypeOK

THEOREM InitInv == Init => Inv

THEOREM NextInv == Inv /\ [Next]_vars => Inv'

THEOREM SpecInv == Spec => []Inv
  BY InitInv, NextInv, PTL DEF Spec

===========================================================================
\* Modification History
\* Last modified Fri Aug 16 15:07:26 EDT 2024 by uguryavuz
\* Created Thu Aug 08 09:37:36 EDT 2024 by uguryavuz
