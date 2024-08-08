--------------------------- MODULE PHash_Proof1_HO ---------------------------
EXTENDS  PHash_Impl, SequenceTheorems, FiniteSets, TLAPS
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

LEMMA NextPTypeOK == PTypeOK /\ [Next]_vars => PTypeOK'

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
  
LEMMA NextInv == Inv /\ [Next]_vars => Inv'

===========================================================================
\* Modification History
\* Last modified Thu Aug 08 09:39:50 EDT 2024 by uguryavuz
\* Created Thu Aug 08 09:37:36 EDT 2024 by uguryavuz
