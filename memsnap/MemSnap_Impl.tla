----------------------------- MODULE MemSnap_Impl -----------------------------
EXTENDS   Cptable_Type
CONSTANT  RemainderID
VARIABLES A, B, X, a, b, x, k, r, arg, ret, pc
algvars == <<A, B, X, a, b, x, k, r>>

C1(p)  == /\ pc[p] = "C1"
          /\ p = Scanner
          /\ X' = X + 1
          /\ pc' = [pc EXCEPT ![p] = "C2"]
          /\ UNCHANGED <<A, B, a, b, x, k, r, arg, ret>>

C2(p)  == /\ pc[p] = "C2"
          /\ p = Scanner
          /\ pc' = [pc EXCEPT ![p] = RemainderID]
          /\ UNCHANGED <<A, B, X, a, b, x, k, r, arg>>
          /\ ret' = [ret EXCEPT ![p] = ACK]

O1A(p) == /\ pc[p] = "O1A"
          /\ p = Scanner
          /\ IF k[p] > 2
                THEN /\ k' = [k EXCEPT ![p] = 1]
                     /\ pc' = [pc EXCEPT ![p] = "O2"]
                     /\ b' = b
                ELSE /\ k' = k
                     /\ pc' = [pc EXCEPT ![p] = "O1B"]
                     /\ b' = [b EXCEPT ![p] = B[arg[p].i]]
          /\ UNCHANGED <<A, B, X, a, x, r, arg, ret>>

O1B(p) == /\ pc[p] = "O1B"
          /\ p = Scanner
          /\ x' = [x EXCEPT ![p] = X]
          /\ IF b[p].seq = x[p]
                THEN /\ k' = [k EXCEPT ![p] = 1]
                     /\ pc' = [pc EXCEPT ![p] = "O2"]
                ELSE /\ k' = k
                     /\ pc' = [pc EXCEPT ![p] = "O1C"]
          /\ UNCHANGED <<A, B, X, a, b, r, arg, ret>>

O1C(p) == /\ pc[p] = "O1C"
          /\ p = Scanner
          /\ a' = [a EXCEPT ![p] = A[arg[p].i]]
          /\ pc' = [pc EXCEPT ![p] = "O1D"]
          /\ UNCHANGED <<A, B, X, b, x, k, r, arg, ret>>
          
O1D(p) == /\ pc[p] = "O1D"
          /\ p = Scanner
          /\ IF B[arg[p].i] = b[p]
                THEN /\ k' = [k EXCEPT ![p] = 1]
                     /\ B' = [B EXCEPT ![arg[p].i] = [val |-> a[p], 
                                                      seq |-> x[p]]]
                     /\ pc' = [pc EXCEPT ![p] = "O2"]
                ELSE /\ k' = [k EXCEPT ![p] = k[p]+1]
                     /\ B' = B
                     /\ pc' = [pc EXCEPT ![p] = "O1A"]
          /\ UNCHANGED <<A, X, a, b, x, r, arg, ret>>

O2(p)  == /\ pc[p] = "O2"
          /\ p = Scanner
          /\ r' = [r EXCEPT ![p] = B[arg[p].i].val]
          /\ pc' = [pc EXCEPT ![p] = "O3"]
          /\ UNCHANGED <<A, B, X, a, b, x, k, arg, ret>>

O3(p)  == /\ pc[p] = "O3"
          /\ p = Scanner
          /\ pc' = [pc EXCEPT ![p] = RemainderID]
          /\ ret' = [ret EXCEPT ![p] = r[p]]
          /\ UNCHANGED <<A, B, X, a, b, x, k, r, arg>>

U1A(p) == /\ pc[p] = "U1A"
          /\ p \in UpdSet
          /\ IF k[p] > 2
                THEN /\ k' = [k EXCEPT ![p] = 1]
                     /\ pc' = [pc EXCEPT ![p] = "U2"]
                     /\ b' = b
                ELSE /\ k' = k
                     /\ pc' = [pc EXCEPT ![p] = "U1B"]
                     /\ b' = [b EXCEPT ![p] = B[arg[p].i]]
          /\ UNCHANGED <<A, B, X, a, x, r, arg, ret>>

U1B(p) == /\ pc[p] = "U1B"
          /\ p \in UpdSet
          /\ x' = [x EXCEPT ![p] = X]
          /\ IF b[p].seq = x[p]
                THEN /\ k' = [k EXCEPT ![p] = 1]
                     /\ pc' = [pc EXCEPT ![p] = "U2"]
                ELSE /\ k' = k
                     /\ pc' = [pc EXCEPT ![p] = "U1C"]
          /\ UNCHANGED <<A, B, X, a, b, r, arg, ret>>

U1C(p) == /\ pc[p] = "U1C"
          /\ p \in UpdSet
          /\ a' = [a EXCEPT ![p] = A[arg[p].i]]
          /\ pc' = [pc EXCEPT ![p] = "U1D"]
          /\ UNCHANGED <<A, B, X, b, x, k, r, arg, ret>>

U1D(p) == /\ pc[p] = "U1D"
          /\ p \in UpdSet
          /\ IF B[arg[p].i] = b[p]
                THEN /\ k' = [k EXCEPT ![p] = 1]
                     /\ B' = [B EXCEPT ![arg[p].i] = [val |-> a[p], 
                                                      seq |-> x[p]]]
                     /\ pc' = [pc EXCEPT ![p] = "U2"]
                ELSE /\ k' = [k EXCEPT ![p] = k[p]+1]
                     /\ B' = B
                     /\ pc' = [pc EXCEPT ![p] = "U1A"]
          /\ UNCHANGED <<A, X, a, b, x, r, arg, ret>>

U2(p)  == /\ pc[p] = "U2"
          /\ p \in UpdSet
          /\ A' = [A EXCEPT ![arg[p].i] = arg[p].uop[A[arg[p].i]][1]]
          /\ r' = [r EXCEPT ![p] = arg[p].uop[A[arg[p].i]][2]]
          /\ pc' = [pc EXCEPT ![p] = "U3"]
          /\ UNCHANGED <<B, X, a, b, x, k, arg, ret>>

U3(p)  == /\ pc[p] = "U3"
          /\ p \in UpdSet
          /\ pc' = [pc EXCEPT ![p] = RemainderID]
          /\ ret' = [ret EXCEPT ![p] = r[p]]
          /\ UNCHANGED <<A, B, X, a, b, x, k, r, arg>>

\* Initial configuration
InitState == CHOOSE state \in StateDomain : state.val = state.snap

Init == /\ pc = [p \in ProcSet |-> RemainderID]
        /\ A = InitState.val
        /\ B = [i \in 1..M |-> [val |-> InitState.val[i], seq |-> 0]]
        /\ X = 0
        /\ a \in [ProcSet -> WordDomain]
        /\ b \in [ProcSet -> [val: WordDomain, seq: Nat]]
        /\ x \in [ProcSet -> Nat]
        /\ k \in [ProcSet -> 1..3]
        /\ r \in [ProcSet -> WordDomain \union UOpRetDomain]
        /\ arg \in [ProcSet -> ArgDomain]
        /\ ret \in [ProcSet -> ResDomain]

\* Invocation lines
OpToInvocLine(op) == CASE op = "Click"   -> "C1"
                       [] op = "Observe" -> "O1A"
                       [] op = "Update"  -> "U1A"
                       
LineIDtoOp(id) == CASE id \in {"C1", "C2"} -> "Click"
                    [] id \in {"O1A", "O1B", "O1C", "O1D", "O2", "O3"} -> "Observe"
                    [] id \in {"U1A", "U1B", "U1C", "U1D", "U2", "U3"} -> "Update"

LineIDs == {RemainderID,
            "C1", "C2",
            "O1A", "O1B", "O1C", "O1D", "O2", "O3",
            "U1A", "U1B", "U1C", "U1D", "U2", "U3"}

IntLines(p) == {C1(p), 
                O1A(p), O1B(p), O1C(p), O1D(p), O2(p),
                U1A(p), U1B(p), U1C(p), U1D(p), U2(p)}

RetLines(p) == {C2(p), O3(p), U3(p)}

===============================================================================
\* Modification History
\* Last modified Wed Aug 14 09:40:17 EDT 2024 by uguryavuz
\* Created Wed Mar 13 17:52:43 EDT 2024 by uguryavuz