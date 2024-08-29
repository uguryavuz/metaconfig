----------------------------- MODULE MemSnap_Impl -----------------------------
EXTENDS   Cptable_Type
CONSTANT  RemainderID
VARIABLES Components, X, a, b, x, k, r, arg, ret, pc
vars == <<Components, X, a, b, x, k, r, arg, ret, pc>>
(* Types:
    - Components \in 
        UNION {[AddrsSubset -> [A: ObjDomain, B: [val: ObjOpRetDomain, seq: Nat]]] : AddrsSubset \in SUBSET Addrs}
        i.e. the set of partial functions from Addrs to [A: ObjDomain, B: [val: ObjOpRetDomain, seq: Nat]]
    - X: Nat
    - a: [ProcSet -> ObjOpRetDomain]
    - b: [ProcSet -> [val: ObjOpRetDomain, seq: Nat]]
    - x: [ProcSet -> Nat]
    - k: [ProcSet -> 1..2]
    - r: [ProcSet -> ObjOpRetDomain]
    - arg: [ProcSet -> ArgDomain]
    - ret: [ProcSet -> ResDomain]
    - pc: [ProcSet -> LineIDs]
*)

C1(p)  == /\ pc[p] = "C1"
          /\ X' = X + 1
          /\ pc' = [pc EXCEPT ![p] = "C2"]
          /\ UNCHANGED <<Components, a, b, x, k, r, arg, ret>>

C2(p)  == /\ pc[p] = "C2"
          /\ pc' = [pc EXCEPT ![p] = RemainderID]
          /\ UNCHANGED <<Components, X, a, b, x, k, r, arg>>
          /\ ret' = [ret EXCEPT ![p] = ACK]

O1A(p) == /\ pc[p] = "O1A"
          /\ pc' = [pc EXCEPT ![p] = "O1B"]
          /\ b' = [b EXCEPT ![p] = Components[arg[p].c].B]
          /\ UNCHANGED <<Components, X, a, x, k, r, arg, ret>>

O1B(p) == /\ pc[p] = "O1B"
          /\ x' = [x EXCEPT ![p] = X]
          /\ IF b[p].seq = X (* Note that in the paper, this is x[p] but after the read - so here it should be X *)
                THEN /\ k' = [k EXCEPT ![p] = 1]
                     /\ pc' = [pc EXCEPT ![p] = "O2"]
                ELSE /\ k' = k
                     /\ pc' = [pc EXCEPT ![p] = "O1C"]
          /\ UNCHANGED <<Components, X, a, b, r, arg, ret>>

O1C(p) == /\ pc[p] = "O1C"
          /\ a' = [a EXCEPT ![p] = Read[Components[arg[p].c].A]]
          /\ pc' = [pc EXCEPT ![p] = "O1D"]
          /\ UNCHANGED <<Components, X, b, x, k, r, arg, ret>>
          
O1D(p) == /\ pc[p] = "O1D"
          /\ IF Components[arg[p].c].B = b[p]
                THEN /\ k' = [k EXCEPT ![p] = 1]
                     /\ Components' = [Components EXCEPT ![arg[p].c].B = [val |-> a[p], seq |-> x[p]]]
                     /\ pc' = [pc EXCEPT ![p] = "O2"]
                ELSE IF k[p] = 2
                     THEN /\ k' = [k EXCEPT ![p] = 1]
                          /\ Components' = Components
                          /\ pc' = [pc EXCEPT ![p] = "O2"]
                     ELSE /\ k' = [k EXCEPT ![p] = k[p]+1]
                          /\ Components' = Components
                          /\ pc' = [pc EXCEPT ![p] = "O1A"]
          /\ UNCHANGED <<Components, X, a, b, x, r, arg, ret>>

O2(p)  == /\ pc[p] = "O2"
          /\ r' = [r EXCEPT ![p] = Components[arg[p].c].B.val]
          /\ pc' = [pc EXCEPT ![p] = "O3"]
          /\ UNCHANGED <<Components, X, a, b, x, k, arg, ret>>

O3(p)  == /\ pc[p] = "O3"
          /\ pc' = [pc EXCEPT ![p] = RemainderID]
          /\ ret' = [ret EXCEPT ![p] = r[p]]
          /\ UNCHANGED <<Components, X, a, b, x, k, r, arg>>

U1A(p) == /\ pc[p] = "U1A"
          /\ pc' = [pc EXCEPT ![p] = "U1B"]
          /\ b' = [b EXCEPT ![p] = Components[arg[p].c].B]
          /\ UNCHANGED <<Components, X, a, x, k, r, arg, ret>>

U1B(p) == /\ pc[p] = "U1B"
          /\ x' = [x EXCEPT ![p] = X]
          /\ IF b[p].seq = X (* Note that in the paper, this is x[p] but after the read - so here it should be X *)
                THEN /\ k' = [k EXCEPT ![p] = 1]
                     /\ pc' = [pc EXCEPT ![p] = "U2"]
                ELSE /\ k' = k
                     /\ pc' = [pc EXCEPT ![p] = "U1C"]
          /\ UNCHANGED <<Components, X, a, b, r, arg, ret>>

U1C(p) == /\ pc[p] = "U1C"
          /\ a' = [a EXCEPT ![p] = Read[Components[arg[p].c].A]]
          /\ pc' = [pc EXCEPT ![p] = "U1D"]
          /\ UNCHANGED <<Components, X, b, x, k, r, arg, ret>>

U1D(p) == /\ pc[p] = "U1D"
          /\ IF Components[arg[p].c].B = b[p]
                THEN /\ k' = [k EXCEPT ![p] = 1]
                     /\ Components' = [Components EXCEPT ![arg[p].c].B = [val |-> a[p], seq |-> x[p]]]
                     /\ pc' = [pc EXCEPT ![p] = "U2"]
                ELSE IF k[p] = 2
                     THEN /\ k' = [k EXCEPT ![p] = 1]
                          /\ Components' = Components
                          /\ pc' = [pc EXCEPT ![p] = "U2"]
                     ELSE /\ k' = [k EXCEPT ![p] = k[p]+1]
                          /\ Components' = Components
                          /\ pc' = [pc EXCEPT ![p] = "U1A"]
          /\ UNCHANGED <<Components, X, a, b, x, r, arg, ret>>

U2(p)  == /\ pc[p] = "U2"
          /\ Components' = [Components EXCEPT ![arg[p].c].A = arg[p].uop[Components[arg[p].c].A][1]]
          /\ r' = [r EXCEPT ![p] = arg[p].uop[Components[arg[p].c].A][2]]
          /\ pc' = [pc EXCEPT ![p] = "U3"]
          /\ UNCHANGED <<Components, X, a, b, x, k, arg, ret>>

U3(p)  == /\ pc[p] = "U3"
          /\ pc' = [pc EXCEPT ![p] = RemainderID]
          /\ ret' = [ret EXCEPT ![p] = r[p]]
          /\ UNCHANGED <<Components, X, a, b, x, k, r, arg>>

CC1(p) == /\ pc[p] = "CC1"
          /\ \E addr \in Addrs : 
             /\ addr \notin DOMAIN Components 
             /\ r' = [r EXCEPT ![p] = addr]
             /\ \E bval \in ObjOpRetDomain : 
                /\ Components' = [comp \in Addrs \cup {addr} |-> 
                                       IF comp = addr 
                                          THEN [A |-> arg[p].init, B |-> [val |-> bval, seq |-> X]]
                                          ELSE Components[comp]]
          /\ pc' = [pc EXCEPT ![p] = "CC2"]
          /\ UNCHANGED <<X, a, b, x, k, arg, ret>>

CC2(p) == /\ pc[p] = "CC2"
          /\ pc' = [pc EXCEPT ![p] = RemainderID]
          /\ ret' = [ret EXCEPT ![p] = r[p]]
          /\ UNCHANGED <<Components, AllocAddrs, X, a, b, x, k, r, arg>>

\* Initial configuration
InitState == CHOOSE state \in StateDomain : 
                    /\ DOMAIN state.val  = DOMAIN state.snap
                    /\ \A comp \in DOMAIN state.val : state.snap[comp] = Read[state.val[comp]]

(* TODO: *)

Init == /\ pc = [p \in ProcSet |-> RemainderID]
        /\ A = InitState.val
        /\ B = [i \in 1..M |-> [val |-> InitState.val[i], seq |-> 0]]
        /\ X = 0
        /\ a \in [ProcSet -> WordDomain]
        /\ b \in [ProcSet -> [val: WordDomain, seq: Nat]]
        /\ x \in [ProcSet -> Nat]
        /\ k \in [ProcSet -> 1..2]
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
\* Last modified Fri Aug 23 15:29:47 EDT 2024 by uguryavuz
\* Created Wed Mar 13 17:52:43 EDT 2024 by uguryavuz