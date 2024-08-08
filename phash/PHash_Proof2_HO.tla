--------------------------- MODULE PHash_Proof2_HO ---------------------------
EXTENDS PHash_Proof1_HO

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
THEOREM L1Next == InvWithL1 /\ [Next]_vars => InvL1'

===========================================================================
\* Modification History
\* Last modified Thu Aug 08 11:43:33 EDT 2024 by uguryavuz
\* Created Thu Aug 08 09:43:24 EDT 2024 by uguryavuz
