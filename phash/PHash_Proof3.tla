---------------------------- MODULE PHash_Proof3 ----------------------------
EXTENDS PHash_Proof2_HO

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
    <2> QED
  <1> QED
    BY <1>1, <1>2 DEF InvWithL2

=============================================================================
\* Modification History
\* Last modified Thu Aug 08 15:13:15 EDT 2024 by uguryavuz
\* Last modified Thu Aug 08 18:01:34 UTC 2024 by uyavuz
\* Created Thu Aug 08 17:54:53 UTC 2024 by uyavuz
