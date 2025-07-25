------------------------- MODULE MCTracking_proofs --------------------------
(***************************************************************************)
(* This module contains proofs of the theorems in the MCTracking module.   *)
(***************************************************************************)
(* Author: Ugur Y. Yavuz (Boston University)                               *)
(* Last updated: 2025-02-10                                                *)
(***************************************************************************)

EXTENDS TLAPS
LOCAL INSTANCE Integers
LOCAL INSTANCE Sequences
LOCAL INSTANCE SequenceTheorems
CONSTANTS BOT,            (* Symbolic bottom value *)
          ProcSet,        (* Symbolic set of processes *)
          ConfigDomain,   (* Domain of configurations *)
          Delta(_, _, _)  (* Transition relation : config * process * config -> Bool *)

(***************************************************************************)
(* Invoke(P, p, op, arg) returns the set of configurations that are the    *)
(* result of invoking process p with operation op and argument arg, given  *)
(* that the process was idle in the previous configuration.                *)
(***************************************************************************)
Invoke(P, p, op, arg) == 
  {c \in ConfigDomain : \E c_prev \in P : 
      /\ c_prev.op[p] = BOT
      /\ c_prev.arg[p] = BOT
      /\ c_prev.res[p] = BOT
      /\ c.op  = [c_prev.op EXCEPT ![p] = op]
      /\ c.arg = [c_prev.arg EXCEPT ![p] = arg]
      /\ c.res = [c_prev.res EXCEPT ![p] = BOT]
      /\ c.state = c_prev.state}
   
(***************************************************************************)
(* TransitionsOK(c, alpha, d) checks if configuration c transitions to     *)
(* configuration d via the sequence of processes alpha.                    *)
(* It is essentially a transitive closure of Delta.                        *)
(***************************************************************************)
TransitionsOK(c, alpha, d) ==
  \E n \in Nat : \E beta \in Seq(ConfigDomain) :
     /\ Len(alpha) = n
     /\ Len(beta) = n+1
     /\ beta[1] = c
     /\ \A i \in 1..n : Delta(beta[i], alpha[i], beta[i+1])
     /\ beta[n+1] = d

(***************************************************************************)
(* Evolve(P) returns the set of configurations that can be reached from    *)
(* any configuration in P by allowing any sequence of processes to         *)
(* linearize as specified in Delta.                                        *)
(***************************************************************************)
Evolve(P) ==
  {c \in ConfigDomain : \E c_prev \in P : \E alpha \in Seq(ProcSet) : 
     TransitionsOK(c_prev, alpha, c)}

(***************************************************************************)
(* Filter(P, p, ret) returns the set of configurations that are the result *)
(* of filtering out configurations that do not have process p returning    *)
(* value ret, and setting the state of p to idle.                          *)
(***************************************************************************)
Filter(P, p, ret) ==
  {c \in ConfigDomain : \E c_prev \in P :
      /\ c_prev.res[p] = ret
      /\ c.op = [c_prev.op EXCEPT ![p] = BOT]
      /\ c.arg = [c_prev.arg EXCEPT ![p] = BOT]
      /\ c.res = [c_prev.res EXCEPT ![p] = BOT]
      /\ c.state = c_prev.state}

(***************************************************************************)
(* Theorem: If c transitions to d via alpha_1, and d transitions to e via  *)
(*          alpha_2, then c transitions to e via alpha_1 \o alpha_2.       *)
(***************************************************************************)
THEOREM SplitTransitionSeq ==
    ASSUME NEW c \in ConfigDomain,
           NEW d \in ConfigDomain,
           NEW e \in ConfigDomain,
           NEW alpha_1 \in Seq(ProcSet),
           NEW alpha_2 \in Seq(ProcSet),
           TransitionsOK(c, alpha_1, d),
           TransitionsOK(d, alpha_2, e)
    PROVE  TransitionsOK(c, alpha_1 \o alpha_2, e)
  <1> SUFFICES \E n \in Nat : \E beta \in Seq(ConfigDomain) : 
               /\ Len(alpha_1 \o alpha_2) = n
               /\ Len(beta) = n+1
               /\ beta[1] = c
               /\ \A i \in 1..n : Delta(beta[i], (alpha_1 \o alpha_2)[i], beta[i+1])
               /\ beta[n+1] = e
    BY Zenon DEF TransitionsOK
  <1>1. PICK n_1 \in Nat : \E beta_1 \in Seq(ConfigDomain) : 
             /\ Len(alpha_1) = n_1
             /\ Len(beta_1) = n_1 + 1
             /\ beta_1[1] = c
             /\ \A i \in 1..n_1 : Delta(beta_1[i], alpha_1[i], beta_1[i+1])
             /\ beta_1[n_1+1] = d
    BY Zenon DEF TransitionsOK
  <1>2. PICK beta_1 \in Seq(ConfigDomain) : 
             /\ Len(beta_1) = n_1 + 1
             /\ beta_1[1] = c
             /\ \A i \in 1..n_1 : Delta(beta_1[i], alpha_1[i], beta_1[i+1])
             /\ beta_1[n_1+1] = d
    BY <1>1
  <1>3. PICK n_2 \in Nat : \E beta_2 \in Seq(ConfigDomain) : 
             /\ Len(alpha_2) = n_2
             /\ Len(beta_2) = n_2 + 1
             /\ beta_2[1] = d
             /\ \A i \in 1..n_2 : Delta(beta_2[i], alpha_2[i], beta_2[i+1])
             /\ beta_2[n_2+1] = e
    BY Zenon DEF TransitionsOK
  <1>4. PICK beta_2 \in Seq(ConfigDomain) :
             /\ Len(beta_2) = n_2 + 1
             /\ beta_2[1] = d
             /\ \A i \in 1..n_2 : Delta(beta_2[i], alpha_2[i], beta_2[i+1])
             /\ beta_2[n_2+1] = e
    BY <1>3
  <1> DEFINE n == n_1 + n_2
  <1>5. Len(alpha_1 \o alpha_2) = n
    BY <1>1, <1>3
  <1> DEFINE beta == beta_1 \o Tail(beta_2)
  <1>6. Len(beta) = n + 1
    BY <1>1, <1>2, <1>3, <1>4, Z3T(15)
  <1>7. beta \in Seq(ConfigDomain)
    BY HeadTailProperties, <1>4
  <1>8. beta[1] = c
    <2>1. beta_1 \in Seq(ConfigDomain) /\ Tail(beta_2) \in Seq(ConfigDomain) BY <1>2, <1>4
    <2>2. \A i \in 1 .. Len(beta_1) + Len(Tail(beta_2)) : 
             beta[i] = IF i <= Len(beta_1) THEN beta_1[i] ELSE Tail(beta_2)[i - Len(beta_1)]
      BY ConcatProperties, <2>1
    <2>3. 1 \in 1 .. Len(beta_1) + Len(Tail(beta_2)) BY <1>2, <1>4, <2>1
    <2>4. 1 <= Len(beta_1) BY <1>2
    <2>5. beta[1] = beta_1[1] BY <2>2, <2>3, <2>4
    <2> QED BY <2>5, <1>2
  <1>9. beta[n+1] = e
    BY <1>2, <1>4
  <1> SUFFICES ASSUME NEW i \in 1..n
               PROVE  Delta(beta[i], (alpha_1 \o alpha_2)[i], beta[i+1])
    BY <1>5, <1>6, <1>7, <1>8, <1>9, Isa
  <1>10. Len(beta_2) = 1 \/ Len(beta_2) > 1 BY <1>4
  <1>11. CASE Len(beta_2) = 1
    <2>A. Len(Tail(beta_2)) = 0 BY <1>11, HeadTailProperties
    <2>B. Len(<< >>) = 0 BY EmptySeq
    <2>C. ASSUME NEW j \in 1 .. Len(<< >>)
          PROVE << >>[j] = Tail(beta_2)[j] BY <2>B
    <2>D. Tail(beta_2) \in Seq(ConfigDomain) BY <1>4
    <2>E. << >> \in Seq(ConfigDomain) OBVIOUS
    <2>F. << >> = Tail(beta_2) BY <2>A, <2>B, <2>C, <2>D, <2>E, SeqEqual, Zenon
    <2>G. beta = beta_1 \o <<>> BY <2>F, Zenon
    <2>H. beta = beta_1 BY <2>G
    <2>J. Len(alpha_2) = 0 BY <1>11, <1>3, <1>4, Z3T(15)
    <2>K. ASSUME NEW j \in 1 .. Len(<< >>)
          PROVE << >>[j] = alpha_2[j] BY <2>J
    <2>L. << >> \in Seq(ProcSet) BY <1>4
    <2>M. << >> = alpha_2 BY <2>J, <2>B, <2>K, <2>L, SeqEqual, Zenon
    <2>N. alpha_1 \o alpha_2 = alpha_1 BY <2>M
    <2> SUFFICES Delta(beta_1[i], alpha_1[i], beta_1[i+1]) BY <2>H, <2>N, Zenon
    <2> SUFFICES i \in 1..n_1 BY <1>2
    <2> QED BY <1>11, <1>3, <1>4, Z3T(15)
  <1> SUFFICES ASSUME Len(beta_2) > 1
               PROVE  Delta(beta[i], (alpha_1 \o alpha_2)[i], beta[i+1])
    BY <1>10, <1>11, Zenon
  <1>12. CASE i <= Len(beta_1)
    <2>1. CASE i < Len(beta_1)
      <3> USE <2>1
      <3>1. beta[i] = beta_1[i] OBVIOUS
      <3>2. beta[i+1] = beta_1[i+1] OBVIOUS
      <3>3. (alpha_1 \o alpha_2)[i] = alpha_1[i] BY <1>1, <1>2
      <3> QED
        BY <3>1, <3>2, <3>3, <1>2
    <2>2. CASE i = Len(beta_1)
      <3> USE <2>2
      <3>1. beta[i] = d BY <1>2
      <3>2. ~(i+1 <= Len(beta_1)) OBVIOUS
      <3>3. Len(Tail(beta_2)) > 0 BY HeadTailProperties
      <3>4. i+1 \in 1 .. Len(beta_1) + Len(Tail(beta_2)) BY <3>3
      <3>5. beta[i+1] = Tail(beta_2)[i+1 - Len(beta_1)] BY <3>4
      <3>6. beta[i+1] = beta_2[2] OBVIOUS
      <3>7. Len(alpha_2) > 0 BY <1>3, <1>4
      <3>8. i = Len(alpha_1) + 1 BY <1>1, <1>2
      <3>9. i \in 1 .. Len(alpha_1) + Len(alpha_2) BY <3>7, <3>8
      <3>10. ~(i <= Len(alpha_1)) BY <1>1, <1>2
      <3>11. (alpha_1 \o alpha_2)[i] = alpha_2[1] BY <3>8, <3>9, <3>10
      <3> SUFFICES Delta(d, alpha_2[1], beta_2[2]) BY <3>1, <3>6, <3>11
      <3> SUFFICES Delta(beta_2[1], alpha_2[1], beta_2[2]) BY <1>3, <1>4
      <3> QED BY <1>3, <1>4
    <2>3. i < Len(beta_1) \/ i = Len(beta_1) BY <1>12
    <2> QED BY <2>1, <2>2, <2>3, Zenon
  <1>13. CASE ~(i <= Len(beta_1))
    <2> i > Len(beta_1) BY <1>13
    <2>1. ~(i <= Len(beta_1)) OBVIOUS
    <2>2. Len(Tail(beta_2)) > 0 BY HeadTailProperties
    <2>3. i \in 1 .. n_1 + n_2 OBVIOUS
    <2>4. i \in 1 .. Len(beta_1) - 1 + Len(Tail(beta_2)) BY <1>2, <1>4, HeadTailProperties
    <2>5. i \in 1 .. Len(beta_1) + Len(Tail(beta_2)) BY <2>4
    <2>6. beta[i] = Tail(beta_2)[i - Len(beta_1)] BY <2>1, <2>5
    <2>7. i+1 \in 1 .. Len(beta_1) + Len(Tail(beta_2)) BY <2>4
    <2>8. ~(i+1 <= Len(beta_1)) OBVIOUS
    <2>9. beta[i+1] = Tail(beta_2)[i+1 - Len(beta_1)] BY <2>7, <2>8
    <2>10. Tail(beta_2)[i - Len(beta_1)] = beta_2[i - Len(beta_1) + 1] BY HeadTailProperties, <2>4
    <2>11. Tail(beta_2)[i+1 - Len(beta_1)] = beta_2[i+1 - Len(beta_1) + 1] BY HeadTailProperties, <2>4, <2>7
    <2>12. /\ beta[i]   = beta_2[i - Len(beta_1) + 1]
           /\ beta[i+1] = beta_2[i+1 - Len(beta_1) + 1] BY <2>6, <2>10, <2>9, <2>11, Zenon
    <2>13. i \in 1 .. Len(alpha_1) + Len(alpha_2) BY <2>3, <1>2, <1>4, <1>1, <1>3
    <2>14. ~(i <= Len(alpha_1)) BY <1>1, <1>2
    <2>15. (alpha_1 \o alpha_2)[i] = alpha_2[i - Len(alpha_1)] BY <2>13, <2>14
    <2> SUFFICES Delta(beta_2[i - Len(beta_1) + 1], alpha_2[i - Len(alpha_1)], beta_2[i+1 - Len(beta_1) + 1]) BY <2>12, <2>15, Zenon
    <2> SUFFICES Delta(beta_2[i - Len(beta_1) + 1], alpha_2[i - Len(beta_1) + 1], beta_2[i - Len(beta_1) + 1 + 1]) BY <1>1, <1>2
    <2> DEFINE j == i - Len(beta_1) + 1
    <2> SUFFICES Delta(beta_2[j], alpha_2[j], beta_2[j+1]) OBVIOUS
    <2> SUFFICES j \in 1 .. Len(beta_2)-1 BY <1>3, <1>4
    <2> QED BY <2>4
  <1> QED
    BY <1>12, <1>13, Zenon   

(***************************************************************************)
(* Theorem: If c is in the tracker P, then c is in Evolve(P).              *)
(***************************************************************************)
THEOREM EmptySeqEvolve == 
    ASSUME NEW P \in SUBSET ConfigDomain,
           NEW c \in ConfigDomain,
           c \in P
    PROVE  c \in Evolve(P)
  <1> USE DEF TransitionsOK
  <1> DEFINE n == 0
  <1> DEFINE alpha == <<>>
  <1> DEFINE beta == <<c>>
  <1>1. alpha \in Seq(ProcSet)
    OBVIOUS
  <1>2. beta \in Seq(ConfigDomain)
    OBVIOUS
  <1> SUFFICES /\ Len(alpha) = n
               /\ Len(beta) = n+1
               /\ beta[1] = c
               /\ \A i \in 1..n : Delta(beta[i], alpha[i], beta[i+1])
               /\ beta[n+1] = c
    BY Zenon, <1>1, <1>2 DEF Evolve
  <1> QED
    OBVIOUS

(***************************************************************************)
(* Theorem: If c is in P and c transitions to d via a process p, then d is *)
(*          in Evolve(P).                                                  *)
(***************************************************************************)
THEOREM SingleDeltaEvolve == 
    ASSUME NEW P \in SUBSET ConfigDomain,
           NEW c \in ConfigDomain,
           NEW d \in ConfigDomain,
           NEW p \in ProcSet,
           c \in P,
           Delta(c, p, d)
    PROVE  d \in Evolve(P)
  <1> USE DEF TransitionsOK
  <1> SUFFICES \E n \in Nat : \E alpha \in Seq(ProcSet) : \E beta \in Seq(ConfigDomain) :
        /\ Len(alpha) = n
        /\ Len(beta) = n+1
        /\ beta[1] = c
        /\ \A i \in 1..n : Delta(beta[i], alpha[i], beta[i+1])
        /\ beta[n+1] = d
    BY DEF Evolve
  <1> DEFINE n == 1
  <1> DEFINE alpha == <<p>>
  <1> DEFINE beta == <<c, d>>
  <1>1. alpha \in Seq(ProcSet)
    OBVIOUS
  <1>2. beta \in Seq(ConfigDomain)
    OBVIOUS
  <1>3. Len(beta) = n+1
    OBVIOUS
  <1>4. beta[n+1] = d
    OBVIOUS
  <1> SUFFICES \A i \in 1..n : Delta(beta[i], alpha[i], beta[i+1])
    BY Zenon, <1>1, <1>2, <1>3, <1>4
  <1> QED
    OBVIOUS
    
=============================================================================
