--------------------- MODULE FinitePermutations_proofs ----------------------
(***************************************************************************)
(* This module contains proofs of the theorems in the FinitePermutations   *)
(* module.                                                                 *)
(***************************************************************************)
(* Author: Ugur Y. Yavuz (Boston University)                               *)
(* Last updated: 2025-02-11                                                *)
(***************************************************************************)

EXTENDS FiniteSets, TLAPS
LOCAL INSTANCE Sequences
LOCAL INSTANCE Integers
LOCAL INSTANCE FiniteSetTheorems

(***************************************************************************)
(* A permutation of a finite set S is an ordered sequence that contains    *)
(* each element of S exactly once, without repetition or omission.         *)
(* In this definition, we define it as a sequence of elements of S,        *)
(* of length equal to the cardinality of S, with no repeated elements.     *)
(* We note that the fact that no element is omitted is implicit, and       *)
(* derivable from this definition.                                         *)
(***************************************************************************)

(***************************************************************************)
(* Set of all permutations of S.                                           *)
(* Observe that this is defined as the empty set if S is not finite,       *)
(* as sequences are finite by definition.                                  *)
(***************************************************************************)
Perm(S) == {seq \in Seq(S) : /\ IsFiniteSet(S)
                             /\ Len(seq) = Cardinality(S) 
                             /\ \A i, j \in 1..Len(seq) : i # j 
                                    => seq[i] # seq[j]}

(***************************************************************************)
(* Every finite set can be permuted.                                       *)
(***************************************************************************)
THEOREM PermutationExists == 
    ASSUME NEW S, IsFiniteSet(S)
    PROVE  Perm(S) # {}
  <1> DEFINE n == Cardinality(S)
  <1>1. n \in Nat BY FS_CardinalityType
  <1> SUFFICES \E seq \in Seq(S) : /\ Len(seq) = n
                                   /\ \A i, j \in 1..Len(seq) : i # j => seq[i] # seq[j]
    BY DEF Perm
  <1> DEFINE Q(k) == k <= n =>  \E seq \in Seq(S) : /\ Len(seq) = k
                                                    /\ \A i, j \in 1..Len(seq) : i # j => seq[i] # seq[j]
  <1> SUFFICES Q(n) BY <1>1
  <1> SUFFICES \A m \in Nat : Q(m) BY <1>1
  <1> SUFFICES Q(0) /\ \A m \in Nat : Q(m) => Q(m+1)
    BY NatInduction, Isa
  <1>2. Q(0)
    <2> SUFFICES 0 <= n => \E seq \in Seq(S) : Len(seq) = 0 /\ \A i, j \in 1..Len(seq) : i # j => seq[i] # seq[j]
      BY Zenon
    <2> SUFFICES \E seq \in Seq(S) : Len(seq) = 0 /\ \A i, j \in 1..Len(seq) : i # j => seq[i] # seq[j]
      BY <1>1, Zenon
    <2> DEFINE seq == << >>
    <2>1. Len(seq) = 0 /\ seq \in Seq(S) OBVIOUS
    <2> SUFFICES ASSUME NEW i \in 1..Len(seq), NEW j \in 1..Len(seq), i # j
                 PROVE  seq[i] # seq[j]
      BY <2>1, Zenon
    <2> QED BY <2>1
  <1>3. \A m \in Nat : Q(m) => Q(m+1)
    <2> SUFFICES ASSUME NEW m \in Nat, Q(m)
                 PROVE  Q(m+1)
      OBVIOUS
    <2> SUFFICES ASSUME m+1 <= n
                 PROVE \E seq \in Seq(S) : Len(seq) = m+1 /\ \A i, j \in 1..Len(seq) : i # j => seq[i] # seq[j]
      BY Zenon
    <2>1. m <= n BY <1>1
    <2>2. PICK seq_prev \in Seq(S) : /\ Len(seq_prev) = m 
                                     /\ \A i, j \in 1..Len(seq_prev) : i # j => seq_prev[i] # seq_prev[j]
      BY <2>1, Zenon
    <2> DEFINE T == S \ Range(seq_prev)
    <2>3. T # {}
      <3> DEFINE R == Range(seq_prev)
      <3>1. IsFiniteSet(T) BY FS_Difference, Zenon
      <3>2. Cardinality(T) = n - Cardinality(S \cap R) BY FS_Difference, Zenon
      <3>3. S \cap R = R \cap S OBVIOUS
      <3>4. IsFiniteSet(R) BY FS_Subset, FS_Interval DEF Range
      <3>5. IsFiniteSet(S \cap R) BY FS_Intersection, Zenon
      <3>6. Cardinality(S \cap R) <= Cardinality(R) BY <3>3, <3>4, FS_Intersection, Zenon
      <3>7. R = {seq_prev[x] : x \in DOMAIN seq_prev} BY DEF Range
      <3> HIDE DEF R
      <3>8. IsFiniteSet(DOMAIN seq_prev) => Cardinality(R) <= Cardinality(DOMAIN seq_prev)
        BY <3>7, FS_Image, Isa
      <3>9. Cardinality(R) <= m BY <2>2, <3>8, FS_Interval DEF Seq
      <3>10. Cardinality(T) >= n - Cardinality(R) BY <3>1, <3>4, <3>5, <3>2, <3>6, FS_CardinalityType
      <3>11. Cardinality(T) >= n - m BY <3>10, <3>9, <3>1, <3>4, FS_CardinalityType
      <3>12. Cardinality(T) > 0 BY <3>11, <1>1, <3>1, FS_CardinalityType
      <3> QED BY <3>1, <3>12, FS_EmptySet
    <2>4. PICK x \in T : x \notin Range(seq_prev) BY <2>3
    <2> DEFINE seq == Append(seq_prev, x)
    <2>5. seq \in Seq(S) OBVIOUS
    <2>6. Len(seq) = m+1 BY <2>2
    <2>7. \A i, j \in 1..Len(seq) : i # j => seq[i] # seq[j] BY <2>2, <2>4 DEF Range
    <2> QED BY <2>5, <2>6, <2>7, Zenon
  <1> QED BY <1>2, <1>3, Isa

(***************************************************************************)
(* The empty permutation.                                                  *)
(***************************************************************************)
THEOREM EmptyPermutation == 
    /\ << >> \in Perm({})
    /\ (\A alpha \in Perm({}) : alpha = << >>)
  BY FS_EmptySet DEF Perm

(***************************************************************************)
(* In a permutation of a set, each element appears at a unique position    *)
(* within the sequence.                                                    *)
(***************************************************************************)
THEOREM PermutationIndex ==
    ASSUME NEW S, NEW x, NEW pi,
           x \in S, pi \in Perm(S)
    PROVE  \E i \in 1..Len(pi) : pi[i] = x
  <1> SUFFICES ASSUME IsFiniteSet(S),
                      \A i \in 1..Len(pi) : pi[i] # x
               PROVE  FALSE
    BY DEF Perm
  <1> DEFINE I == 1..Len(pi)
  <1> DEFINE R == Range(pi)
  <1>1. Len(pi) \in Nat BY DEF Perm
  <1>2. IsFiniteSet(I) BY <1>1, FS_Interval
  <1>3. pi \in [I -> R] BY DEF Perm, Range
  <1>4. Cardinality(I) = Cardinality(S) BY FS_Interval DEF Perm
  <1>5. x \notin R BY DEF Range, Perm
  <1>6. R \in SUBSET S BY DEF Range, Perm
  <1>7. IsFiniteSet(R) BY <1>6, FS_Subset
  <1>8. Cardinality(R) < Cardinality(S) BY <1>5, <1>6, FS_Subset, FS_CardinalityType
  <1>9. Cardinality(R) < Cardinality(I) BY <1>4, <1>8
  <1>10. \E y, z \in I : y # z /\ pi[y] = pi[z] BY <1>2, <1>3, <1>7, <1>9, FS_PigeonHole
  <1> QED BY <1>10 DEF Perm

=============================================================================
