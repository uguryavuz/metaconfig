------------------------- MODULE FinitePermutations -------------------------
(***************************************************************************)
(* This module defines permutations of finite sets.                        *)
(***************************************************************************)
(* Author: Ugur Y. Yavuz (Boston University)                               *)
(* Last updated: 2025-02-11                                                *)
(***************************************************************************)

EXTENDS FiniteSets
LOCAL INSTANCE Sequences
LOCAL INSTANCE Integers

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

(***************************************************************************)
(* The empty permutation.                                                  *)
(***************************************************************************)
THEOREM EmptyPermutation == 
    /\ << >> \in Perm({})
    /\ (\A alpha \in Perm({}) : alpha = << >>)

(***************************************************************************)
(* In a permutation of a set, each element appears at a unique position    *)
(* within the sequence.                                                    *)
(***************************************************************************)
THEOREM PermutationIndex ==
    ASSUME NEW S, NEW x, NEW pi,
           x \in S, pi \in Perm(S)
    PROVE  \E i \in 1..Len(pi) : pi[i] = x

(***************************************************************************)
(* A permutation of a set of integers can be chosen to be sorted in        *)
(* increasing order.                                                       *)
(***************************************************************************)
THEOREM SortedPermutationOfIntegerSet ==
    ASSUME NEW S, IsFiniteSet(S), 
           S \in SUBSET Int
    PROVE  \E pi \in Perm(S) : 
             \A m, n \in 1..Len(pi) : m < n => pi[m] < pi[n]

=============================================================================
