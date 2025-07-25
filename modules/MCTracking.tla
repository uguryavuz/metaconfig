----------------------------- MODULE MCTracking -----------------------------
(***************************************************************************)
(* This module defines the machinery needed to implement metaconfiguration *)
(* tracking, namely the invocation, evolution and filtering of             *)
(* configurations; and includes theorems about these operations.           *)
(***************************************************************************)
(* Author: Ugur Y. Yavuz (Boston University)                               *)
(* Last updated: 2025-02-10                                                *)
(***************************************************************************)

LOCAL INSTANCE Sequences
LOCAL INSTANCE Integers
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

(***************************************************************************)
(* Theorem: If c is in the tracker P, then c is in Evolve(P).              *)
(***************************************************************************)
THEOREM EmptySeqEvolve == 
    ASSUME NEW P \in SUBSET ConfigDomain,
           NEW c \in ConfigDomain,
           c \in P
    PROVE  c \in Evolve(P)

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

=============================================================================
