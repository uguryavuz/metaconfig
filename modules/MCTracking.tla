----------------------------- MODULE MCTracking -----------------------------
(***************************************************************************)
(* This module defines the machinery needed to implement metaconfiguration *)
(* tracking, namely the invocation, evolution and filtering of             *)
(* configurations; and includes theorems about these operations.           *)
(***************************************************************************)
(* Author: Ugur Y. Yavuz (Boston University)                               *)
(* Last updated: 2025-08-05                                                *)
(***************************************************************************)

EXTENDS Integers, Sequences

CONSTANTS 
  BOT,            (* Symbolic bottom value *)
  ProcSet,        (* Symbolic set of processes *)
  StateDomain,
  OpNames,
  ArgsOf(_),
  RetsOf(_),
  Delta(_, _, _)  (* Transition relation : conf * proc * conf -> bool *)

(***************************************************************************)
(* Domain of configurations                                                *)
(***************************************************************************)
OpDomain == OpNames \union {BOT}
ArgDomain == (UNION {ArgsOf(op) : op \in OpNames}) \union {BOT}
RetDomain == (UNION {RetsOf(op) : op \in OpNames})
ResDomain == (UNION {RetsOf(op) : op \in OpNames}) \union {BOT}
ConfigDomain == 
  [state: StateDomain, 
   op: [ProcSet -> OpDomain], 
   arg: [ProcSet -> ArgDomain], 
   res: [ProcSet -> ResDomain]]

(***************************************************************************)
(* Invoke(P, p, op, arg) returns the set of configurations that are the    *)
(* result of invoking process p with operation op and argument arg, given  *)
(* that the process was idle in the previous configuration.                *)
(***************************************************************************)
Invoke(pset, p, op, arg) == 
  {c \in ConfigDomain : \E c_prev \in pset : 
    /\ c_prev.op[p] = BOT
    /\ c_prev.arg[p] = BOT
    /\ c_prev.res[p] = BOT
    /\ c.op  = [c_prev.op EXCEPT ![p] = op]
    /\ c.arg = [c_prev.arg EXCEPT ![p] = arg]
    /\ c.res = c_prev.res
    /\ c.state = c_prev.state}
   
(***************************************************************************)
(* TransitionsOK(c, alpha, d) checks if configuration c transitions to     *)
(* configuration d via the sequence of processes alpha.                    *)
(* It is essentially a transitive closure of Delta.                        *)
(***************************************************************************)
TransitionsOK(c, alpha, d) ==
  \E beta \in Seq(ConfigDomain) :
    /\ Len(beta) = Len(alpha)+1
    /\ beta[1] = c
    /\ \A i \in 1..Len(alpha) : Delta(beta[i], alpha[i], beta[i+1])
    /\ beta[Len(beta)] = d

(***************************************************************************)
(* Evolve(P) returns the set of configurations that can be reached from    *)
(* any configuration in P by allowing any sequence of processes to         *)
(* linearize as specified in Delta.                                        *)
(***************************************************************************)
Evolve(pset) ==
  {c \in ConfigDomain : \E c_prev \in pset : \E alpha \in Seq(ProcSet) : 
    TransitionsOK(c_prev, alpha, c)}

(***************************************************************************)
(* Filter(P, p, ret) returns the set of configurations that are the result *)
(* of filtering out configurations that do not have process p returning    *)
(* value ret, and setting the state of p to idle.                          *)
(***************************************************************************)
Filter(pset, p, ret) ==
  {c \in ConfigDomain : \E c_prev \in pset :
    /\ c_prev.res[p] = ret
    /\ c.op = [c_prev.op EXCEPT ![p] = BOT]
    /\ c.arg = [c_prev.arg EXCEPT ![p] = BOT]
    /\ c.res = [c_prev.res EXCEPT ![p] = BOT]
    /\ c.state = c_prev.state}

(***************************************************************************)
(* THEOREMS                                                                *)
(***************************************************************************)

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
(* Evolve theorems                                                         *)
(***************************************************************************)

(***************************************************************************)
(* Theorem: If c is in P, then c is in Evolve(P).                          *)
(***************************************************************************)
THEOREM EmptySeqEvolve == 
    ASSUME NEW pset \in SUBSET ConfigDomain,
           NEW c \in ConfigDomain,
           c \in pset
    PROVE  c \in Evolve(pset)

(***************************************************************************)
(* Theorem: If c is in P and c transitions to d via a process p, then d is *)
(*          in Evolve(P).                                                  *)
(***************************************************************************)
THEOREM SingleDeltaEvolve == 
    ASSUME NEW pset \in SUBSET ConfigDomain,
           NEW c \in ConfigDomain,
           NEW d \in ConfigDomain,
           NEW p \in ProcSet,
           c \in pset,
           Delta(c, p, d)
    PROVE  d \in Evolve(pset)

(***************************************************************************)
(* Theorem: If c is in Evolve(P_1) where P_1 is a subset of P_2, then c is *)
(*          also in Evolve(P_2).                                           *)
(***************************************************************************) 
THEOREM EvolveForSubset ==
    ASSUME NEW pset_sub, 
           NEW pset_main,
           pset_sub \in SUBSET pset_main
    PROVE  Evolve(pset_sub) \in SUBSET Evolve(pset_main)

(***************************************************************************)
(* Invoke theorems                                                         *)
(***************************************************************************)

(***************************************************************************)
(* Theorem: To show that c is in Invoke(P, p, op, arg) it suffices to show *)
(*          that c_prev where c_prev is the configuration before invoking  *)
(*          with op and arg is in P.                                       *)
(***************************************************************************)
THEOREM InvokeFromUninvoked ==
    ASSUME NEW pset \in SUBSET ConfigDomain,
           NEW p \in ProcSet, NEW op, NEW arg,
           NEW c \in ConfigDomain,
           c.op[p] = op,
           c.arg[p] = arg,
           c.res[p] = BOT,
           NEW c_prev,
           c_prev = [c EXCEPT !.op = [c.op EXCEPT ![p] = BOT], 
                              !.arg = [c.arg EXCEPT ![p] = BOT]],
           c_prev \in pset
    PROVE  c \in Invoke(pset, p, op, arg)

(***************************************************************************)
(* Theorem: To show that c is in Evolve(Invoke(P, p, op, arg)) it          *)
(*          suffices to show that c_prev where c_prev is the configuration *)
(*          before invoking with op and arg is in P.                       *)
(***************************************************************************)
THEOREM InvokeAndEvolveFromUninvoked ==
    ASSUME NEW pset \in SUBSET ConfigDomain,
           NEW p \in ProcSet, NEW op, NEW arg,
           NEW c \in ConfigDomain,
           c.op[p] = op,
           c.arg[p] = arg,
           c.res[p] = BOT,
           NEW c_prev,
           c_prev = [c EXCEPT !.op = [c.op EXCEPT ![p] = BOT], 
                              !.arg = [c.arg EXCEPT ![p] = BOT]],
           c_prev \in pset
    PROVE  c \in Evolve(Invoke(pset, p, op, arg))

(***************************************************************************)
(* Theorem: If c is in Invoke(P_1, p, op, arg) with P_1 a subset of P_2,   *)
(*          then c is also in Invoke(P_2, p, op, arg).                     *)
(***************************************************************************)
THEOREM InvokeForSubset == 
    ASSUME NEW pset_sub, NEW pset_main,
           pset_sub \in SUBSET pset_main,
           NEW p, NEW op, NEW arg
    PROVE  Invoke(pset_sub, p, op, arg) \in SUBSET Invoke(pset_main, p, op, arg)

(***************************************************************************)
(* Filter theorems                                                         *)
(***************************************************************************)

(***************************************************************************)
(* Theorem: To show that c is in Filter(P, p, ret) it suffices to show     *)
(*          that c_prev where c_prev is the configuration before the       *)
(*          filter is applied is in P for p the return value ret.          *)
(***************************************************************************)
THEOREM FilterFromUnfiltered ==
    ASSUME NEW pset \in SUBSET ConfigDomain,
           NEW p \in ProcSet, NEW op, NEW arg, NEW ret,
           NEW c \in ConfigDomain,
           c.op[p] = BOT,
           c.arg[p] = BOT,
           c.res[p] = BOT,
           NEW c_prev,
           c_prev = [c EXCEPT !.op = [c.op EXCEPT ![p] = op], 
                              !.arg = [c.arg EXCEPT ![p] = arg],
                              !.res = [c.res EXCEPT ![p] = ret]],
           c_prev \in pset
    PROVE  c \in Filter(pset, p, ret)

(***************************************************************************)
(* Theorem: To show that c is in Filter(Evolve(P), p, ret) it suffices to  *)
(*          show that c_prev where c_prev is the configuration before the  *)
(*          filter is applied is in P for p the return value ret.          *)
(***************************************************************************)
THEOREM EvolveAndFilterFromUnfiltered ==
    ASSUME NEW pset \in SUBSET ConfigDomain,
           NEW p \in ProcSet, NEW op, NEW arg, NEW ret,
           NEW c \in ConfigDomain,
           c.op[p] = BOT,
           c.arg[p] = BOT,
           c.res[p] = BOT,
           NEW c_prev,
           c_prev = [c EXCEPT !.op = [c.op EXCEPT ![p] = op], 
                              !.arg = [c.arg EXCEPT ![p] = arg],
                              !.res = [c.res EXCEPT ![p] = ret]],
           c_prev \in pset
    PROVE  c \in Filter(Evolve(pset), p, ret)

(***************************************************************************)
(* Theorem: If c is in Filter(P_1, p, ret) with P_1 a subset of P_2,       *)
(*          then c is also in Filter(P_2, p, ret).                         *)
(***************************************************************************)
THEOREM FilterForSubset ==
    ASSUME NEW pset_sub, NEW pset_main,
           pset_sub \in SUBSET pset_main,
           NEW p, NEW ret
    PROVE  Filter(pset_sub, p, ret) \in SUBSET Filter(pset_main, p, ret)

=============================================================================
