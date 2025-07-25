---------------------------- MODULE Assumptions -----------------------------
(***************************************************************************)
(* This module contains assumptions that are used in other modules.        *)
(***************************************************************************)
(* Author: Ugur Y. Yavuz (Boston University)                               *)
(* Last updated: 2025-07-25                                                *)
(***************************************************************************)

EXTENDS ReadWriteReg

ASSUME RegDomainNE == RegDomain # {}
ASSUME BotDef == /\ BOT \notin {"Read", "Write", ACK}
                 /\ BOT \notin RegDomain

=============================================================================
