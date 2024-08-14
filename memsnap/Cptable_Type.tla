----------------------------- MODULE Cptable_Type -----------------------------
EXTENDS Integers
CONSTANTS ACK, \* Default return value for returns with no value
          BOT, \* 
          ProcSet, \* The set of all processes
          WordDomain, \* The domain of the words
          M, \* The size of the array of words
          UOpSet \* The set of all update operations (with uarg folded in)
                 \* these should be maps WordDomain -> WordDomain x (some return domain for the operation)

\* Assume well-formedness of the UOpSet:
\* specifically, it consists of maps from WordDomain to WordDomain x RetValues, for some set RetValues.
\* Note that the set RetValues is a set that contains all possible return values for 
\* every operation in UOpSet.
ASSUME UOpSet_WF == 
    \E RetValues : /\ RetValues # {}
                   /\ UOpSet \in SUBSET [WordDomain -> WordDomain \X RetValues]

\* M is a non-zero natural number
ASSUME M_NZ == M \in Nat \ {0}

\* WordDomain is a non-empty set
ASSUME WordDomainNE == WordDomain # {}

\* Retrieve the return domain of the UOpSet
UOpRetDomain == CHOOSE RetValues : /\ RetValues # {}
                                   /\ UOpSet \in SUBSET [WordDomain -> WordDomain \X RetValues]

\* Scanner and updater processes : assume ProcSet is non-empty
ASSUME ProcSetNE == ProcSet # {}
Scanner == CHOOSE s \in ProcSet : TRUE
UpdSet  == ProcSet \ {Scanner}

OpNames == {"Click", "Observe", "Update"}
OpDomain == {"Click", "Observe", "Update", BOT}
StateDomain == [val:  [1..M -> WordDomain],
                snap: [1..M -> WordDomain]]

\* Click takes no arguments, 
\* Observe takes i \in 1..M, 
\* Update takes i \in 1..M and uop \in UOpSet
ArgDomain == [i: 1..M] \union [i: 1..M, uop: UOpSet] \union {BOT}

\* Return values domain: Click returns ACK, Observe returns a word, Update returns something in UOpRetDomain
RetDomain == WordDomain \union UOpRetDomain \union {ACK}
ResDomain == WordDomain \union UOpRetDomain \union {ACK, BOT}

\* ArgsOf(op) is the set of arguments that can be passed to operation op
ArgsOf(op) == CASE op = "Click"   -> {BOT}
                [] op = "Observe" -> [i: 1..M]
                [] op = "Update"  -> [i: 1..M, uop: UOpSet]
                [] OTHER          -> {}

\* ConfigDomain is the set of all possibilities
ConfigDomain == [state: StateDomain, 
                 op: [ProcSet -> OpDomain],
                 arg: [ProcSet -> ArgDomain],
                 res: [ProcSet -> ResDomain]]

\* Delta is the transition relation - given configuration c, p's operation
\* changes the configuration to d
Delta(c, p, d) == CASE (c.op[p] = "Click"
                          /\ c.arg[p] \in ArgsOf("Click") /\ c.res[p] = BOT)
                       -> /\ d.state = [val |-> c.state.val, snap |-> c.state.val]
                          /\ d.op    = c.op
                          /\ d.arg   = c.arg
                          /\ d.res   = [c.res EXCEPT ![p] = ACK]
                    [] (c.op[p] = "Observe"
                          /\ c.arg[p] \in ArgsOf("Observe") /\ c.res[p] = BOT)
                       -> /\ d.state = c.state
                          /\ d.op    = c.op
                          /\ d.arg   = c.arg
                          /\ d.res   = [c.res EXCEPT ![p] = c.state.snap[c.arg[p].i]]
                    [] (c.op[p] = "Update"
                          /\ c.arg[p] \in ArgsOf("Update") /\ c.res[p] = BOT)
                       -> /\ d.state = [val  |-> [c.state.val EXCEPT ![c.arg[p].i] = c.arg[p].uop[c.state.val[c.arg[p].i]][1]],
                                        snap |-> c.state.snap]
                          /\ d.op    = c.op
                          /\ d.arg   = c.arg
                          /\ d.res   = [c.res EXCEPT ![p] = c.arg[p].uop[c.state.val[c.arg[p].i]][2]]
                    [] OTHER -> FALSE

===============================================================================
\* Modification History
\* Last modified Tue Aug 13 11:27:37 EDT 2024 by uguryavuz
\* Created Tue Mar 12 21:14:40 EST 2024 by uguryavuz