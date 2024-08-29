----------------------------- MODULE Cptable_Type -----------------------------
EXTENDS Integers
CONSTANTS ACK,           \* Default return value for returns with no value
          BOT,           \* For empty fields in meta-configurations 
          ProcSet,       \* The set of all processes
          Addrs,         \* The set of all memory addresses
          ObjDomain,     \* Domain of readable object states
          ObjOpRetDomain \* Domain of return values; including the return value of reads

\* Addrs / ObjDomain / ObjOpRetDomain are not empty
ASSUME AddrsNE == Addrs # {}
ASSUME ObjDomainNE == ObjDomain # {}
ASSUME ObjOpRetDomainNE == ObjOpRetDomain # {}

\* Define reading operation on objects
Read == CHOOSE fn \in [ObjDomain -> ObjOpRetDomain] : TRUE

\* Set of all possible operations
OpNames == {"Click", "Observe", "Update", "CreateComp", "DeleteComp"}

(* MAJOR TODO: make it take arg as argument etc. *)
\* You can't start a Click or Observe if there is an ongoing Click.
\* You can't start a Click if there is an ongoing Observe.
\* 
AllowedOpNames(pc, LineIDtoOp(_)) == 
    IF \E p \in ProcSet : LineIDtoOp(pc[p]) = "Click" 
       THEN {"Update", "CreateComp", "DeleteComp"}
    ELSE 
    IF \E p \in ProcSet : LineIDtoOp(pc[p]) = "Observe"
       THEN {"Observe", "Update", "CreateComp", "DeleteComp"}
    ELSE {"Click", "Observe", "Update", "CreateComp", "DeleteComp"}

\* Domain of the op field of meta-configurations - OpNames + {BOT}                       
OpDomain == OpNames \union {BOT}

\* Domain of the state field
\*  - val (partial map from Addrs to ObjDomain) (* Decided to go with partial function instead of nullable! *)
\*  - snap (partial map from Addrs to ObjOpRetDomain)
StateDomain == [val   : UNION {[AddrsSubset -> ObjDomain]      : AddrsSubset \in SUBSET Addrs},
                snap  : UNION {[AddrsSubset -> ObjOpRetDomain] : AddrsSubset \in SUBSET Addrs}]

\* Domain of the arg field of meta-configurations
\*  - Click takes no arguments (hence {BOT})
\*  - Observe takes an address
\*  - Update takes an address and a function in [ObjDomain -> ObjDomain \X ObjOpRetDomain]
\*  - CreateComp takes a readable object state
\*  - DeleteComp takes an address
ArgDomain == {BOT} \union
             [comp: Addrs] \union 
             [comp: Addrs, uop: [ObjDomain -> ObjDomain \X ObjOpRetDomain]] \union 
             [init: ObjDomain]

\* Return value domain: (defined separately from res field domain - because this will be the range of the ret variable 
\*  - Click returns ACK
\*  - Observe returns an elt. of ObjOpRetDomain
\*  - Update returns an elt. of ObjOpRetDomain
\*  - CreateComp returns an address
\*  - DeleteComp returns ACK
RetDomain == ObjOpRetDomain \union Addrs \union {ACK}
ResDomain == RetDomain \union {BOT}

\* ArgsOf(op) is the set of arguments that can be passed to operation op.
ArgsOf(op) == CASE op = "Click"      -> {BOT}
                [] op = "Observe"    -> [comp: Addrs]
                [] op = "Update"     -> [comp: Addrs, uop: [ObjDomain -> ObjDomain \X ObjOpRetDomain]]
                [] op = "CreateComp" -> [init: ObjDomain]
                [] op = "DeleteComp" -> [comp: Addrs]
                [] OTHER -> {}

\* Since we don't want processes to be able to observe/update non-existent components,
\* we define the set of allowed arguments for each operation. This is a function of which
\* addresses contain components, which the implementation must maintain.
AllowedArgs(op, ValidAddrs) == CASE op = "Click"   
                                    -> {BOT}
                                 [] op = "Observe" /\ ValidAddrs \in SUBSET Addrs
                                    -> [comp: ValidAddrs]
                                 [] op = "Update"  /\ ValidAddrs \in SUBSET Addrs
                                    -> [comp: ValidAddrs, uop: [ObjDomain -> ObjDomain \X ObjOpRetDomain]]
                                 [] op = "CreateComp" 
                                    -> [init: ObjDomain]
                                 [] op = "DeleteComp" /\ ValidAddrs \in SUBSET Addrs
                                    -> [comp: ValidAddrs]
                                 [] OTHER -> {}

\* ConfigDomain is the set of all possibilities
ConfigDomain == [state: StateDomain, 
                 op: [ProcSet -> OpDomain],
                 arg: [ProcSet -> ArgDomain],
                 res: [ProcSet -> ResDomain]]

\* Delta is the transition relation - given configuration c, p's operation
\* changes the configuration to d
Delta(c, p, d) == CASE (c.op[p] = "Click"
                          /\ c.arg[p] \in ArgsOf("Click") /\ c.res[p] = BOT)
                       -> /\ d.state = [val   |-> c.state.val, 
                                        snap  |-> [comp \in DOMAIN c.state.val |-> Read[c.state.val[comp]]]]
                          (* Note that, before the changes, it used to be that snap |-> c.state.val *)
                          /\ d.op    = c.op
                          /\ d.arg   = c.arg
                          /\ d.res   = [c.res EXCEPT ![p] = ACK]
                    [] (c.op[p] = "Observe"
                          /\ c.arg[p] \in ArgsOf("Observe") /\ c.res[p] = BOT)
                       -> /\ c.arg[p] \in AllowedArgs("Observe", DOMAIN c.state.snap)
                          /\ d.state = c.state
                          /\ d.op    = c.op
                          /\ d.arg   = c.arg
                          /\ d.res   = [c.res EXCEPT ![p] = c.state.snap[c.arg[p].comp]]
                    [] (c.op[p] = "Update"
                          /\ c.arg[p] \in ArgsOf("Update") /\ c.res[p] = BOT)
                       -> /\ c.arg[p] \in AllowedArgs("Update", DOMAIN c.state.val)
                          /\ d.state = [val   |-> [c.state.val EXCEPT ![c.arg[p].comp] = c.arg[p].uop[c.state.val[c.arg[p].comp]][1]],
                                        snap  |-> c.state.snap]
                          /\ d.op    = c.op
                          /\ d.arg   = c.arg
                          /\ d.res   = [c.res EXCEPT ![p] = c.arg[p].uop[c.state.val[c.arg[p].comp]][2]]
                    [] (c.op[p] = "CreateComp"
                          /\ c.arg[p] \in ArgsOf("CreateComp") /\ c.res[p] = BOT)
                       -> \E newcomp \in Addrs : 
                          /\ newcomp \notin DOMAIN c.state.val
                          /\ d.state = [val   |-> [comp \in DOMAIN c.state.val \union {newcomp} |-> 
                                                        IF comp = newcomp 
                                                           THEN c.arg[p].init 
                                                           ELSE c.state.val[comp]], 
                                        snap  |-> c.state.snap]
                          /\ d.op    = c.op
                          /\ d.arg   = c.res
                          /\ d.res   = [c.res EXCEPT ![p] = newcomp]
                    [] (c.op[p] = "DeleteComp"
                          /\ c.arg[p] \in ArgsOf("DeleteComp") /\ c.res[p] = BOT)
                       -> /\ c.arg[p] \in AllowedArgs("DeleteComp", DOMAIN c.state.val)
                          /\ d.state = [val   |-> [comp \in DOMAIN c.state.val \ {c.arg[p].comp} |-> c.state.val[comp]], 
                                        snap  |-> [comp \in DOMAIN c.state.val \ {c.arg[p].comp} |-> c.state.snap[comp]]]
                          /\ d.op    = c.op
                          /\ d.arg   = c.arg
                          /\ d.res   = [c.res EXCEPT ![p] = ACK]
                    [] OTHER -> FALSE

===============================================================================
\* Modification History
\* Last modified Mon Aug 26 09:12:37 EDT 2024 by uguryavuz
\* Created Tue Mar 12 21:14:40 EST 2024 by uguryavuz