--------------------------- MODULE TransitionCommit -------------------------
CONSTANT
    \* @type: Set(Nat); 
    Participant
VARIABLE
        \* @type: Nat -> Str; 
        pState
-----------------------------------------------------------------------------
Prepare(p)   == /\ pState[p] = "working"
                /\ pState'   = [pState EXCEPT ![p] = "prepared"]

ItCommits(p) == /\ pState[rm] = "prepared"
                /\ \A pp \in Participant : pState[pp] \in {"prepared", "committed"} \* can commit
                /\ pState' = [pState EXCEPT ![p] = "committed"]
    
ItAborts(p)  == /\ pState[p] \in {"working", "prepared"}
                /\ \A pp \in Participant : pState[pp] # "committed" \* can not commit
                /\ pState' = [pState EXCEPT ![p] = "aborted"]

Decide(p)    == ItAborts(p) \/ ItCommits(p) 
-----------------------------------------------------------------------------
Init == pState = [p \in Participant |-> "working"]
Next == \E p \in Participant : Prepare(p) \/ Decide(p)
Spec == Init /\ [][Next]_pState
-----------------------------------------------------------------------------
(*****************************   INVARIANTS   ******************************)
TypeOK     == pState \in [Participant -> {"working", "prepared", "committed", "aborted"}]
Consistent ==  
  (*************************************************************************)
  (* A state predicate asserting that two Participants have not arrived at *)
  (* conflicting decisions.                                                *)
  (*************************************************************************)
  \A p, pp \in Participant : pState[p] = "aborted" => pState[p] # "committed"
  (* USING DISJUNCTIONS: p => ~q <=> (~p \/ ~q) <=> ~(p /\ q)              *)
 
THEOREM Spec => [](TypeOK /\ Consistent)
=============================================================================