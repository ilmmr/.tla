-------------------------- MODULE CigaretteSmokers --------------------------
(***************************************************************************)
(* A specification of the cigarette smokers problem, originally            *)
(* described in 1971 by Suhas Patil.                                       *)
(* https://en.wikipedia.org/wiki/Cigarette_smokers_problem                 *)
(***************************************************************************)
EXTENDS Integers, FiniteSets, TLC

CONSTANT INGREDIENTS
(* INGREDIENTS == {"tobacco", "paper", "matches"} => put this on .cfg file *)
(*  SMOKERS     == {"Juan", "Paulo", "Adrian"} 
    This ref is not necessary as each i of INGREDIENTS represents a different
    smoker s.
*)

(* The TABLE defines every possible combination of 2 ingredients on the table *)
TABLE       == {s \in SUBSET INGREDIENTS : Cardinality(s) = 2}

(* While the dealer variable defines 1 of the sets of the TABLE 
   inHand variable associates a smoker (an ingredient) with 
   a set of ingredients.
*)
VARIABLE   dealer, inHand, doneSmoking
vars == << dealer, inHand, doneSmoking >>

TypeOK ==  /\ dealer \in (TABLE \cup {})
           /\ TABLE \subseteq (SUBSET INGREDIENTS)
           /\ inHand \in [INGREDIENTS -> SUBSET INGREDIENTS]
           /\ doneSmoking \subseteq INGREDIENTS

Init == /\ LET t == CHOOSE t \in TABLE : TRUE IN dealer = t
        /\ inHand        = [i \in INGREDIENTS |-> {i}]
        /\ doneSmoking   = {}
    
PickUp      == \E i \in dealer : \E s \in DOMAIN inHand : 
                    /\ ~(s = i) (* A smoker can not pick up its ingredient *)
                    /\ inHand' = [inHand EXCEPT ![s] = @ \cup {i}]
                    /\ dealer' = dealer \ {i}
                    /\ UNCHANGED doneSmoking

Smoking     == \E s \in DOMAIN inHand :
                    (* pre-condition *)
                    /\ inHand[s] = INGREDIENTS /\ dealer = {}
                    /\ doneSmoking' = doneSmoking \cup {s}
                    /\ UNCHANGED << inHand, dealer >>

StopSmoking == \E s \in DOMAIN inHand :
                    (* pre-condition *)
                    /\ inHand[s] = INGREDIENTS
                    /\ inHand'   = [inHand EXCEPT ![s] = {s}]
                    /\ \E t \in TABLE : dealer' = t
                    /\ UNCHANGED doneSmoking

RequestOne  == \E s \in DOMAIN inHand :
                    /\ dealer  = {}
                    /\ dealer' = {s}
                    /\ UNCHANGED << inHand, doneSmoking >>

Next        == \/ PickUp
               \/ Smoking
               \/ StopSmoking
(* As it stands, this deadlocks as,
    -> A smoker a could pick an ing c
    -> A smoker c could pick an ing b
    which means,
    => Neither a or b can smoke.
*)
               \/ RequestOne

Spec      == Init /\ [][Next]_vars
FairSpec  == Spec /\ WF_vars(Next)

(*  The idea is to set this spec as an INVARIANT 
    It checks wheter it can find a trace such:
        -> every smoker is done smoking.
*)
NotSolved == (doneSmoking # INGREDIENTS)

(* 
    PUT this into the .cfg file:
    CONSTANT INGREDIENTS = {"tobacco", "paper", "matches"}
    SPECIFICATION FairSpec
    INVARIANT NotSolved
*)
=============================================================================