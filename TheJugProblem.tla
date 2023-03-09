--------------------------- MODULE TheJugProblem ----------------------------
(***************************************************************************)
(* We now generalize the problem from Die Hard:                            *)
(*     -> 2 jugs of water are available of n and m lt                      *)
(*     -> We want to fill exactly j lt, where j differs from m and n       *)
(***************************************************************************)
EXTENDS Naturals

(* We now declare two constant parameters.                                 *)
CONSTANT Jug,      \* The set of all jugs.
         Capacity, \* A function, where Capacity[j] is the capacity of jug j.
         Goal      \* The quantity of water our heros must measure.


(* Change these values *)
mGoal == 4
mJug  == {"j3", "j5"}
mCapacity == [jug \in Jug |-> CASE jug="j3" -> 3
                              []   jug="j5" -> 5]
(* We make an assumption about these constants--namely, that Capacity is a *)
(* function from jugs to positive integers, and Goal is a natural number.  *)
ASSUME /\ Capacity \in [Jug -> (Nat \ {0})]
       /\ Goal \in Nat
-----------------------------------------------------------------------------
VARIABLE contents \* contents[j] is the amount of water in jug j
TypeOK == contents \in [Jug -> Nat]
Init   == contents   = [j \in Jug |-> 0]
-----------------------------------------------------------------------------

fill(j)  == contents' = [contents EXCEPT ![j] = Capacity[j]]
empty(j) == contents' = [contents EXCEPT ![j] = 0]
  
jug2jug(j, k) == 
  LET waterTransfered == LET diff == (Capacity[k]-contents[k]) IN 
                            CASE (contents[j] \leq diff) -> contents[j]
                            [] OTHER -> diff
  IN  contents' = [contents EXCEPT ![j] = @ - waterTransfered,
                                   ![k] = @ + waterTransfered]

(***************************************************************************)
(* As usual, the next-state relation Next is the disjunction of all        *)
(* possible actions, where existential quantification is a general form of *)
(* disjunction.                                                            *)
(***************************************************************************)
JugS == \E j \in Jug : \E k \in Jug \ {j} : jug2jug(j,k)
Next ==  \E j \in Jug : \/ fill(j)
                        \/ empty(j)
                        \/ JugS
(***************************************************************************)
(* We define the formula Spec to be the complete specification, asserting  *)
(* of a behavior that it begins in a state satisfying Init, and that every *)
(* step either satisfies Next or else leaves contents unchanged.           *)
(***************************************************************************)
Spec == Init /\ [][Next]_contents
-----------------------------------------------------------------------------
(***************************************************************************)
(* We define NotSolved to be true of a state iff no jug contains Goal      *)
(* gallons of water.                                                       *)
(***************************************************************************)
NotSolved == \A j \in Jug : contents[j] # Goal
(***************************************************************************)
(* We find a solution by having TLC check if NotSolved is an invariant,    *)
(* which will cause it to print out an "error trace" consisting of a       *)
(* behavior ending in a states where NotSolved is false.  Such a           *)
(* behavior is the desired solution.                                       *)
(* INVARIANT NotSolved                                                     *)
(*                                                                         *)
(* => This is also known as PROOF BY REFUTATION                            *)
(* Which means that this would be the same as defining a PROPERTY where:   *)
(*   Succ == <>(\E j \in Jug : contents[j] = Goal)                         *)
Success   == <>(\E j \in Jug : contents[j] = Goal)
(* However, as stuttering can happen we must define a fairness for Prop.   *)
(* If we apply WF to Next, this will still fail since                      *)
(*    -> the junk j can be filled and emptyied continuously...             *)
(* So we need to ensure that jug2jug is executed                           *)

(* The bad thing about TLA+, I found it difficult to get it with fairness. *)
(* In such cases its better to verify using an Invariance, since TLA+ is   *)
(* unable to return satisfying instances: per say, return me an instance   *)
(* where the goal is achieved                                              *)
FairSpec  == Spec /\ WF_contents(Next)
THEOREM FairSpec => Success
(***************************************************************************)
=============================================================================