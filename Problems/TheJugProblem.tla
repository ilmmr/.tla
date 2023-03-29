--------------------------- MODULE TheJugProblem ----------------------------
(***************************************************************************)
(* We now generalize the problem from Die Hard:                            *)
(*     -> 2 jugs of water are available of n and m lt                      *)
(*     -> We want to fill exactly j lt, where j differs from m and n       *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT 
         \* @type: Set(Str);
         Jug,
         \* @type: Str -> Nat;
         Capacity,
         \* @type: Nat;
         Goal

ASSUME /\ Capacity \in [Jug -> (Nat \ {0})]
       /\ Goal \in Nat

VARIABLE
        \* @type: Str -> Nat; 
        contents

fill(j)  == contents' = [contents EXCEPT ![j] = Capacity[j]]
empty(j) == contents' = [contents EXCEPT ![j] = 0]
  
jug2jug(j, k) == 
  LET waterTransfered == LET diff == (Capacity[k]-contents[k]) IN 
                            CASE (contents[j] \leq diff) -> contents[j]
                            [] OTHER -> diff
  IN  contents' = [contents EXCEPT ![j] = @ - waterTransfered,
                                   ![k] = @ + waterTransfered]

-----------------------------------------------------------------------------
JugS == \E j \in Jug : \E k \in Jug \ {j} : jug2jug(j,k)

Next ==  \E j \in Jug : \/ fill(j)
                        \/ empty(j)
                        \/ JugS

Init   == contents   = [j \in Jug |-> 0]

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
FairSpec      == Spec /\ WF_contents(Next)
TypeInvariant == contents \in [Jug -> Nat]
THEOREM FairSpec => Success
THEOREM FairSpec => []TypeInvariant
(***************************************************************************)
=============================================================================