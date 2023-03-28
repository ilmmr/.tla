------------------------- MODULE DiningPhilosophers -------------------------
(***************************************************************************)
(* A specification of the dining philosophers problem, originally          *)
(* described 1965 by Edsger Dijkstra.                                      *)
(* https://en.wikipedia.org/wiki/Dining_philosophers_problem               *)
(***************************************************************************)

EXTENDS Naturals, TLC, FiniteSets

(* N is the number of philosophers, which needs to be greater (>) than 0.  *)
CONSTANTS N
ASSUME N \in Nat \ {0}

VARIABLE   inHand, hasEaten, table, waiter
vars == << inHand, hasEaten, table, waiter >>
(* The idea is to check if the neighours of some philosopher are thinking. *)
(* inHand tracks which philospher holds the fork.                          *)
(* hasEaten tracks if every philo has eaten already.                       *)
(* if no deadlock solution is implememted, 2 distincts philosophers will   
   pick up a fork and then the system will stall (the philosophers starve!).
   For that I've used a waiter, which works as a mutex, if a waiter picks up
   a fork, it has to pick up the other one. 
*)

(* Range of a function. *)
Range(f) == { f[x] : x \in DOMAIN f }

TypeOK ==  /\ hasEaten \subseteq 1..N
           /\ table    \subseteq 1..N
           /\ inHand \in [1..N -> SUBSET 1..N]
           /\ waiter \in [1..N -> Nat]
           /\ \A p \in DOMAIN inHand : 
                /\ Cardinality(inHand[p]) \leq 2
                /\  CASE p = N -> inHand[p] \in SUBSET {N,1} 
                    [] OTHER   -> inHand[p] \in SUBSET {p,p+1}
 
Init == /\ hasEaten = {}
        /\ inHand   = [p \in 1..N |-> {}]
        /\ waiter   = [p \in 1..N |-> 0 ]
        /\ table    = 1..N

PickUp      == \E f \in table : \E p \in DOMAIN inHand :
                    (* pre-conditions *)
                    /\ p \notin hasEaten
                    /\ (f \notin Range(waiter)) \/ (waiter[p] = f) (* meaning that the fork is not allocated/stalling for anyone *)
                    /\ IF p = N 
                            THEN (f = N   /\ waiter' = [waiter EXCEPT ![p] = 1]) \/ (f = 1 /\ waiter' = [waiter EXCEPT ![p] = N  ]) 
                            ELSE (f = p+1 /\ waiter' = [waiter EXCEPT ![p] = p]) \/ (f = p /\ waiter' = [waiter EXCEPT ![p] = p+1]) 
                    /\ inHand' = [inHand EXCEPT ![p] = @ \cup {f}]
                    /\ table' = table \ {f}
                    /\ UNCHANGED hasEaten

Eats        == \E p \in DOMAIN inHand :
                    (* pre-condition *)
                    /\ Cardinality(inHand[p]) = 2
                    /\ waiter'   = [waiter EXCEPT ![p] = 0]
                    /\ hasEaten' = hasEaten \cup {p}
                    /\ inHand'   = [inHand EXCEPT ![p] = {}]
                    /\ table'    = table \cup inHand[p]

Next        == \/ PickUp
               \/ Eats

Spec      == Init /\ [][Next]_vars
FairSpec  == Spec /\ WF_hasEaten(Next)

(* Invariants *)
(* REMEMBER: All invariants are safety properties, but not all safety properties are invariants. *)
(*  The idea is to set this spec as an INVARIANT 
    It checks wheter it can find a trace such:
        -> every philo is done eating.
*)
NotSolved   == hasEaten # 1..N
ForksinHand == \A a,b \in DOMAIN inHand : inHand[a] = inHand[b] /\ ~(inHand[a] = {})=> a = b (* the same as being injective *)
(* Properties *)
WillEat     == \A p   \in 1..N          : []<>(p \in hasEaten) 
(* 
    DiningPhilosophers.cfg FILE :
        CONSTANTS N = 5
        SPECIFICATION FairSpec
        INVARIANT NotSolved ForksinHand
        PROPERTIES WillEat
*)
=============================================================================