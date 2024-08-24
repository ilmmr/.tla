---------------------- MODULE ReadersNWritersSimplified ----------------------
(*****************************************************************************)
(* A specification of the readers and writers problem, a common computing    *)
(* problem in concurrency.                                                   *)
(* Note: this example checks for data consistency when writing. Each writer  *)
(* increments a global counter, if the counter is bellow 5.                  *)
(* Can the counter ever go beyond 5?                                         *)
(* https://en.wikipedia.org/wiki/Readers%E2%80%93writers_problem             *)
(*****************************************************************************)
EXTENDS FiniteSets, Naturals, Sequences, TLC

CONSTANT 
    \* @type: Nat;
    NumWriters
Writers == 1..NumWriters

VARIABLES
    \* @type: Nat;
    counter,
    \* @type: Set(Nat);
    writers
vars == << counter, writers >>

TypeInvariant ==
    /\ writers \subseteq Actors
    /\ counter \in Nat

ReadyToWrite(writer) ==
    /\ writer \notin DOMAIN writers
    /\ counter < 5
    /\ writers' = writers \cup {writer}
    /\ UNCHANGED counter

Write(writer) ==
    /\ writer \in DOMAIN writers
    /\ counter' = counter + 1
    /\ writers' = writers \ {writer}

Init ==
    /\ writers  = {}
    /\ counter  = 0
Next == \E writer \in Writers : ReadyToWrite(actor) \/ Write(actor)
Spec == Init /\ [][Next]_vars

CounterIsAlwaysBellow5 == [](counter < 5)

(* 
    PUT this into the .cfg file:
    CONSTANTS NumWriters = 2
    SPECIFICATION Spec
    PROPERTIES CounterIsAlwaysBellow5
*)
============================================================================