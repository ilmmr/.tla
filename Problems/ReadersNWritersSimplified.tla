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
    /\ writers \subseteq Writers
    /\ counter \in Nat

ReadyToWrite(writer) ==
    /\ writer \notin writers
    /\ counter < 5
    /\ writers' = writers \cup {writer}
    /\ UNCHANGED counter

Write(writer) ==
    /\ writer \in writers
    /\ counter' = counter + 1
    /\ writers' = writers \ {writer}

Init ==
    /\ writers  = {}
    /\ counter  = 0
Next == \E writer \in Writers : ReadyToWrite(writer) \/ Write(writer)
Spec == Init /\ [][Next]_vars

CounterIsAlwaysBellow5 == (counter <= 5)
NoTwoWriters == \/ writers = {}  (* No writer is writing *)
                \/ \E w \in writers: writers = {w}  (* At most one writer is writing *)

THEOREM CounterBellow5Theorem   == Spec => []CounterIsAlwaysBellow5
THEOREM NoTwoWritersTheorem     == Spec => []NoTwoWriters
(* 
    PUT this into the .cfg file:
    CONSTANTS NumWriters = 2
    SPECIFICATION Spec
    INVARIANTS CounterIsAlwaysBellow5 NoTwoWriters
*)
============================================================================