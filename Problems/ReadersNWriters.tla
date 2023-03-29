-------------------------- MODULE ReadersNWriters --------------------------
(**************************************************************************)
(* A specification of the readers and writers problem, a common computing *)
(* problem in concurrency.                                                *)
(* https://en.wikipedia.org/wiki/Readers%E2%80%93writers_problem          *)
(**************************************************************************)
EXTENDS FiniteSets, Naturals, Sequences, TLC

\* @type: Nat;
CONSTANT NumActors

VARIABLES
    \* @type: Set(Nat);
    readers, \* set of processes currently reading
    \* @type: Set(Nat);
    writers, \* set of processes currently writing
    \* @type: Seq(Nat);
    waiting  \* queue of processes waiting to access the resource
vars == <<readers, writers, waiting>>

Actors == 1..NumActors

(* Manipulate waiting queue *)
ToSet(s)       == { s[i] : i \in DOMAIN s }
WaitingToRead  == { p[2] : p \in ToSet(SelectSeq(waiting, LAMBDA s : s[1] = "read" )) }
WaitingToWrite == { p[2] : p \in ToSet(SelectSeq(waiting, LAMBDA s : s[1] = "write")) }

(* Actions *)
TryRead(actor) ==
    /\ actor \notin WaitingToRead
    /\ waiting' = Append(waiting, <<"read", actor>>)
    /\ UNCHANGED <<readers, writers>>

TryWrite(actor) ==
    /\ actor \notin WaitingToWrite
    /\ waiting' = Append(waiting, <<"write", actor>>)
    /\ UNCHANGED <<readers, writers>>

(* The following actions are executed upon: 
    -> An element in a queue is read;
    which means, that the waiting' will be set as 
    the tail of the current waiting list.
*)
Read(actor) ==
    /\ readers' = readers \cup {actor}
    /\ waiting' = Tail(waiting)
    /\ UNCHANGED writers

Write(actor) ==
    (* can only write when there are no readers *)
    /\ readers = {}
    /\ writers' = writers \cup {actor}
    /\ waiting' = Tail(waiting)
    /\ UNCHANGED readers

ReadOrWrite ==
    /\ waiting /= <<>>
    /\ writers = {}
    /\ LET pair   == Head(waiting)
           action == pair[1]
           actor  == pair[2]
       IN CASE action = "read"  -> Read(actor)
            [] action = "write" -> Write(actor)

StopActivity(actor) ==
    IF actor \in readers
    THEN /\ readers' = readers \ {actor}
         /\ UNCHANGED <<writers, waiting>>
    ELSE /\ writers' = writers \ {actor}
         /\ UNCHANGED <<readers, waiting>>

Stop == \E actor \in readers \cup writers : StopActivity(actor)

Init ==
    /\ readers = {}
    /\ writers = {}
    /\ waiting = <<>>

Next ==
    \/ \E actor \in Actors : TryRead(actor)
    \/ \E actor \in Actors : TryWrite(actor)
    \/ ReadOrWrite
    \/ Stop

Fairness ==
    /\ \A actor \in Actors : WF_vars(TryRead(actor))
    /\ \A actor \in Actors : WF_vars(TryWrite(actor))
    /\ WF_vars(ReadOrWrite)
    /\ WF_vars(Stop)

Spec == Init /\ [][Next]_vars /\ Fairness

(* Invariants *)
(* REMEMBER: All invariants are safety properties, but not all safety properties are invariants. *)
TypeInvariant ==
    /\ readers \subseteq Actors
    /\ writers \subseteq Actors
    /\ waiting \in Seq({"read", "write"} \times Actors)

Safety ==
    /\ Cardinality(writers) <= 1

(* Properties *)
Liveness ==
    /\ \A actor \in Actors : []<>(actor \in readers)
    /\ \A actor \in Actors : []<>(actor \in writers)
    /\ \A actor \in Actors : []<>(actor \notin readers)
    /\ \A actor \in Actors : []<>(actor \notin writers)

THEOREM Spec => []TypeInvariant
THEOREM Spec => []Safety
(* 
    PUT this into the .cfg file:
    CONSTANTS NumActors = 2
    SPECIFICATION Spec
    INVARIANTS TypeOK Safety
    PROPERTIES Liveness
*)
============================================================================