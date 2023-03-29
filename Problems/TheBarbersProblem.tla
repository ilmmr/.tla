------------------------- MODULE TheBarbersProblem -------------------------
(**************************************************************************)
(* A specification of the spleeping barbers problem, a common computing   *)
(* problem in inter-processing and synchronizatio.                        *)
(* https://en.wikipedia.org/wiki/Sleeping_barber_problem                  *)
(**************************************************************************)

(*
    - If there are no customers, the barber falls asleep in the chair
    - A customer must wake the barber if he is asleep
    - If a customer arrives while the barber is working, the customer leaves if all chairs are occupied and sits in an empty chair if it's available
    - When the barber finishes a haircut, he inspects the waiting room to see if there are any waiting customers and falls asleep if there are none
*)

LOCAL INSTANCE Naturals
LOCAL INSTANCE FiniteSets
LOCAL INSTANCE Functions

\* @type: Nat;
CONSTANT NumberOfChairs

VARIABLES   
            \* @type: Bool;
            barber,
            \* @type: Bool;
            goingToSleep,
            \* @type: Bool;
            goingToSit,
            \* @type: Nat -> Bool;
            chairs

(*
    The goingToSleep and the goingToSit variables
    are actually apart of critical area that needs a lock:
        -> When the barber acknowledges that he can go to sleep...
    Since a customer can sit after checking the barber is working, but the barber finishes
    , checks the waiting room and goes to sleep.
*)

ASSUME /\ NumberOfChairs \in Nat

EmptyChairs     == TRUE \notin Range(chairs)
ChairEmpty      == CHOOSE c \in 1..NumberOfChairs : chairs[c] = FALSE
BarberIsWorking == barber = TRUE

BarberGoesToSleep   ==  /\ goingToSleep = TRUE
                        /\ barber'      = FALSE
                        /\ goingToSleep' = FALSE
                        /\ UNCHANGED << chairs, goingToSit >>

BarberStopAndChecks ==  /\ BarberIsWorking
                        /\ \/ 
                                /\ EmptyChairs
                                /\ goingToSleep' = TRUE
                                /\ UNCHANGED << chairs, barber, goingToSit >>
                            \/
                                \E cust \in DOMAIN chairs : 
                                    /\ chairs[cust] = TRUE
                                    /\ chairs' = [chairs EXCEPT ![cust]=FALSE]
                                    /\ UNCHANGED << barber, goingToSleep, goingToSit >>
                            \/ UNCHANGED << barber, chairs, goingToSleep, goingToSit >>

Barber              == \/ BarberGoesToSleep
                       \/ BarberStopAndChecks

ChecksBarber        == /\ BarberIsWorking
                       /\ goingToSit' = TRUE
                       /\ UNCHANGED << chairs, barber, goingToSleep >>

CustomerWakesBarber == /\ ~BarberIsWorking
                       /\ EmptyChairs
                       /\ barber' = TRUE
                       /\ UNCHANGED << chairs, goingToSit, goingToSleep >>

CustomerSits        == /\ FALSE \in Range(chairs) /\ goingToSit
                       /\ chairs' = [chairs EXCEPT ![ChairEmpty] = TRUE]
                       /\ goingToSit' = FALSE
                       /\ UNCHANGED << barber, goingToSleep >>
    
CustomerLeaves      == /\ FALSE \notin Range(chairs) /\ BarberIsWorking
                       /\ goingToSit /\ goingToSit' = FALSE
                       /\ UNCHANGED << barber, chairs, goingToSleep >>

Customer            == \/ CustomerWakesBarber
                       \/ CustomerLeaves
                       \/ CustomerSits 
                       \/ ChecksBarber

--------------------------------------------------------------------------
Next                ==  \/ Customer
                        \/ Barber

Init                ==  /\ barber
                        /\ chairs = [n \in 1..NumberOfChairs |-> FALSE]
                        /\ goingToSit = FALSE /\ goingToSleep = FALSE

Spec                ==  /\ Init 
                        /\ [][Next]_<<barber, chairs, goingToSit, goingToSleep>>
                        /\ WF_<<barber, chairs, goingToSit, goingToSleep>>(Next)

TypeInvariant       == /\ chairs \in [1..NumberOfChairs -> BOOLEAN]
                       /\ barber \in BOOLEAN 

WillEmptyChairs == []<>(EmptyChairs)
NotWork         == (~BarberIsWorking) => EmptyChairs
THEOREM Spec => []TypeInvariant

(* 
    TheBarbersProblem.cfg FILE :
        CONSTANT NumberOfChairs = 3
        SPECIFICATION Spec
        INVARIANT TypeInvariant
*)
==========================================================================