--------------------------- MODULE CoffeeCan -------------------------
(*
    . You are initially given a coffee can that contains some black beans 
    and some white beans and a large pile of “extra” black beans. 
    You then repeat the following process until 
    there is a single bean left in the can.

    . Randomly select two beans from the can. 
    If they are the same color, 
    throw them both out and insert an extra black bean. 
    If they are different colors, 
    return the white bean to the can and throw out the black.

*)
EXTENDS TLC
LOCAL INSTANCE Naturals
LOCAL INSTANCE FiniteSets

CONSTANT
        \* @type: Nat; 
        NumberOfBeans

ASSUME  /\ NumberOfBeans \in Nat \ {0}
        \* redundant
        /\ NumberOfBeans >= 1

VARIABLES 
    \* @type: Seq(Nat); 
    can

\* It either picks 2 black beans or 2 white beans.
SameColor ==    \/
                    /\ can[1] >= 2
                    /\ can' = [can EXCEPT ![1] = @ - 1]
                \/
                    /\ can[2] >= 2
                    /\ can' = [can EXCEPT ![2] = @ - 2, ![1] = @ + 1]

\* It has no other choice than picking a black and a white.
DifferentColor ==   /\ can[1] >= 1 
                    /\ can[2] >= 1
                    /\ can' = [can EXCEPT ![1] = @ - 1]

\* It terminates.
BeanCount      ==   can[1] + can[2]
OneBeanLeft    ==   /\ can[1] + can[2] = 1
                    /\ UNCHANGED can

----------------------------------------------------------------------

Init == can \in {<<x, y>> : x \in 1..NumberOfBeans, y \in 1..NumberOfBeans}
Next == \/
            /\  BeanCount >= 2
            /\
                \/ SameColor
                \/ DifferentColor
        \/ OneBeanLeft

Spec == /\ Init
        /\ [][Next]_can
        /\ WF_can(Next)
        /\ WF_can(OneBeanLeft)  \* also redundant because SameColor and DifferentColor 
                                \* cannot execute if OneBeanLeft is continuously ENABLED.

TypeInvariant == /\ can[1] \in 0..NumberOfBeans
                 /\ can[2] \in 0..NumberOfBeans
                 /\ \A i \in DOMAIN can : can[i] \in 0..NumberOfBeans
\* It terminates eventually.
ItTerminates  == <> (ENABLED OneBeanLeft)
\* The number of beans can only decrease.
BeansDecrease == [][BeanCount' < BeanCount]_can
\* Every step preserves the parity of the number of white beans (either odd or even).
WhiteBeansPar == [][can[2] % 2 = can'[2] % 2]_can
THEOREM Spec => TypeInvariant
======================================================================