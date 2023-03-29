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
LOCAL INSTANCE Naturals
LOCAL INSTANCE FiniteSets

CONSTANT
        \* @type: Nat; 
        NumberOfBeans

ASSUME NumberOfBeans \in Nat \ {0}

VARIABLES 
    \* @type: Seq(Nat); 
    can
----------------------------------------------------------------------





======================================================================