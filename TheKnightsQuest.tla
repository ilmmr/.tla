-------------------------- MODULE TheKnightsQuest --------------------------- 
(***************************************************************************)
EXTENDS Naturals, FiniteSets, TLC, Functions

(* As a constant we get the size of the border                             *)
CONSTANT N
(* As a variable, we define which positions have occupied yet.             *)
(* And the current position of the knight                                  *)
VARIABLE occupied, current
vars    == << occupied, current >>

Possible == 0..N-1

Inv    == /\ Cardinality(occupied) \leq N^2
          /\ IsFiniteSet(occupied)
          /\ occupied \subseteq (Possible \X Possible)

Jumps(pair) == LET x == pair[1]
                   y == pair[2] 
                IN 
                ({<<x+2, y-1>>, <<x+2, y+1>>, <<x-2,y+1>>, <<x-2,y-1>>}
                    \cup
                 {<<x+1, y-2>>, <<x+1, y+2>>, <<x-1,y+2>>, <<x-1,y-2>>}
                ) 
                    \cap 
                (Possible \X Possible)

Init == \E x \in Possible     : \E y \in Possible : /\ occupied = {<<x,y>>}
                                                    /\ current  = <<x,y>>

Next == LET S == Jumps(current) 
            Chosen == CHOOSE s \in S: TRUE
        IN
            /\ current'  = Chosen
            /\ occupied' = occupied \cup {Chosen}


Spec      == Init /\ [][Next]_vars
FairSpec  == Spec /\ WF_occupied(Next)
NotSolved == Cardinality(occupied) < 8

(*
    Slice == {{<< xt[n], yt[n] >>:  n \in Dom}:
              << xt, yt >> \in [Dom -> X] \X Bijection(Dom, Y)}
*)
=============================================================================