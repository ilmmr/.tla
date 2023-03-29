-------------------------- MODULE TheKnightsQuest --------------------------- 
(***************************************************************************)
EXTENDS Naturals, FiniteSets, TLC

(* As a constant we get the size of the border                             *)
CONSTANT 
    \* @type: Nat;
    N

(* As a variable, we define which positions have occupied yet.             *)
(* And the current position of the knight                                  *)
VARIABLE
        \* @type: Set(Seq(Nat)); 
        occupied, 
        \* @type: Set(Nat);
        current
vars    == << occupied, current >>

\* @type: Set(Nat);
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
(* 
    -> Before I had \E, I've used CHOOSE to select an arbitrary value from S.
    However, as I was having stalling issues, which is the CHOOSE was always returning the same value, to
    an arbitray input i.

    That is because CHOOSE is a function that returns an arbitrary value fulfilling the specified criteria. 
    But because it's a function it always returns the same value for the same expression. 

    See more at https://stackoverflow.com/questions/75684906/tla-spec-stalls-as-choose-does-not-select-a-previous-selected-value
*)
Next == LET S == Jumps(current) 
        IN \E Chosen \in S:
            /\ current'  = Chosen
            /\ occupied' = occupied \cup {Chosen}
(* However, this take a lot of time to perform, as N could be large. *)

Spec      == Init /\ [][Next]_vars
FairSpec  == Spec /\ WF_occupied(Next)
NotSolved == Cardinality(occupied) < (N-1)^2

(*
    Nevertheless, the current description does allow for a path where the same element of S is chosen over and over again. 
    You can prevent that by adding /\ ~(Chosen \in occupied) as a conjunct. 
    But that also means at some point you will have exhausted S and your algorithm will stall which you need to take into account.
*)
=============================================================================