---------------------- MODULE GameOfLife ---------------------- 
(*************************************************************)

EXTENDS TLC, FiniteSets, Naturals
\* @type: Nat;
CONSTANT N
ASSUME   N \in Nat \ {0}

VARIABLE
        \* @type: Seq(Nat) -> Boolean;
        status

\* @type: Set(Seq(Nat));
POSGRID == {<< x, y >> : x, y \in 1..N}
\* @type: f -> DOMAIN f^-1;
CODOMAIN(func) == {func[p] : p \in DOMAIN func}
\* @type: Set(Nat);
RANGE == 1..N

\* @type: Seq(Nat) -> Nat;
Neighbours(cell) == LET x == cell[1]
                        y == cell[2]
                        S == (UNION {{<< x+pX, y+pY >>, << x-pX, x-pY>>} \ {<<x,y>>} : pX, pY \in {0, 1}}) \intersect (RANGE \X RANGE)
                    IN
                        Cardinality({c \in S : status[c] = TRUE})
                        
Init    ==  status \in [POSGRID -> BOOLEAN]
Next    ==  LET revive(cell)  == ~status[cell] /\ Neighbours(cell) = 3
                survive(cell) ==  status[cell] /\ Neighbours(cell) \in {2, 3}
            IN  status' =   [ p \in POSGRID |-> CASE revive(p) \/ survive(p)    -> TRUE
                                                [] OTHER                        -> FALSE
                            ]

Spec    == Init /\ [][Next]_status

\* It implictly checks for deadlock.
===============================================================