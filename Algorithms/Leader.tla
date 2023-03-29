--------------------------- MODULE Leader -------------------------
EXTENDS TLC
LOCAL INSTANCE Naturals
LOCAL INSTANCE FiniteSets

\* @type: Nat;
CONSTANT NumberOfNodes

\* @type: Set(Nat);
Nodes == 1..NumberOfNodes
\* @type: Nat -> Nat;
Successor  ==   [ id \in Nodes |->  CASE id = NumberOfNodes -> 1
                                    [] OTHER -> id + 1 
                ]

ASSUME  /\ NumberOfNodes \in Nat
        /\ Successor \in [Nodes -> Nodes]
        /\ Nodes \intersect {n \in Nat : n = 0 \/ n \geq NumberOfNodes+1} = {}

VARIABLES    
            \* @type: Nat -> Set(Nat);
            inbox,
            \* @type: Nat -> Set(Nat);
            outbox
-------------------------------------------------------------------
Elected    == {node \in Nodes : node \in inbox[node]}

Send(node) == LET 
                succ == Successor[node]
              IN
                \E id \in outbox[node] :
                    /\ inbox'  = [inbox  EXCEPT ![succ] = @ \cup {id}]
                    /\ outbox' = [outbox EXCEPT ![node] = @ \ {id}] 

Comp(node) == \E id \in inbox[node] :
                    /\ id \geq node \* this prevents from being more than 1 elected
                    /\ outbox' = [outbox EXCEPT ![node] = @ \cup {id}]
                    /\ inbox'  = [inbox  EXCEPT ![node] = @ \ {id}]

DetectElected == /\ Elected # {}
                 /\ UNCHANGED << inbox, outbox >>

Init == /\ inbox  = [id \in Nodes |-> {}]
        /\ outbox = [id \in Nodes |-> {id}]

Next == \E node \in Nodes : 
                            \/ Comp(node)
                            \/ Send(node)

Spec == /\ Init 
        /\ [][Next]_<<inbox,outbox>> 
        /\ WF_<<inbox,outbox>>(DetectElected)

TypeInvariant       == /\ inbox  \in [Nodes -> SUBSET Nodes]
                       /\ outbox \in [Nodes -> SUBSET Nodes]
NeverElected        == Elected = {} \* counter-example : 1 is selected
Safety              == Cardinality(Elected) \in {0,1}

THEOREM Spec => []TypeInvariant
===================================================================