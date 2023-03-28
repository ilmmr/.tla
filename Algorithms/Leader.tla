--------------------------- MODULE Leader -------------------------
LOCAL INSTANCE Naturals
LOCAL INSTANCE FiniteSets
Range(f) == { f[x] : x \in DOMAIN f }

\* @type: Nat;
CONSTANT NumberOfNodes

\* @type: Set(Nat);
Nodes == 1..NumberOfNodes
\* @type: Nat -> Nat;
Successor  ==   [ id \in Nodes |->  CASE id = NumberOfNodes -> 1
                                    [] OTHER -> id + 1 
                ]

VARIABLES   
            \* @type: Nat -> Set(Nat);
            inbox,
            \* @type: Nat -> Set(Nat);
            outbox
-------------------------------------------------------------------

===================================================================