---------------------- MODULE BankAccount ----------------------- 
(****************************************************************)
(* The Bank Account Transfer Problem: From one account to other *)
EXTENDS TLC, FiniteSets, Naturals

CONSTANT 
        \* @type: Set(Str);
        Users,
        \* @type: Set(Nat);
        Accounts
\* Accounts are a Set of Nats (> 0) that represent their Id.
\* One could create sep the accounts id by adding an action.
ASSUME  /\ Accounts \subseteq Nat \ {0}

VARIABLE
        \* @type: Seq(Int);
        balance,
        \* @type: Str -> (Nat \X Int);
        terminal
vars == << balance, terminal >>

\* @type: f -> DOMAIN f^-1;
CODOMAIN(func) == {func[p] : p \in DOMAIN func}
TypeInvariant ==    /\ DOMAIN balance \in Accounts
                    /\ DOMAIN terminal \in Users

access(user, account) == 
        LET
            current_balance == balance[account] 
        IN
        \* pre-conditions.
        /\ user \notin DOMAIN terminal
        \* --------------
        /\ terminal' = terminal @@ user :> << account, current_balance >>
        /\ UNCHANGED balance
terminate(user, account)   == 
        LET 
            login == terminal[user]
        IN
            \* pre-conditions.
            /\ 
                /\ account = login[1]
                /\ user \in DOMAIN terminal
            \* --------------
            /\ balance'   = [balance EXCEPT ![login[1]] = login[2]]
            /\ terminal'  = [terminal EXCEPT ![user] = << 0,0 >>]
increment(user, account) == 
        /\ terminal' = [terminal EXCEPT ![user].balance = @ + 1]
        /\ UNCHANGED balance
decrement(user, account) ==  
        /\ terminal' = [terminal EXCEPT ![user].balance = @ - 1]
        /\ UNCHANGED balance

Init    ==  /\ terminal = [u \in Users |-> << 0,0 >>]
            \* This will create a sequence of integers, as accounts are accounted as Nat.
            /\ balance = [a \in Accounts |-> 0]

Next    == \E u \in Users: \E a \in Accounts:
                \/ access(u, a)
                \/ terminate(u, a)
                \/ increment(u, a)
                \/ decrement(u, a)

Spec    == Init /\ [][Next]_vars

BalanceInvariance   == [](\A u \in DOMAIN terminal: \A a \in terminal[u]: terminal[u][2] = balance[a])

(*  FIXING THIS:
        -> Adding a locker upon accessing.
        -> Restrict the operations for incrementing and decrementing.
*)
===============================================================