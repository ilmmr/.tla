---------------------- MODULE BankAccount ----------------------- 
(****************************************************************)
(* The Bank Account Transfer Problem: From one account to other *)
EXTENDS TLC, FiniteSets, Naturals

CONSTANT 
        \* @type: Set(Str);
        Users,
        \* @type: Set(Int);
        Accounts

\* Accounts are a Set of Ints that represent their Id.
\* One could create sep the accounts id by adding an action.
VARIABLE
        \* @type: Int -> Int;
        balance,
        \* @type: Str -> (Int \X Int);
        terminal
vars == << balance, terminal >>

\* @type: f -> DOMAIN f^-1;
CODOMAIN(func) == {func[p] : p \in DOMAIN func}
TypeInvariant ==    /\ DOMAIN balance \in Accounts
                    /\ CODOMAIN(balance) \in Int
                    /\ DOMAIN terminal \in Users

login(user, account) == 
        \* pre-conditions.
        /\ user \notin DOMAIN terminal
        \* --------------
        /\ terminal' = terminal @@ user :> << account, 0 >>
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
            /\ terminal'  = [u \in DOMAIN terminal \ {user} |-> terminal[u]]
increment(user, account) == 
        /\ terminal' = [terminal EXCEPT ![user].balance = @ + 1]
        /\ UNCHANGED balance
decrement(user, account) ==  
        /\ terminal' = [terminal EXCEPT ![user].balance = @ + 1]
        /\ UNCHANGED balance

Next    == \E u \in Users: \E a \in Accounts:
                \/ login(u, a)
                \/ terminate(u, a)
                \/ increment(u, a)
                \/ decrement(u, a)

Init    == /\ terminal = {}
           /\ balance = [Accounts -> 0]
Spec    == Init /\ [][Next]_vars
===============================================================