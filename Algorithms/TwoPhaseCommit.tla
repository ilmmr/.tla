---------------------------- MODULE TwoPhaseCommit -------------------------- 
CONSTANT
    \* @type: Set(Nat); 
    Participant

VARIABLES
    \* @type: Nat -> Str;
    pState,    (* the state of each participant *)
    \* @type: Str;
    mState,    (* the state of the manager *)
    \* @type: Set(Nat);
    pPrepared, (* which participants are prepared *)
    \* @type: Set({type: Set(Str), participant?: Set(Nat)});
    msgs       (* the set of messages interchaged *)

vars    == << pState, mState, pPrepared, msgs >> 
Message == [type : {"Prepared"}, participant : Participant]  \cup  [type : {"Commit", "Abort"}]

-----------------------------------------------------------------------------
(******************** ACTIONS FROM THE COMMIT MANAGER **********************)
TMRcvPrepared(p) ==
  /\ mState = "init"
  /\ [type |-> "Prepared", participant |-> p] \in msgs
  /\ pPrepared' = pPrepared \cup {Participant}
  /\ UNCHANGED <<pState, mState, msgs>>

TMCommit ==
  /\ mState = "init"
  /\ pPrepared = Participant \* Can only commit when every Participant is prepared
  /\ mState' = "committed"
  /\ msgs' = msgs \cup {[type |-> "Commit"]}
  /\ UNCHANGED <<pState, pPrepared>>

TMAbort ==
  /\ mState = "init"
  /\ mState' = "aborted"
  /\ msgs' = msgs \cup {[type |-> "Abort"]}
  /\ UNCHANGED <<pState, pPrepared>>

-----------------------------------------------------------------------------
(********************  ACTIONS FROM EACH PARTICIPANT  **********************)
ParticipantPrepare(p) == 
  /\ pState[p] = "working"
  /\ pState' = [pState EXCEPT ![p] = "prepared"]
  /\ msgs' = msgs \cup {[type |-> "Prepared", participant |-> p]}
  /\ UNCHANGED <<mState, pPrepared>>
  
ParticipantChooseToAbort(p) ==
  /\ pState[p] = "working"
  /\ pState' = [pState EXCEPT ![p] = "aborted"]
  /\ UNCHANGED <<mState, pPrepared, msgs>>

ParticipantRcvCommitMsg(p) ==
  /\ [type |-> "Commit"] \in msgs
  /\ pState' = [pState EXCEPT ![p] = "committed"]
  /\ UNCHANGED <<mState, pPrepared, msgs>>

ParticipantRcvAbortMsg(p) ==
  /\ [type |-> "Abort"] \in msgs
  /\ pState' = [pState EXCEPT ![p] = "aborted"]
  /\ UNCHANGED <<mState, pPrepared, msgs>>

-----------------------------------------------------------------------------
TPInit ==   
  /\ pState    = [p \in Participant |-> "working"]
  /\ mState    = "init"
  /\ pPrepared = {}
  /\ msgs      = {}

TPNext ==
  \/ TMCommit \/ TMAbort
  \/ \E p \in Participant : 
       TMRcvPrepared(p) \/ ParticipantPrepare(p) \/ ParticipantChooseToAbort(p)
         \/ ParticipantRcvCommitMsg(p) \/ ParticipantRcvAbortMsg(p)

TPSpec == TPInit /\ [][TPNext]_vars

-----------------------------------------------------------------------------
TPTypeOK ==  
  (*************************************************************************)
  (* The type-correctness invariant                                        *)
  (*************************************************************************)
  /\ pState \in [Participant -> {"working", "prepared", "committed", "aborted"}]
  /\ mState \in {"init", "committed", "aborted"}
  /\ pPrepared \subseteq Participant
  /\ msgs \subseteq Message

THEOREM TPSpec => []TPTypeOK
(*************************************************************************)
(* This theorem asserts that the type-correctness predicate TPTypeOK is  *)
(* an invariant of the specification.                                    *)
(*************************************************************************)
-----------------------------------------------------------------------------
TC == INSTANCE TransitionCommit 

THEOREM TPSpec => TC!Spec
(*************************************************************************)
(* This theorem asserts that the specification TPSpec of the Two-Phase   *)
(* Commit protocol implements the specification Spec of the              *)
(* Transaction Commit protocol.                                          *)
(*************************************************************************)
=============================================================================