------------------------------------------ MODULE Paxos -------------------------------------------
EXTENDS Integers, FiniteSets, TLC

\* Constants come from the .cfg file.
CONSTANTS Proposers, Acceptors, Values

\* Quantity to denote the absence of a value.
NoValue == 0

\* TLC will verify these assumptions.
ASSUME
    /\ IsFiniteSet(Proposers)
    /\ IsFiniteSet(Acceptors)
    /\ IsFiniteSet(Values)
    /\ NoValue \notin Values

\* Variables are initialized in the Init formula.
VARIABLES
    network,    \* Set to contain all messages in transit.
    prState,    \* Mapping of a Proposer to the value it thinks has been chosen.
    acState,    \* Mapping of an Acceptor to its state.
    ballotGen   \* Counter to generate ballots.

vars == <<network, prState, acState, ballotGen>>

\* Type safety.
TypeInv == TRUE

(*************************************************************************************************)
\* Custom Actions.

Phase1A(p) == FALSE
Phase1B(a) == FALSE
Phase2A(p) == FALSE
Phase2B(p) == FALSE
Phase3(p) == FALSE

(*************************************************************************************************)
\* System Actions.

Init ==
    /\ network = {}
    /\ prState = [p \in Proposers |-> NoValue]
    /\ acState = [a \in Acceptors |-> [maxBallot1A |-> 0, maxBallot2A |-> 0, value |-> NoValue]]
    /\ ballotGen = 0

Next ==
    \/ \E p \in Proposers:
        \/ Phase1A(p)
        \/ Phase2A(p)
        \/ Phase3(p)
    \/ \E a \in Acceptors:
        \/ Phase1B(a)
        \/ Phase2B(a)

(*************************************************************************************************)

\* Algorithm safety.
SafetyInv ==
    \* All proposers end up on the same value.
    /\ \A p1, p2 \in Proposers: (prState[p1] # NoValue /\ prState[p2] # NoValue)
        => prState[p1] = prState[p2]
    \* Same 2A ballot means the same value.
    /\ \A a1, a2 \in Acceptors: (acState[a1].maxBallot2A = acState[a2].maxBallot2A)
        => acState[a1].value = acState[a2].value

\* Algorithm liveness - Eventually all proposers agree on the same value and then keep agreeing.
Liveness == <>[](\A p1, p2 \in Proposers:
    /\ prState[p1] # NoValue
    /\ prState[p2] # NoValue
    /\ prState[p1] = prState[p2])

\* Contraint to limit state space.
Constraint == ballotGen < 5

(* Temporal formula of the spec. *)
Spec == /\ Init
        /\ [][Next]_vars
        \* NOTE: As per my understanding, a fairness condition on Phase1A shouldn't be required.
        \* But without it, the system starts stuttering just after the initial state.
        /\ WF_vars(\E p \in Proposers: Phase1A(p))
        /\ WF_vars(\E p \in Proposers: Phase2A(p))
        /\ WF_vars(\E p \in Proposers: Phase3(p))
        /\ WF_vars(\E a \in Acceptors: Phase1B(a))
        /\ WF_vars(\E a \in Acceptors: Phase2B(a))

\* Invariants should always hold.
THEOREM Spec => []TypeInv
THEOREM Spec => []SafetyInv

===================================================================================================