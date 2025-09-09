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

AcceptorRecord ==
    [maxBallot1A: Nat, maxBallot2A: Nat, value: Values \cup {NoValue}]

\* Type safety.
TypeInv ==
    /\ network \subseteq
        [type: {"1A"}, src: Proposers, dst: Acceptors, ballot: Nat] \cup
        [type: {"1B"}, src: Acceptors, dst: Proposers, record: AcceptorRecord] \cup
        [type: {"2A"}, src: Proposers, dst: Acceptors, ballot: Nat, value: Values] \cup
        [type: {"2B"}, src: Acceptors, dst: Proposers, record: AcceptorRecord]
    /\ prState \in [Proposers -> Values \cup {NoValue}]
    /\ acState \in [Acceptors -> AcceptorRecord]
    /\ ballotGen \in Nat

(*************************************************************************************************)
\* Custom Actions.

Phase1A(p) ==
    /\ prState[p] = NoValue
    /\ network' = network \cup {[
        type    |-> "1A",
        src     |-> p,
        dst     |-> a,
        ballot  |-> ballotGen + 1]: a \in Acceptors}
    /\ ballotGen' = ballotGen + 1
    /\ UNCHANGED <<prState, acState>>

Phase1B(a) == \E msg \in network:
    /\ msg.type = "1A"
    /\ msg.dst = a
    /\ msg.ballot > acState[a].maxBallot1A
    /\ acState' = [acState EXCEPT ![a].maxBallot1A = msg.ballot]
    /\ network' = (network \ {msg}) \cup {[
        type    |-> "1B",
        src     |-> a,
        dst     |-> msg.src,
        record  |-> acState'[a]]}
    /\ UNCHANGED <<prState, ballotGen>>

---------------------------------------------------------------------------------------------------

SmallestMajoritySize == (Cardinality(Acceptors) \div 2) + 1

\* Helper operator to find the highest 2A ballot from a set of 1B messages
HighestBallot2A(msgs) ==
    LET ballots2A == {m.record.maxBallot2A : m \in msgs}
    IN CHOOSE ballot \in ballots2A :
        \A other \in ballots2A : ballot >= other

\* Helper operator to determine the value to propose
ValueToPropose(msgsForBallot) ==
    LET highestBallot2A == HighestBallot2A(msgsForBallot)
    IN IF highestBallot2A = 0
        THEN CHOOSE v \in Values : TRUE
        ELSE (CHOOSE m \in msgsForBallot : m.record.maxBallot2A = highestBallot2A).record.value

Phase2A(p) ==
    LET phase1BMessages == {m \in network : m.type = "1B" /\ m.dst = p}
        availableBallots == {m.record.maxBallot1A : m \in phase1BMessages}
    IN \E selectedBallot \in availableBallots :
        LET msgsForBallot == {m \in phase1BMessages : m.record.maxBallot1A = selectedBallot}
            respondingAcceptors == {m.src : m \in msgsForBallot}
            proposedValue == ValueToPropose(msgsForBallot)
        IN /\ Cardinality(msgsForBallot) >= SmallestMajoritySize
            /\ network' = (network \ msgsForBallot) \cup {[
                type    |-> "2A",
                src     |-> p,
                dst     |-> a,
                ballot  |-> selectedBallot,
                value   |-> proposedValue] : a \in respondingAcceptors}
            /\ UNCHANGED <<prState, acState, ballotGen>>

---------------------------------------------------------------------------------------------------

Phase2B(a) == \E msg \in network:
    /\ msg.type = "2A"
    /\ msg.dst = a
    /\ acState[a].maxBallot1A = msg.ballot
    /\ acState' = [acState EXCEPT
        ![a].maxBallot2A = msg.ballot,
        ![a].value = msg.value]
    /\ network' = (network \ {msg}) \cup {[
        type    |-> "2B",
        src     |-> a,
        dst     |-> msg.src,
        record  |-> acState'[a]]}
    /\ UNCHANGED <<prState, ballotGen>>

Phase3(p) ==
    LET phase2BMessages == {m \in network : m.type = "2B" /\ m.dst = p}
        availableBallots == {m.record.maxBallot1A : m \in phase2BMessages}
    IN \E selectedBallot \in availableBallots :
        LET msgsForBallot == {m \in phase2BMessages : m.record.maxBallot1A = selectedBallot}
            respondingAcceptors == {m.src : m \in msgsForBallot}
        IN  /\ Cardinality(msgsForBallot) >= SmallestMajoritySize
            /\ prState' = [prState EXCEPT ![p] = (CHOOSE m \in msgsForBallot : TRUE).record.value]
            /\ UNCHANGED <<network, acState, ballotGen>>

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
Constraint == ballotGen < 4

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