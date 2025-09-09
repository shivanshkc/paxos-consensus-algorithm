# Paxos Consensus Algorithm

A comprehensive implementation and formal verification project for the Paxos consensus algorithm. This repository contains TLA+ specifications for formal verification of the Paxos protocol, with plans to include code implementations in the future.

## Overview

Paxos is a consensus algorithm designed to achieve agreement among distributed nodes in an unreliable network. This project provides:

- **Formal Specification**: Complete TLA+ specification of the Paxos algorithm with safety and liveness properties
- **Model Checking**: Automated verification of correctness properties using TLC (TLA+ model checker)
- **Future Implementation**: Code implementations of the algorithm (planned)

## Project Structure

```
├── specifications/
│   └── Paxos/                 # Main Paxos specification
│       ├── Paxos.tla         # TLA+ specification file
│       └── Paxos.cfg         # Configuration file for model checking
└── README.md
```

## The Paxos Algorithm

The TLA+ specification implements the classic Paxos consensus algorithm with three phases:

1. **Phase 1A (Prepare)**: Proposers send prepare requests with ballot numbers
2. **Phase 1B (Promise)**: Acceptors respond with promises not to accept lower-numbered proposals
3. **Phase 2A (Accept)**: Proposers send accept requests with chosen values
4. **Phase 2B (Accepted)**: Acceptors accept proposals and notify proposers
5. **Phase 3 (Learn)**: Proposers learn when a value has been chosen by a majority

### Safety Properties

- **Agreement**: All proposers that decide on a value decide on the same value
- **Validity**: Any decided value was proposed by some proposer
- **Consistency**: Acceptors with the same ballot number accept the same value

### Liveness Properties

- **Termination**: Eventually all proposers agree on the same value (under fairness conditions)

## Usage

### Prerequisites

Before running TLA+ model checking, you need to download the TLA+ tools JAR file:

1. **Download tla2tools.jar**:
   - Visit the [TLA+ tools releases page](https://github.com/tlaplus/tlaplus/releases)
   - Download the latest `tla2tools.jar` file from the most recent release (v1.7.4 at the time of writing).
   - Place the downloaded file in the `specifications/` directory of this project

2. **Verify the setup**:
   ```bash
   java -jar specifications/tla2tools.jar
   ```

### Running Model Checking

### 1. Exhaustive Model Checking

Run complete state space exploration (remember constraints for infinite state spaces):

```bash
java -Xms42G -Xmx42G -jar specifications/tla2tools.jar \
  -seed 0 \
  -workers auto \
  -checkpoint 5 \
  -metadir specifications/Paxos/states \
  -config specifications/Paxos/Paxos.cfg \
  specifications/Paxos/Paxos.tla
```

### 2. Simulation Mode

For infinite state spaces or quick testing (non-exhaustive):

```bash
java -Xms42G -Xmx42G -jar specifications/tla2tools.jar \
  -seed 0 \
  -workers auto \
  -checkpoint 5 \
  -simulate \
  -depth 100 \
  -metadir specifications/Paxos/states \
  -config specifications/Paxos/Paxos.cfg \
  specifications/Paxos/Paxos.tla
```

### 3. Recovery from Checkpoint

Resume a previous model checking run:

```bash
java -Xms42G -Xmx42G -jar specifications/tla2tools.jar \
  -seed 0 \
  -workers auto \
  -checkpoint 5 \
  -recover specifications/Paxos/states/<checkpoint-directory> \
  -metadir specifications/Paxos/states \
  -config specifications/Paxos/Paxos.cfg \
  specifications/Paxos/Paxos.tla
```

### Command Line Flags Explained

#### Java Virtual Machine Options
- `-Xms42G`: Set initial heap size to 42GB
- `-Xmx42G`: Set maximum heap size to 42GB (adjust based on available memory)

#### TLA+ Tools Options
- `-seed 0`: Set random seed for reproducible results
- `-workers auto`: Use all available CPU cores for parallel checking
- `-checkpoint 5`: Save checkpoint every 5 minutes
- `-simulate`: Enable simulation mode (non-exhaustive, for infinite state spaces)
- `-depth <num>`: Maximum search depth in simulation mode
- `-metadir <path>`: Directory for storing state files and checkpoints
- `-config <file>`: Configuration file specifying constants and properties to check
- `-recover <path>`: Resume from the specified checkpoint directory

## Configuration

The `Paxos.cfg` file defines the model parameters.

- **SPECIFICATION**: Entry point for model checking
- **INVARIANTS**: Properties that must always hold
- **PROPERTY**: Temporal properties (liveness conditions)
- **CONSTANTS**: Concrete values for the specification parameters
- **CONSTRAINT**: State space limitations for finite model checking

## Future Development

This project will be extended to include:

- **Go Implementation**: Production-ready implementation of Paxos in Go
- **Performance Benchmarks**: Comparative analysis of different implementations
- **Network Simulation**: Testing under various network conditions
- **Multi-Paxos**: Extended protocol for multiple consensus instances

## Requirements

- **Java 8+**: Required for running TLA+ tools
- **Memory**: Recommended 8GB+ RAM for model checking
- **Storage**: Sufficient disk space for checkpoint files during long-running verifications

## References

- [Lamport, L. "Paxos Made Simple"](https://lamport.azurewebsites.net/pubs/paxos-simple.pdf)
- [TLA+ Language Reference](https://lamport.azurewebsites.net/tla/tla.html)
- [Practical TLA+](https://www.apress.com/gp/book/9781484238288)
