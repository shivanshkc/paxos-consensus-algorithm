#!/bin/bash

set -e

SCRIPT_NAME=$(basename "$0")
JAR_PATH="specifications/tla2tools.jar"
JAVA_OPTS="-Xms42G -Xmx42G -XX:+UnlockExperimentalVMOptions -XX:+UseG1GC"

usage() {
    cat << EOF
Usage: $SCRIPT_NAME <subcommand> [options]

Subcommands:
  fresh     Run a TLA+ specification fresh
  recover   Recover a TLA+ specification run from checkpoint

Fresh subcommand options:
  --spec <name>       Name of the spec (required)
  --depth <depth>     Search depth (default: 100)
  --metadir <suffix>  Metadir suffix (default: states)

Recover subcommand options:
  --spec <name>       Name of the spec (required)
  --checkpoint <path> Path to checkpoint folder (required)
  --depth <depth>     Search depth (default: 100)
  --metadir <suffix>  Metadir suffix (default: states)

Examples:
  $SCRIPT_NAME fresh --spec Paxos
  $SCRIPT_NAME fresh --spec Paxos --depth 200 --metadir custom
  $SCRIPT_NAME recover --spec Paxos --checkpoint specifications/Paxos/states/25-09-09-16-22-20
EOF
}

fresh() {
    local spec=""
    local depth=100
    local metadir="states"
    
    while [[ $# -gt 0 ]]; do
        case $1 in
            --spec)
                spec="$2"
                shift 2
                ;;
            --depth)
                depth="$2"
                shift 2
                ;;
            --metadir)
                metadir="states-$2"
                shift 2
                ;;
            *)
                echo "Unknown option: $1" >&2
                exit 1
                ;;
        esac
    done
    
    if [[ -z "$spec" ]]; then
        echo "Error: --spec is required" >&2
        exit 1
    fi
    
    local spec_file="specifications/$spec/$spec.tla"
    local config_file="specifications/$spec/$spec.cfg"
    local metadir_path="specifications/$spec/$metadir"
    
    if [[ ! -f "$spec_file" ]]; then
        echo "Error: Spec file not found: $spec_file" >&2
        exit 1
    fi
    
    if [[ ! -f "$config_file" ]]; then
        echo "Error: Config file not found: $config_file" >&2
        exit 1
    fi
    
    if [[ ! -f "$JAR_PATH" ]]; then
        echo "Error: TLA2Tools jar not found: $JAR_PATH" >&2
        exit 1
    fi
    
    mkdir -p "$metadir_path"
    
    echo "Running fresh TLA+ specification: $spec"
    echo "Spec file: $spec_file"
    echo "Config file: $config_file"
    echo "Metadir: $metadir_path"
    echo "Depth: $depth"
    echo
    
    java $JAVA_OPTS -jar "$JAR_PATH" \
        -seed 0 \
        -depth "$depth" \
        -workers auto \
        -checkpoint 5 \
        -metadir "$metadir_path" \
        -config "$config_file" \
        "$spec_file"
}

recover() {
    local spec=""
    local checkpoint=""
    local depth=100
    local metadir="states"
    
    while [[ $# -gt 0 ]]; do
        case $1 in
            --spec)
                spec="$2"
                shift 2
                ;;
            --checkpoint)
                checkpoint="$2"
                shift 2
                ;;
            --depth)
                depth="$2"
                shift 2
                ;;
            --metadir)
                metadir="$2"
                shift 2
                ;;
            *)
                echo "Unknown option: $1" >&2
                exit 1
                ;;
        esac
    done
    
    if [[ -z "$spec" ]]; then
        echo "Error: --spec is required" >&2
        exit 1
    fi
    
    if [[ -z "$checkpoint" ]]; then
        echo "Error: --checkpoint is required" >&2
        exit 1
    fi
    
    local spec_file="specifications/$spec/$spec.tla"
    local config_file="specifications/$spec/$spec.cfg"
    local metadir_path="specifications/$spec/$metadir"
    
    if [[ ! -f "$spec_file" ]]; then
        echo "Error: Spec file not found: $spec_file" >&2
        exit 1
    fi
    
    if [[ ! -f "$config_file" ]]; then
        echo "Error: Config file not found: $config_file" >&2
        exit 1
    fi
    
    if [[ ! -d "$checkpoint" ]]; then
        echo "Error: Checkpoint directory not found: $checkpoint" >&2
        exit 1
    fi
    
    if [[ ! -f "$JAR_PATH" ]]; then
        echo "Error: TLA2Tools jar not found: $JAR_PATH" >&2
        exit 1
    fi
    
    echo "Recovering TLA+ specification: $spec"
    echo "Spec file: $spec_file"
    echo "Config file: $config_file"
    echo "Checkpoint: $checkpoint"
    echo "Metadir: $metadir_path"
    echo "Depth: $depth"
    echo
    
    java $JAVA_OPTS -jar "$JAR_PATH" \
        -seed 0 \
        -depth "$depth" \
        -workers auto \
        -checkpoint 5 \
        -metadir "$metadir_path" \
        -config "$config_file" \
        -recover "$checkpoint" \
        "$spec_file"
}

if [[ $# -eq 0 ]]; then
    usage
    exit 1
fi

subcommand="$1"
shift

case $subcommand in
    fresh)
        fresh "$@"
        ;;
    recover)
        recover "$@"
        ;;
    -h|--help|help)
        usage
        ;;
    *)
        echo "Unknown subcommand: $subcommand" >&2
        echo "Run '$SCRIPT_NAME --help' for usage information." >&2
        exit 1
        ;;
esac