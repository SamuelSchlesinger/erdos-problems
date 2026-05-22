#!/bin/bash
# Parallel runner for extend_search_v2.
# Args: N_START N_END WORKERS DO_ENUM
set -eu

HERE="$(cd "$(dirname "$0")" && pwd)"
BIN="$HERE/extend_search_v2"
N_START=${1:-80}
N_END=${2:-100}
WORKERS=${3:-14}
DO_ENUM=${4:-1}
OUTDIR="$HERE/par_v2"
mkdir -p "$OUTDIR"

run_one() {
    local N=$1
    local out="$OUTDIR/n_${N}.txt"
    "$BIN" "$N" "$N" "$DO_ENUM" > "$out" 2>&1
    echo "done N=$N"
}
export -f run_one
export BIN OUTDIR DO_ENUM

seq "$N_START" "$N_END" | xargs -n 1 -P "$WORKERS" -I {} bash -c 'run_one "$@"' _ {}
