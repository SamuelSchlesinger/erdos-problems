#!/bin/bash
# Run target_enum for a list of (N, size, MAX_OUT) tuples in parallel.
# Args: workers, then list of "N:SIZE:MAXOUT" triples.
set -eu

HERE="$(cd "$(dirname "$0")" && pwd)"
BIN="$HERE/target_enum"
OUTDIR="$HERE/par_target"
mkdir -p "$OUTDIR"

WORKERS=${1:-14}
shift

run_one() {
    local spec=$1
    local N=$(echo "$spec" | cut -d: -f1)
    local S=$(echo "$spec" | cut -d: -f2)
    local M=$(echo "$spec" | cut -d: -f3)
    local out="$OUTDIR/N${N}_s${S}.txt"
    local err="$OUTDIR/N${N}_s${S}.err"
    "$BIN" "$N" "$S" "$M" > "$out" 2> "$err"
    echo "done N=$N size=$S found=$(wc -l < $out)"
}
export -f run_one
export BIN OUTDIR

printf '%s\n' "$@" | xargs -n 1 -P "$WORKERS" -I {} bash -c 'run_one "$@"' _ {}
