#!/bin/bash
# Parallel driver: run extend_search on a range of N values in parallel.
#
# Usage: parallel_run.sh N_START N_END [WORKERS]

set -eu

HERE="$(cd "$(dirname "$0")" && pwd)"
BIN="$HERE/extend_search"
N_START=${1:-70}
N_END=${2:-100}
WORKERS=${3:-12}

mkdir -p "$HERE/par_results"
rm -f "$HERE/par_results/n_"*.txt
rm -f "$HERE/par_results/combined.txt"

export BIN HERE

run_one() {
  N=$1
  out="$HERE/par_results/n_${N}.txt"
  "$BIN" "$N" "$N" > "$out" 2>&1
  echo "done N=$N"
}
export -f run_one

seq "$N_START" "$N_END" | xargs -n 1 -P "$WORKERS" -I {} bash -c 'run_one "$@"' _ {}

# Combine.
out="$HERE/par_results/combined.txt"
: > "$out"
for f in "$HERE"/par_results/n_*.txt; do
  cat "$f" >> "$out"
done
sort -k1,1n "$out" -o "$out"
echo "Combined output in $out"
