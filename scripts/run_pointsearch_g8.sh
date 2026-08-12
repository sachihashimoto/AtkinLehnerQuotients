#!/bin/bash
# Run directly: ./scripts/run_pointsearch_g8.sh   (no options; edit B / NSHARDS below to change)
#
# Launches scripts/pointsearch_g8.m as NSHARDS parallel Magma shards (B=10^6),
# waits for all of them, then concatenates the shard outputs into one summary.
# Each shard writes outputs/special_vs_found_g8_sqfree_B1000000_shard<k>.txt
set -u
cd "$(dirname "$0")/.."

B=1000000
NSHARDS=8
LOGDIR=outputs
mkdir -p "$LOGDIR"

pids=()
for k in $(seq 1 "$NSHARDS"); do
    magma -b B:=$B shard:=$k nshards:=$NSHARDS scripts/pointsearch_g8.m \
        > "$LOGDIR/pointsearch_g8_B${B}_shard${k}.log" 2>&1 &
    pids+=($!)
done

fail=0
for p in "${pids[@]}"; do
    wait "$p" || fail=1
done

# Concatenate completed shard result files into one summary.
OUT="$LOGDIR/special_vs_found_g8_sqfree_B${B}.txt"
{
    echo "# Squarefree genus-8 X0(N)*: PointSearch(B=$B, Nonsingular:=true) found vs stored special points"
    echo "# N  found  special  diff  search_s"
    for k in $(seq 1 "$NSHARDS"); do
        f="$LOGDIR/special_vs_found_g8_sqfree_B${B}_shard${k}.txt"
        [ -f "$f" ] && grep -v '^#' "$f"
    done | sort -n
} > "$OUT"

echo "DONE fail=$fail  summary=$OUT"
exit $fail
