// scripts/check_fiber_table.m
//
// Regenerates the paper's Table "exceptional points in special fibers of
// triple covers" (tab:exceptional_cm_fibers) from src/triple_covers.m, so the
// hand-entered discriminants and the ramified/unramified annotations can be
// diffed against the computation.
//
// This table is currently pinned by nothing: tests/test_triple_covers.m
// exercises AnalyzeCMFiber and SweepCMFibers but does not assert the table's
// contents, and the one other hand-entered table we checked (genus 4, N = 370)
// was wrong.
//
// Run from the repo root:
//     magma scripts/check_fiber_table.m
// or inside a session:
//     load "scripts/check_fiber_table.m";
//
// Runtime: BuildTripleCover is ~10 s per level and SweepCMFibers is the
// expensive part (~30 s per discriminant at N = 290).  Each row prints as it
// finishes.

load "src/triple_covers.m";

// <N, Cremona label of E^C_f> for the rows of the table.  Transcribe the rest
// of tab:exceptional_cm_fibers here; these are the ones already in the draft.
// Cremona labels, not LMFDB: BuildTripleCover takes what Magma emits.
ROWS := [
    <154, "154a1">,
    <285, "285b1">,
    <286, "286c1">,
    <318, "318c1">,
    <430, "430a1">,
    <154, "77a1">,
    <285, "57a1">,
    <286, "143a1">,
    <310, "155c1">,
    <246, "123b1">
];

for r in ROWS do
    N, lab := Explode(r);
    printf "\n=== N = %o -> %o ===\n", N, lab;
    t0 := Cputime();
    pi, X, E, fs, Sstar, c := BuildTripleCover(N, lab);
    printf "  built (%o s)\n", Cputime(t0);
    rows := SweepCMFibers(pi, X, E, fs, Sstar, N);
    printf "  %o fiber rows\n", #rows;
    rows;
end for;

printf "\nCompare each printed fiber against the corresponding row of\n";
printf "tab:exceptional_cm_fibers: the CM discriminant, the third point of\n";
printf "the fiber, and whether the special point occurs with multiplicity\n";
printf "(the 'ramified rational CM' annotation).\n";
