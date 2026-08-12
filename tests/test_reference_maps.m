// tests/test_reference_maps.m
//
// Exercises both TripleCoverMap_* branches of BuildStarCover
// (src/triple_covers.m), including the canonical branch, which otherwise has
// zero runtime coverage anywhere in the test suite. ~38 s.
//
// Run with: tests/run.sh test_reference_maps
//
// Cache-busting (why, not just "chosen because uncached"): the triple-cover
// classification is exhaustive (reproduced in
// outputs/triple_cover_classification.txt, pinned against the paper's table by
// tests/test_triple_cover_table.m), there are exactly 48 (M, target) pairs
// for which BuildStarCover can possibly succeed, period, and all 48 already
// have a data/starmodels/map_<M>_<label>.m cache entry (verified by
// scripts/reconcile_covers.m: 48 enumerated, 48 cached, 0 orphans, 0 missing).
// So no pair, now or in the future, can be "the uncached one": any pair
// added here would get cached the first time this file runs and stay cached.
// Picking pairs by cache absence is therefore not a stable strategy; instead,
// each case below passes use_cache := false, so the
// TripleCoverMap_canonical/hyperelliptic search path (src/triple_covers.m) is
// exercised unconditionally on every run. That is a cache-read bypass, not a
// delete: the cached maps cost hours to produce and are independent evidence
// that each cover exists, so this test must never remove them to force a miss.
// (The star-model cache, data/starmodels/starforms_<M>.m, is left alone; it is
// a different cache layer, for StarModelWithForms, and staying warm there is
// fine and matches the documented timings below.)
//
//   call                              branch          expected time
//   BuildStarCover(246, "123b1")      canonical       ~7.6 s
//   BuildStarCover(290, "58a1")       canonical       ~8.3 s
//   BuildStarCover(286, "143a1")      hyperelliptic   ~21.6 s
//
// BuildStarCover rewrites map_<M>_<label>.m in data/starmodels/ as a side
// effect, with identical content; expected, and harmless. Do not "reset" the
// cache with `git clean -fdq data/starmodels`: most map files there are
// untracked and that would delete maps costing hours to rebuild.

load "src/triple_covers.m";
load "tests/assertions.m";
SetSeed(1);

results := NewResults();

// --- Arrange ---
// <M, Cremona label, branch, expected aInvariants(E)> for the three cases that
// exercise both TripleCoverMap_* branches of BuildStarCover. The canonical
// branch has no other runtime coverage anywhere in the suite.
//
// Only aInvariants(E) and Degree(pi) are pinned. Both are canonical: E is
// determined by its Cremona label, and the cover has degree 3 by construction.
// DefiningPolynomials(pi) and c are deliberately NOT pinned -- the polynomials
// depend on the coordinate system of the constructed model (see the
// data/starmodels cache note in README.md, which records that a cached map
// does not store the coordinate system used to create it), and c is the
// constant in pi^*omega = c*h*dq/q, so it depends on the normalisation of the
// forms and can shift with the same coordinate change. Pinning either would
// make this test fail on legitimate model changes, which is the brittleness
// this suite was rewritten to remove.
cases := [
    <246, "123b1", "canonical",     [ 0, -1, 1,  1, -1 ]>,
    <290, "58a1",  "canonical",     [ 1, -1, 0, -1,  1 ]>,
    <286, "143a1", "hyperelliptic", [ 0, -1, 1, -1, -2 ]>
];

for c in cases do
    M := c[1]; lab := c[2]; branch := c[3]; expected_ainv := c[4];
    printf "\n=== BuildStarCover(%o, \"%o\") [%o branch] ===\n", M, lab, branch;

    // --- Act ---
    // use_cache := false forces a genuine build, so the search path is
    // exercised on every run regardless of what is in data/starmodels/. It is
    // a cache-read bypass, not a delete: the cached maps cost hours to produce
    // and are independent evidence that each cover exists.
    //
    // BuildStarCover's progress chatter is suppressed so only the assertions
    // below reach stdout. There is no try/catch: Magma's try/catch does not
    // catch runtime errors, and a runtime error here terminates the process
    // with its message on stderr (which SetOutputFile does not redirect),
    // emitting no completion marker -- which tests/run.sh reports as
    // INCOMPLETE, the correct status for a suite that died.
    SetOutputFile("/dev/null" : Overwrite := true);
    pi, X, E, fs, Sstar, cval := BuildStarCover(M, lab : use_cache := false);
    UnsetOutputFile();

    // --- Assert ---
    AssertEqual(~results, aInvariants(E), expected_ainv,
        Sprintf("M=%o -> %o (%o branch): aInvariants(E)", M, lab, branch));
    AssertEqual(~results, Degree(pi), 3,
        Sprintf("M=%o -> %o (%o branch): Degree(pi)", M, lab, branch));
end for;

printf "\n";
Report(~results, "test_reference_maps");
