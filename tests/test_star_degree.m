// tests/test_star_degree.m
// Tests for src/star_degree.m: the Atkin-Lehner translations c_n, the star
// degree delta_f, and the target curve E^C_f.
//
// Run from the repo root with:
//   tests/run.sh test_star_degree > /tmp/t.txt 2>&1; cat /tmp/t.txt
// Judge the result by counting PASS lines, not by the trailing banner;
// magma -b continues past undeclared-identifier errors, so a stale file can
// print "ALL TESTS PASSED" having executed zero assertions.

load "src/AtkinLehner.m";
load "tests/assertions.m";
SetSeed(1);

results := NewResults();

// ---------------------------------------------------------------------------
printf "\n=== 1. ALTranslations: |C| on known curves ===\n";
// ---------------------------------------------------------------------------
// C = 0 for every totally-+1 curve in the production tables except 185c1,
// which is the case the old classification had to special-case.
for t in [<"37a1", 1>, <"57a1", 1>, <"58a1", 1>, <"77a1", 1>, <"91a1", 1>,
          <"143a1", 1>, <"155c1", 1>, <"190b1", 1>, <"154a1", 1>,
          <"163a1", 1>, <"201a1", 1>, <"185c1", 2>] do
    E := EllipticCurve(t[1]);
    nC := ALTranslations(E);
    AssertEqual(~results, nC, t[2],
        Sprintf("ALTranslations(%o): |C|", t[1]));
end for;

// ---------------------------------------------------------------------------
printf "\n=== 2. ALTranslations: c is a homomorphism ===\n";
// ---------------------------------------------------------------------------
// The internal cross-check asserts c_{nm} = c_n + c_m; confirm it is exercised
// on a curve with three prime divisors.
E := EllipticCurve("154a1");
nC, classes := ALTranslations(E);
AssertEqual(~results, #classes, 3,
    "ALTranslations(154a1): one class per prime divisor of 154");

// ---------------------------------------------------------------------------
printf "\n=== 3. TotallyPlusOptimalCurves ===\n";
// ---------------------------------------------------------------------------
// A level can carry several totally-+1 classes, 185a and 185c both have
// a_5 = a_37 = -1.  Only 185c has delta_f = 3; 185a is filtered later, by the
// degree, not here.  (This multiplicity is why BuildStarCover takes the target
// curve by Cremona label rather than deriving it from the level.)
AssertEqual(~results,
    [CremonaReference(F) : F in TotallyPlusOptimalCurves(185)], ["185a1", "185c1"],
    "TotallyPlusOptimalCurves(185) = [185a1, 185c1]");
AssertEqual(~results, #TotallyPlusOptimalCurves(174), 0,
    "TotallyPlusOptimalCurves(174) is empty (174's newform level is 58)");

// ---------------------------------------------------------------------------
printf "\n=== 4. StarDegree ===\n";
// ---------------------------------------------------------------------------
// delta_f = 1 exactly on the genus-1 star levels; delta_f = 3 is the own-level
// trigonal case.  185c1 reaches delta = 2*6/4 = 3 only because |C| = 2, with
// the old formula it came out 6/4, not an integer at all.
for t in [<"37a1", 1>, <"57a1", 1>, <"58a1", 1>, <"77a1", 1>, <"91a1", 1>,
          <"143a1", 1>, <"155c1", 1>, <"190b1", 1>,
          <"154a1", 3>, <"163a1", 3>, <"201a1", 3>, <"185c1", 3>] do
    E := EllipticCurve(t[1]);
    dl := StarDegree(E);
    AssertEqual(~results, dl, t[2],
        Sprintf("StarDegree(%o)", t[1]));
end for;

// ---------------------------------------------------------------------------
printf "\n=== 5. StarTargetCurve ===\n";
// ---------------------------------------------------------------------------
// C = 0 leaves the curve alone; 185 is the one case where the target is a
// different member of the isogeny class.
for t in [<"77a1", "77a1">, <"154a1", "154a1">, <"201a1", "201a1">,
          <"185c1", "185c2">] do
    E := EllipticCurve(t[1]);
    lab := CremonaReference(StarTargetCurve(E));
    AssertEqual(~results, lab, t[2],
        Sprintf("StarTargetCurve(%o)", t[1]));
end for;

// ---------------------------------------------------------------------------
printf "\n=== 6. The guards reject rather than guess ===\n";
// ---------------------------------------------------------------------------
// Feeding ALTranslationClass the intersection lattice Lattice(M) instead of the
// image of H_1 produces denominator-12 coordinates.  The half-integrality guard
// must error, not return a plausible wrong class.  This is the regression that
// matters: the failure mode this repo has hit before is a guard that silently
// accepts.
Eg := EllipticCurve("185c1");
Mg := ModularSymbols(Eg);
Ag := AmbientSpace(Mg);
pmxg := ProjectionMatrix(Mg);
Bwrong := Matrix(Rationals(), [Eltseq(b) : b in Basis(Lattice(Mg))]);
guard_fired := false;
try
    _ := ALTranslationClass(Ag, pmxg, Bwrong, 185, 5);
catch e
    guard_fired := true;
end try;
AssertEqual(~results, guard_fired, true,
    "ALTranslationClass errors on the intersection lattice instead of guessing");

Report(~results, "test_star_degree");
