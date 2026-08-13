// test_triple_covers.m
// Tests for src/triple_covers.m: the degree-3 maps pi : X_0(M)* -> E (M the top
// level, E of conductor d | M) and the CM fiber analysis.
//
// Run from the repo root with:  tests/run.sh test_triple_covers
//
// Covers:
//   1. TripleCoverXYSeries: the q-series (x∘pi, y∘pi) satisfy the Weierstrass
//      equation of E, and their differential equals (f + e f(q^e)) dq/q for
//      e = M/d.
//   2. SolveRatFun: recovers a known rational-function identity.
//   3. LabelAndAnalyze 5th return value (idx -> disc map, cusp = 0) on N=97.
//   4. End-to-end known answer on M=286 -> 143a1 (the examples/X0star286.m
//      example): degree 3, c=1, E=143a1, X isomorphic to the known model of
//      X_0(286)*, D=-39 fiber third point = the exceptional point
//      (5/2 : -143/16 : 1), D=-55 fiber third point = the cusp.

load "src/triple_covers.m";
load "tests/assertions.m";
SetSeed(1);

results := NewResults();

// ---------------------------------------------------------------------------
printf "\n=== 1. TripleCoverXYSeries consistency ===\n";
// ---------------------------------------------------------------------------
prec := 60;
// <target label, top level M>; both cases have M/d prime, so the oldform
// combination TripleCoverXYSeries derives from Divisors(M div d) is
// f(q) + e f(q^e) with the single e = M/d checked below.
for pair in [<"143a1", 286>, <"58a1", 290>] do
    E := EllipticCurve(pair[1]);
    M := pair[2];
    e := M div Conductor(E);
    xq, yq := TripleCoverXYSeries(E, M, prec, 1);
    a1, a2, a3, a4, a6 := Explode(aInvariants(E));
    res := yq^2 + a1*xq*yq + a3*yq - (xq^3 + a2*xq^2 + a4*xq + a6);
    AssertEqual(~results, IsWeaklyZero(res), true,
        Sprintf("%o: (x∘pi, y∘pi) satisfy the Weierstrass equation", pair[1]));

    // pullback differential: q d/dq(x) / (2y + a1 x + a3) = f(q) + e f(q^e)
    L<q> := Parent(xq);
    Dx := q * Derivative(xq);
    omega_ratio := Dx / (2*yq + a1*xq + a3);
    fE := qExpansion(ModularForm(E), prec + 1);
    h := &+[L | Coefficient(fE, n) * q^n : n in [1..prec - 1]]
       + e * &+[L | Coefficient(fE, n) * q^(e*n) : n in [1..Floor((prec - 1)/e)]]
       + O(q^prec);
    AssertEqual(~results, IsWeaklyZero(omega_ratio - h), true,
        Sprintf("%o: pi^* omega = (f + %o f(q^%o)) dq/q", pair[1], e, e));
end for;

// ---------------------------------------------------------------------------
printf "\n=== 2. SolveRatFun synthetic identity ===\n";
// ---------------------------------------------------------------------------
L<q> := LaurentSeriesRing(Rationals());
f1 := q + q^3 - 2*q^7 + O(q^80);
f2 := q^2 - q^5 + 3*q^9 + O(q^80);
mons := [f1^2, f1*f2, f2^2];
target := (2*f1^2 - f1*f2 + 5*f2^2) / (f1^2 + 4*f2^2);
ok, a, b := SolveRatFun(target, mons : min_extra := 10);
AssertEqual(~results, ok, true, "SolveRatFun finds a solution");
if ok then
    lhs := &+[a[j]*mons[j] : j in [1..3]];
    rhs := target * &+[b[j]*mons[j] : j in [1..3]];
    AssertEqual(~results, IsWeaklyZero(lhs - rhs), true,
        "SolveRatFun solution satisfies the identity");
    AssertEqual(~results, not IsWeaklyZero(&+[b[j]*mons[j] : j in [1..3]]), true,
        "SolveRatFun denominator is nonzero");
end if;

// ---------------------------------------------------------------------------
printf "\n=== 3. LabelAndAnalyze idx -> disc map (N = 97) ===\n";
// ---------------------------------------------------------------------------
pts97, X97, fs97, Sstar97 := point_search_X0Nstar(97, 100000);
exc97, planes97, ok97, fail97, i2d97 :=
    LabelAndAnalyze(97, X97, fs97, pts97, Keys(RationalCMDiscs(97)) : confirm_deg2 := false);
AssertEqual(~results, #exc97, 0, "N=97: no exceptional points");
AssertEqual(~results, #Keys(i2d97), #pts97,
    "N=97: idx_to_disc labels all points");
AssertEqual(~results, #[j : j in Keys(i2d97) | i2d97[j] eq 0], 1,
    "N=97: exactly one cusp sentinel in idx_to_disc");

// ---------------------------------------------------------------------------
printf "\n=== 4. End-to-end known answer: M = 286 -> 143a1 (X_0(286)*) ===\n";
// ---------------------------------------------------------------------------
pi, X, E, fs, Sstar, c := BuildTripleCover(286, "143a1");
AssertEqual(~results, Degree(pi), 3, "M=286: map has degree 3");
AssertEqual(~results, c, 1, "M=286: differential normalization c = 1");
AssertEqual(~results, CremonaReference(E), "143a1", "M=286: E = 143a1");
R<x> := PolynomialRing(Rationals());
C1 := HyperellipticCurve(x^6 + 2*x^4 + 5*x^2 + 12*x - 4);   // examples/X0star286.m model
iso := IsIsomorphic(X, C1);
AssertEqual(~results, iso, true, "M=286: X isomorphic to the X0star286.m model of X_0(286)*");

res39 := AnalyzeCMFiber(pi, X, E, fs, Sstar, 286, -39);
AssertEqual(~results, #res39, 1, "D=-39: exactly one third point");
if #res39 eq 1 then
    AssertEqual(~results, Sprint(res39[1][2]), "(4 : -7 : 1)",
        "D=-39: CM pair maps to Q = (4 : -7 : 1)");
    AssertEqual(~results, Sprint(res39[1][3]), "(5/2 : -143/16 : 1)",
        "D=-39: third point is (5/2 : -143/16 : 1)");
    AssertEqual(~results, res39[1][4], "NOT CM (exceptional)",
        "D=-39: third point labelled exceptional");
end if;

res55 := AnalyzeCMFiber(pi, X, E, fs, Sstar, 286, -55);
AssertEqual(~results, #res55, 1, "D=-55: exactly one third point");
if #res55 eq 1 then
    AssertEqual(~results, Sprint(res55[1][2]), "(0 : 1 : 0)",
        "D=-55: CM pair maps to Q = (0 : 1 : 0)");
    AssertEqual(~results, Sprint(res55[1][3]), "(1 : -1/2 : 0)",
        "D=-55: third point is (1 : -1/2 : 0)");
    AssertEqual(~results, res55[1][4], "cusp",
        "D=-55: third point labelled cusp");
end if;

Report(~results, "test_triple_covers");
