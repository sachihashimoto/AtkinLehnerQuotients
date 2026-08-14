///////////////////////////////////////////////////////////////////////////
// tests/test_tangent_plane.m
//
// A coplanarity plane must meet X transversally at the exceptional point.
//
// A hyperplane cuts out a canonical divisor of degree 2g-2 on X.  The
// coplanarity argument reads that divisor as "the exceptional point, plus
// these CM points"; a plane tangent at the exceptional point instead cuts out
// 2*P_exc + (rest), so the exceptional point is not the simple point of a
// special divisor the reported CM labels describe, and the plane explains
// nothing.
//
// Such planes are not hypothetical: at N = 399 the plane
// z[1] + 4z[2] + z[3] - 8z[4] = 0 through the exceptional point (5:-3/2:1:0)
// is tangent there, and used to be reported alongside the two transversal
// ones.  It is invisible in the component degrees, which read [1,1,2,2]:
// Magma's IrreducibleComponents keeps the non-reduced structure, so a doubled
// rational point has degree 2 exactly like a Galois-conjugate pair of CM
// points does.
//
// This suite drives the search off the committed genus-4 model rather than
// building N=399 through check_exceptional_example, which is what the other
// plane suites do.  Nothing here needs a CM label -- the claim is purely about
// how a plane meets X at one rational point -- so the CM machinery would only
// cost ~80s for data the test never reads.  The hardcoded points below are
// coerced onto X, so a regenerated model that moved them fails loudly instead
// of quietly testing nothing.
//
// Run with: tests/run.sh test_tangent_plane
///////////////////////////////////////////////////////////////////////////

load "src/AtkinLehner.m";
load "tests/assertions.m";
load "data/genus4_models.m";   // defines `models` (AssociativeArray) and P

results := NewResults();

N := 399;
X := models[N]`curve;
g := Genus(X);
R := CoordinateRing(AmbientSpace(X));

error if g ne 4,
    Sprintf("N=399 model should be a genus-4 canonical curve, got genus %o", g);

// The 10 rational points of X_0(399)^* found by the point search at B = 1000,
// coerced onto X (which errors if the committed model has moved under them).
// rats[9] is the exceptional point; every other one is CM or the cusp, so all
// of them are "known" input to Search 1, exactly as in LabelAndAnalyze.
rats := [X | [-1, 0, 1, 0], [21/166, 167/83, -29/166, 1], [1, 0, 0, 0],
             [1/2, 1, -1/2, 1], [0, 1, 1, 1], [3, 1, 2, 1], [1, 3/2, 1, 1],
             [-2, 2, 1, 0], [5, -3/2, 1, 0], [0, 1, 1/2, 1]];
exc_idx := 9;
known_rat_idxs := [j : j in [1..#rats] | j ne exc_idx];
exc_coords := [Rationals()!c : c in Eltseq(rats[exc_idx])];

// The three planes through the exceptional point that Search 1 reported before
// the tangency check existed, with the multiplicity of the intersection at the
// exceptional point.  The middle one is the tangent plane.
CASES := [
    <[Rationals()| 0, 4, 6, -7], 1>,
    <[Rationals()| 1, 4, 1, -8], 2>,
    <[Rationals()| 1, 2, -2, -1], 1>
];

// ------------------------------------------------------------------------
// The predicate agrees with Magma's intersection multiplicity.
//
// Valuation(Divisor(X, plane), Place(P)) is the definition; the predicate is
// the linear-algebra shortcut (does the plane contain the tangent line at P).
// Testing it against the definition is the point of this block: the shortcut
// is what the search actually calls, on every candidate plane it fits.
// ------------------------------------------------------------------------

for c in CASES do
    vi, expected_mult := Explode(c);
    L := &+[vi[i]*R.i : i in [1..g]];

    error if &+[vi[i]*exc_coords[i] : i in [1..g]] ne 0,
        Sprintf("test fixture is wrong: %o does not pass through the exceptional point", L);

    mult := Valuation(Divisor(Curve(X), Scheme(AmbientSpace(X), L)),
                      Place(rats[exc_idx]));
    AssertEqual(~results, mult, expected_mult,
        Sprintf("N=399: intersection multiplicity of %o=0 at the exceptional point", L));

    AssertEqual(~results, HyperplaneIsTangentAt(X, vi, exc_coords), expected_mult ge 2,
        Sprintf("N=399: HyperplaneIsTangentAt agrees with multiplicity %o for %o=0", mult, L));
end for;

// A plane through a point it is NOT tangent at is still transversal there:
// z[1]+4z[2]+z[3]-8z[4] is tangent at the exceptional point rats[9] and at
// rats[7], and transversal at the other two rational points it contains.
// Keeps the predicate honest about which point it is asked about.
tangent_vi := [Rationals()| 1, 4, 1, -8];
for j in [1, 2, 7, 9] do
    coords := [Rationals()!c : c in Eltseq(rats[j])];
    error if &+[tangent_vi[i]*coords[i] : i in [1..g]] ne 0,
        Sprintf("test fixture is wrong: the tangent plane misses rats[%o]", j);
    mult := Valuation(Divisor(Curve(X), Scheme(AmbientSpace(X),
                &+[tangent_vi[i]*R.i : i in [1..g]])), Place(rats[j]));
    AssertEqual(~results, HyperplaneIsTangentAt(X, tangent_vi, coords), mult ge 2,
        Sprintf("N=399: HyperplaneIsTangentAt at rats[%o] agrees with multiplicity %o", j, mult));
end for;

// ------------------------------------------------------------------------
// Search 1 drops the tangent plane and keeps the two transversal ones.
// ------------------------------------------------------------------------

r1_deg1, r1_deg2 := CoplanaritySearch1(X, rats, exc_idx, known_rat_idxs);
found := [* e[2] : e in r1_deg1 *] cat [* e[2] : e in r1_deg2 *];

printf "\nSearch 1 planes through rats[%o]: %o\n", exc_idx, found;

for c in CASES do
    vi, mult := Explode(c);
    L := &+[vi[i]*R.i : i in [1..g]];
    // Sign is not part of the plane's identity, so compare both ways.
    reported := exists{e : e in found | e eq L or e eq -L};
    AssertEqual(~results, reported, mult eq 1,
        Sprintf("N=399: Search 1 %o the plane %o=0 (multiplicity %o at the exceptional point)",
                mult eq 1 select "reports" else "drops", L, mult));
end for;

// The two survivors are the whole answer: nothing else was let through, and
// the level is still covered, so rejecting the tangent plane does not cost
// N=399 its exceptional-point explanation.
AssertEqual(~results, #found, 2,
    Sprintf("N=399: Search 1 returns exactly the 2 transversal planes (got %o)", found));

Report(~results, "test_tangent_plane");
