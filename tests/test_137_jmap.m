///////////////////////////////////////////////////////////////////////////
// Independent certification of every CM discriminant on the N=137
// {D=-11, D=-4, cusp} plane via the actual modular curve X_0(137) and its
// j-map, cross-checking the canonical-model/plane-intersection argument in
// tests/test_137_plane.m.
//
// tests/test_137_plane.m certifies that the exact rational plane through
// {D=-11, D=-4, cusp} on X_0(137)* (built from cusp-form q-expansions, see
// src/modelsX0Nstar.m) meets X_0(137)* in components {D=-11, D=-4, cusp,
// exceptional point, D=-32}; but the D=-32 match is made via
// src/labelling.m's CM-field machinery, entirely within the star-form
// model, and D=-11/D=-4 are taken on faith from MatchRationalCMPoints's
// numerical CM-evaluation match. This test instead, for each CM
// discriminant on the plane (D=-11, D=-4, D=-32; the cusp isn't a CM
// point and the exceptional point is by definition not CM, so neither has
// a Hilbert class polynomial to check):
//   1. builds X_0(137) and its w_137-quotient X_0(137)* via
//      QuadraticPoints' eqs_quos (a different construction from
//      src/modelsX0Nstar.m's cusp-form embedding);
//   2. checks the two constructions of X_0(137)* literally share
//      coordinates (every rats[] point from step 1 lies on the eqs_quos
//      model too);
//   3. re-derives the plane through {D=-11, D=-4, cusp} natively on the
//      eqs_quos model, and locates each discriminant's locus on it (a
//      rational point for D=-11/D=-4, a degree-2 component for D=-32);
//   4. pulls that locus back through the quotient map
//      rho : X_0(137) -> X_0(137)* to X_0(137) itself;
//   5. applies jmap (the actual j-invariant map on X_0(137)) to every
//      preimage point, and checks the result is a root of
//      HilbertClassPolynomial(D).
//
// A pass here means every CM label on the plane was reached by two
// independent routes, CM-field/CM-evaluation matching on the star-form
// model, and literal j-invariant/Hilbert-class-polynomial evaluation on
// X_0(137) itself, which share almost no code apart from Magma's scheme
// engine.
//
// Run with: tests/run.sh test_137_jmap    (~90s, dominated by jmap)
///////////////////////////////////////////////////////////////////////////

// Loads src/triple_covers.m (which itself loads src/AtkinLehner.m) rather
// than src/AtkinLehner.m directly, purely to reuse its PolyCoeffData /
// PolyFromCoeffData / StrJoin / STAR_CACHE_DIR helpers for the jmap cache
// below, none of the triple-cover machinery itself is used here.
load "src/triple_covers.m";
load "tests/assertions.m";

// ------------------------------------------------------------------------
// jmap(X137, 137) alone accounts for ~75s of this test's ~90s runtime (it
// re-derives the j-map from scratch via q-expansion linear algebra every
// time). Cache its num/denom polynomials the same way
// src/triple_covers.m caches triple-cover maps: ring-independent
// <coeff,exponents> data under data/starmodels/, staged through a temp
// file so a partial write never clobbers a good cache.
// ------------------------------------------------------------------------
function JmapCachePath(N)
    return STAR_CACHE_DIR cat "/jmap_" cat Sprint(N) cat ".m";
end function;

function LoadJmapCache(N, R)
    s := "";
    try
        s := Read(JmapCachePath(N));
    catch e
        return false, _, _;
    end try;
    dat := eval s;   // <numdata, dendata>
    num := PolyFromCoeffData(R, dat[1]);
    denom := PolyFromCoeffData(R, dat[2]);
    return true, num, denom;
end function;

procedure SaveJmapCache(N, num, denom)
    body := Sprintf("<%o, %o>", PolyCoeffData(num), PolyCoeffData(denom));
    tmp := JmapCachePath(N) cat ".tmp" cat Sprint(Random(10^9));
    Write(tmp, body : Overwrite := true);
    System(Sprintf("mv %o %o", tmp, JmapCachePath(N)));
    printf "[cache] saved jmap for level %o\n", N;
end procedure;

results := NewResults();

target_degree2_disc     := -32;
target_rational_labels  := {Integers() | -11, -4, 0};


// ------------------------------------------------------------------------
// Step 1: the star-form model (src/modelsX0Nstar.m), used only to find the
// exact rational plane through {D=-11, D=-4, cusp}; exactly as in
// tests/test_137_plane.m.
// ------------------------------------------------------------------------

interesting := check_exceptional_example(137);
N      := interesting[1][1];
rats   := interesting[1][3];
X      := interesting[1][4];
fs     := interesting[1][5];
cm_pts := interesting[1][7];

g := Genus(X);
error if N ne 137 or g ne 4,
    Sprintf("Expected N=137, genus 4; got N=%o, genus %o.", N, g);

CC  := ComplexField(200);
tol := 10^-15;
rats_cc := [[CC!c : c in Eltseq(rats[j])] : j in [1..#rats]];

ell_pts, disc_ell_pts := EllipticDiscsByOrder(N);
rat_cm_discs := {Integers() | d : d in Keys(cm_pts)};

matched, match_nfail, disc_to_idx, fail_reason :=
    MatchRationalCMPoints(N, fs, rats_cc, rats, CC, tol, rat_cm_discs, ell_pts, disc_ell_pts);
error if match_nfail ne 0,
    Sprintf("Rational CM matching failed: %o", fail_reason);

idx_to_disc := AssociativeArray();
for disc in Keys(disc_to_idx) do
    for j in disc_to_idx[disc] do
        idx_to_disc[j] := disc;
    end for;
end for;

cusp_cc := [CC!Coefficient(fs[i], 1) : i in [1..g]];
cusp_idxs := [j : j in [1..#rats] | IsProjectivelyEquivalent(rats_cc[j], cusp_cc, tol)];
error if #cusp_idxs ne 1,
    Sprintf("The cusp was matched %o times among rats (expected exactly 1).", #cusp_idxs);
cusp_idx := cusp_idxs[1];
error if IsDefined(idx_to_disc, cusp_idx),
    "The cusp index already carries a CM label.";
idx_to_disc[cusp_idx] := 0;

exceptional_idxs := [j : j in [1..#rats] | not IsDefined(idx_to_disc, j)];
error if #exceptional_idxs ne 1,
    Sprintf("Expected exactly one exceptional point on X_0(137)*; got %o.", exceptional_idxs);
exc_idx := exceptional_idxs[1];
exc_coords := [Rationals()!c : c in Eltseq(rats[exc_idx])];

target_idxs := Sort([j : j in Keys(idx_to_disc) | idx_to_disc[j] in target_rational_labels]);
error if #target_idxs ne 3,
    Sprintf("Expected three rational target points {D=-11,-4,cusp}; found indices %o.", target_idxs);

target_coords := [[Rationals()!c : c in Eltseq(rats[j])] : j in target_idxs];
ok, vi := HyperplaneFromPoints(g, target_coords);
error if not ok, "HyperplaneFromPoints failed to construct the plane.";

AssertEqual(~results, CanonicalPlaneKey(vi), [0,2,-1,-2],
    "N=137: plane through {D=-11,D=-4,cusp} has coefficients [0,2,-1,-2] up to sign");


// ------------------------------------------------------------------------
// Step 2: build X_0(137) and X_0(137)* independently via eqs_quos, and
// check the two X_0(137)* models literally share coordinates.
// ------------------------------------------------------------------------

time X137, ws137, pairs137, NB137, cusp137 := eqs_quos(137, [[137]]);

AssertEqual(~results, Genus(X137), 11,
    "N=137: eqs_quos genus of X_0(137) is 11");

Ystar := pairs137[1][1];
rho   := pairs137[1][2];

AssertEqual(~results, Genus(Ystar), g,
    Sprintf("N=137: eqs_quos genus of X_0(137)* matches the star-form model's genus %o", g));

AY := AmbientSpace(Ystar);
same_coords := &and[
    &and[Evaluate(eqn, [Rationals()!c : c in Eltseq(rats[j])]) eq 0 : eqn in DefiningEquations(Ystar)]
    : j in [1..#rats]
];
AssertEqual(~results, same_coords, true,
    "N=137: the eqs_quos X_0(137)* model shares coordinates with the star-form model (every rats[] point lies on it)");

error if not same_coords,
    "Cannot continue: the two X_0(137)* models do not share coordinates.";


// ------------------------------------------------------------------------
// Step 3: re-derive the plane natively on Ystar, and confirm it meets it in
// the same component shape [1,1,1,1,2] found by tests/test_137_plane.m
// (D=-11, D=-4, cusp, the exceptional point, and D=-32).
// ------------------------------------------------------------------------

plane_eqnY := &+[vi[l]*AY.l : l in [1..g]];
ScutY   := Scheme(Ystar, [plane_eqnY]);
compsY  := IrreducibleComponents(ScutY);
degsY   := Sort([Degree(c) : c in compsY]);

AssertEqual(~results, degsY, [1,1,1,1,2],
    "N=137: plane meets the eqs_quos X_0(137)* model in components of degree [1,1,1,1,2]");

comps2Y := [c : c in compsY | Degree(c) eq 2];
error if #comps2Y ne 1,
    Sprintf("Expected exactly one degree-2 component; got %o.", #comps2Y);
compY := comps2Y[1];

_, split_fldY := PointsOverSplittingField(compY);
comp_nfY := NumberField(AbsolutePolynomial(split_fldY));
pts_KY   := RationalPoints(BaseChange(compY, comp_nfY));
error if #pts_KY ne 2,
    Sprintf("Expected 2 conjugate points on the degree-2 component; got %o.", #pts_KY);

printf "\nD=-32 component field: %o\n", DefiningPolynomial(comp_nfY);
printf "D=-32 points on the eqs_quos X_0(137)* model: %o\n", [Eltseq(p) : p in pts_KY];

// Cross-check against the field independently found by
// tests/test_137_plane.m's AlgebraicDeg2Matches (same claimed D=-32
// component, reached from the star-form model instead).
Rx<xx> := PolynomialRing(Rationals());
AssertEqual(~results, DefiningPolynomial(comp_nfY), xx^2 - 4*xx + 2,
    "N=137: D=-32 component field matches x^2-4x+2");


// ------------------------------------------------------------------------
// Step 4: pull every CM locus on the plane back through rho to X_0(137),
// and check its jmap image against the right Hilbert class polynomial.
//
// rho is (for this branch of eqs_quos) literally the raw coordinate
// projection x |-> [x[1]:...:x[g]] on X_0(137)'s ambient P^10, checked
// explicitly below, since that equality is exactly what justifies pulling
// a locus on Ystar back by direct substitution of its AY-side defining
// equations into AX137's first g coordinates, instead of Magma's Pullback
// (which errors "Element is not in the codomain of the map" on this
// map/scheme pair) or a base-changed Difference (which errors "Arguments
// are not compatible" once the base scheme is moved to a number field;
// the direct-substitution route sidesteps that because it stays over Q,
// pulling back the whole (possibly Galois-conjugate) locus as one
// Q-rational scheme rather than an individual algebraic point).
//
// For D=-11 and D=-4 (rational points, so the "locus" is just g-1
// independent linear equations pinning that one point) this is exactly
// what the D=-32 degree-2 case does with DefiningEquations(compY) instead
// of hand-built linear equations, both are "the AY-side equations
// cutting out this discriminant's locus", so one procedure handles all
// three.
// ------------------------------------------------------------------------

rho_eqns := DefiningEquations(rho);
AX137    := AmbientSpace(X137);

AssertEqual(~results, rho_eqns, [AX137.i : i in [1..g]],
    Sprintf("N=137: rho is the raw coordinate-projection map x |-> [x[1]:...:x[%o]]", g));

error if rho_eqns ne [AX137.i : i in [1..g]],
    "Cannot continue: the direct-substitution pullback shortcut is invalid for this rho.";

BS := BaseScheme(rho);

gX137 := Genus(X137);
R_num := PolynomialRing(Rationals(), gX137);

have_jmap_cache, num, denom := LoadJmapCache(137, R_num);
if have_jmap_cache then
    printf "\n[cache] loaded jmap for level 137\n";
else
    time jm, numden := jmap(X137, 137);
    num   := numden[1];
    denom := numden[2];
    SaveJmapCache(137, num, denom);
end if;

// ay_eqns: the AY-side equations cutting out a rational point y in P^(g-1)
//, g-1 independent linear equations through y, pivoting on a nonzero
// coordinate so none of them is 0=0.
function PointLocusEqns(AY, g, y)
    piv := [k : k in [1..g] | y[k] ne 0][1];
    return [AY.k*y[piv] - AY.piv*y[k] : k in [1..g] | k ne piv];
end function;

procedure CertifyCMDiscViaJmap(~results, X137, AX137, BS, g, num, denom, D, ay_eqns, expected_fiber_deg)
    eqns_X      := [Evaluate(e, [AX137.i : i in [1..g]]) : e in ay_eqns];
    FiberScheme := Scheme(AX137, DefiningEquations(X137) cat eqns_X);
    Dfib        := Difference(FiberScheme, BS);

    AssertEqual(~results, Dimension(Dfib), 0,
        Sprintf("N=137: the pullback of the D=%o locus under rho is 0-dimensional", D));

    AssertEqual(~results, Degree(Dfib), expected_fiber_deg,
        Sprintf("N=137: the pullback of the D=%o locus under rho has degree %o", D, expected_fiber_deg));

    pb, split := PointsOverSplittingField(Dfib);

    AssertEqual(~results, #pb, expected_fiber_deg,
        Sprintf("N=137: found %o geometric preimage points on X_0(137) for D=%o", expected_fiber_deg, D));

    HD := HilbertClassPolynomial(D);
    printf "\nHilbertClassPolynomial(%o) = %o\n", D, HD;

    all_roots := true;
    for P in pb do
        Pcoords := Eltseq(P);
        L := Universe(Pcoords);
        numval := Evaluate(num, Pcoords);
        denval := Evaluate(denom, Pcoords);

        error if denval eq 0,
            Sprintf("jmap denominator vanishes at a D=%o preimage point %o.", D, Pcoords);

        jval    := numval/denval;
        HDL     := ChangeRing(HD, L);
        is_root := Evaluate(HDL, jval) eq 0;

        printf "  D=%o preimage j = %o : root of H_(%o) = %o\n", D, jval, D, is_root;

        if not is_root then all_roots := false; end if;
    end for;

    AssertEqual(~results, all_roots, true,
        Sprintf("N=137: jmap(preimage point) is a root of HilbertClassPolynomial(%o) for all %o preimages of the D=%o locus",
            D, expected_fiber_deg, D));
end procedure;

// D=-11 and D=-4: single rational points on Ystar (from the star-form
// model's rats[], already Q-rational; see target_idxs/idx_to_disc above).
rational_cm_discs := [d : d in target_rational_labels | d ne 0];   // {-11,-4}, drop the cusp
for j in target_idxs do
    D := idx_to_disc[j];
    if D notin rational_cm_discs then continue; end if;   // skip the cusp

    y := [Rationals()!c : c in Eltseq(rats[j])];
    ay_eqns := PointLocusEqns(AY, g, y);
    CertifyCMDiscViaJmap(~results, X137, AX137, BS, g, num, denom, D, ay_eqns, 2);
end for;

// D=-32: the degree-2 component found in Step 3.
CertifyCMDiscViaJmap(~results, X137, AX137, BS, g, num, denom,
    target_degree2_disc, DefiningEquations(compY), 4);


// ------------------------------------------------------------------------
// Step 6: the exceptional point itself. Everything above certifies the
// CM discriminants on the plane, it says nothing about the exceptional
// point, which is the actual substance of the claim (a non-CM point
// sitting coplanar with CM points). Pull it back through rho, compute its
// j-invariant via jmap, and confirm it is not a root of
// HilbertClassPolynomial(D) for any D in rat_cm_discs (computed in Step 1
// via RationalCMDiscs(137)).
//
// rat_cm_discs is not an arbitrary bound to sweep, for squarefree N,
// RationalCMDiscs only ever considers discriminants with class number in
// {2^i : i=0..omega(N)}, and (see src/fields_of_definition.m,
// DegreeOfFieldOfDefinitionOfCMPoint) the field-of-definition-degree
// formula deg = h(R)/2^(omega(N/N_R)-eps) structurally forces h(R) in
// {1,2} for deg=1 to be possible at all when N=137 is prime
// (omega(N)=1). So rat_cm_discs is the provably complete list of
// discriminants that could ever give a rational CM point on X_0(137)*,
// not a heuristic sweep. All 7 of its discriminants were already claimed
// by the other 7 rational points (Step 1), so if the exceptional point's
// j-invariant matches none of them, it is not a rational-CM point of any
// discriminant, full stop; this is a complete check for that class of
// point, not merely evidence.
// ------------------------------------------------------------------------

ay_eqns_exc := PointLocusEqns(AY, g, exc_coords);
eqns_X_exc  := [Evaluate(e, [AX137.i : i in [1..g]]) : e in ay_eqns_exc];
FiberScheme_exc := Scheme(AX137, DefiningEquations(X137) cat eqns_X_exc);
Dfib_exc := Difference(FiberScheme_exc, BS);

AssertEqual(~results, Dimension(Dfib_exc), 0,
    "N=137: the pullback of the exceptional point under rho is 0-dimensional");
AssertEqual(~results, Degree(Dfib_exc), 2,
    "N=137: the pullback of the exceptional point under rho has degree 2");

pb_exc, split_exc := PointsOverSplittingField(Dfib_exc);

AssertEqual(~results, #pb_exc, 2,
    "N=137: found 2 geometric preimage points on X_0(137) for the exceptional point");

printf "\n=== Exceptional point: preimage on X_0(137) and its j-invariant ===\n";
exc_jvals := [* *];
for P in pb_exc do
    Pcoords := Eltseq(P);
    L := Universe(Pcoords);
    numval := Evaluate(num, Pcoords);
    denval := Evaluate(denom, Pcoords);
    error if denval eq 0,
        Sprintf("jmap denominator vanishes at exceptional-point preimage %o.", Pcoords);
    jval := numval/denval;
    printf "  field: %o\n  j = %o\n", L, jval;
    Append(~exc_jvals, jval);
end for;

exc_is_noncm := true;
matched_disc := 0;
for jval in exc_jvals do
    L := Parent(jval);
    for D in rat_cm_discs do
        HD  := HilbertClassPolynomial(D);
        HDL := ChangeRing(HD, L);
        if Evaluate(HDL, jval) eq 0 then
            exc_is_noncm := false;
            matched_disc := D;
        end if;
    end for;
end for;

AssertEqual(~results, exc_is_noncm, true,
    Sprintf("N=137: exceptional point's j-invariant is NOT a root of HilbertClassPolynomial(D) for any D in rat_cm_discs=%o (the complete list of discs that could give a rational CM point on X_0(137)*; matched_disc if failed: %o)",
        rat_cm_discs, matched_disc));


Report(~results, "test_137_jmap");
