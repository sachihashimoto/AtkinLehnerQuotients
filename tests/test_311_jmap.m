///////////////////////////////////////////////////////////////////////////
// Independent certification of every CM discriminant on the N=311
// {D=-19} plane (collinearity4[311] = {-232,-123,-19} in
// tests/test_exceptional_tables.m) via the actual modular curve X_0(311)
// and its j-map, the N=311 analogue of tests/test_137_jmap.m.
//
// Structurally different from the N=137 case: only one of the three CM
// points on this plane is rational (D=-19); D=-123 and D=-232 are both
// class-number-2 conjugate pairs (h(-123)=h(-232)=2), so the plane itself
// cannot be built from 3 known rational points the way tests/test_137_plane.m
// builds it. Instead it is built from the exceptional point plus a
// certified Galois-conjugate pair (CertifiedPlaneFromCMPair, the same
// mechanism, and the same rigor level, tests/test_exceptional_tables.m's
// confirm_deg2:=true path already relies on for collinearity4[311]).
//
// Also structurally different downstream: since D=-123 and D=-232 are both
// degree-2 components of the same plane, there is no a-priori way to say
// which of the two geometric components on the X_0(311)* model below is
// which discriminant, so instead of assuming an order, this test pulls
// each component back through rho, evaluates jmap, and asks which of
// HilbertClassPolynomial(-123) / HilbertClassPolynomial(-232) it is a root
// of, then checks the two components land on the two discriminants
// bijectively.
//
// Steps (mirrors tests/test_137_jmap.m):
//   1. star-form model (src/modelsX0Nstar.m): find exc_coords and the exact
//      integer plane vi through it and the D=-123 conjugate pair, via
//      CertifiedPlaneFromCMPair; confirm (exactly, algebraically) it also
//      contains D=-19, and its other degree-2 component is D=-232
//      (AlgebraicDeg2Matches).
//   2. build X_0(311) and X_0(311)* independently (not via QuadraticPoints'
//      eqs_quos, see the Step 2 comment below for why); check coordinates
//      match the star-form model.
//   3. re-derive the plane and its components natively on that model.
//   4. pull each locus (D=-19 point, both degree-2 components) back through
//      rho : X_0(311) -> X_0(311)* to X_0(311) itself.
//   5. apply jmap and check against the right HilbertClassPolynomial(D);
//      for the two degree-2 components, "right" is determined by trial
//      against both -123 and -232, not assumed.
//
// Run with: tests/run.sh test_311_jmap
//
// This is by far the slowest suite in the repository: measured at 1875 s
// (~31 min) on an Apple M4 Pro. Nearly all of that is the genus-26 pullbacks
// in Steps 4-5; long stretches with no output are expected, not a hang.
// The Step 2 construction and jmap(X311,311) are both far more expensive
// here than at level 137 (X_0(311) has genus 26, vs 11 for X_0(137)); run
// data/starmodels/jmap_311.m's build once ahead of time (see
// src/triple_covers.m's cache helpers) so a normal test run hits the cache.
///////////////////////////////////////////////////////////////////////////

// Loads src/triple_covers.m (which itself loads src/AtkinLehner.m) rather
// than src/AtkinLehner.m directly, purely to reuse its PolyCoeffData /
// PolyFromCoeffData / StrJoin / STAR_CACHE_DIR helpers for the jmap cache
// below, none of the triple-cover machinery itself is used here.
load "src/triple_covers.m";
load "tests/assertions.m";

// ------------------------------------------------------------------------
// jmap(X311, 311) cache; see tests/test_137_jmap.m's header comment for
// why (ring-independent <coeff,exponents> data under data/starmodels/,
// staged through a temp file). At this genus (26) it is the dominant cost
// by a wide margin, so this test is expected to be run against a
// pre-warmed cache in normal use.
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

// ------------------------------------------------------------------------
// eqs_quos(311, [[311]]) cache. For this branch (genus_quo > 1,
// non-hyperelliptic), eqs_quos's own source (QuadraticPoints/models_and_maps.m)
// shows the dominant cost is all_diag_X(N), computing X_0(N)'s own
// genus-26 canonical model via canonic(all_diag_basis(N)), and that
// rho is unconditionally built as a literal coordinate-projection map
// `map<X -> Y | [x[i] : i in coords]>` (never CurveQuotient/Pullback for
// this branch). So caching is just: X's and Y's defining equations (as
// ring-independent <coeff,exponents> data, reusing the same PolyCoeffData
// machinery as the jmap cache above) plus the `coords` index list rho
// projects onto, recovered from DefiningEquations(rho) since eqs_quos
// itself never returns `coords`. Rebuilding rho from cached data is then
// a single cheap `map<...>` constructor call, with no relation-finding
// or modular-symbols computation at all.
// ------------------------------------------------------------------------
function EqsQuosCachePath(N)
    return STAR_CACHE_DIR cat "/eqsquos_" cat Sprint(N) cat ".m";
end function;

function LoadEqsQuosCache(N)
    s := "";
    try
        s := Read(EqsQuosCachePath(N));
    catch e
        return false, _, _, _;
    end try;
    dat := eval s;   // <nX, Xeqns_data, nY, Yeqns_data, coords>
    nX := dat[1];
    RX := PolynomialRing(Rationals(), nX);
    Xeqns := [PolyFromCoeffData(RX, d) : d in dat[2]];
    X311 := Curve(ProjectiveSpace(RX), Xeqns);
    nY := dat[3];
    RY := PolynomialRing(Rationals(), nY);
    Yeqns := [PolyFromCoeffData(RY, d) : d in dat[4]];
    Ystar := Curve(ProjectiveSpace(RY), Yeqns);
    coords := dat[5];
    AX := AmbientSpace(X311);
    rho := map<X311 -> Ystar | [AX.i : i in coords]>;
    return true, X311, Ystar, rho;
end function;

procedure SaveEqsQuosCache(N, X311, Ystar, rho)
    AX := AmbientSpace(X311);
    nX := Dimension(AX) + 1;
    nY := Dimension(AmbientSpace(Ystar)) + 1;
    rho_eqns := DefiningEquations(rho);
    coords := [];
    for e in rho_eqns do
        matches := [k : k in [1..nX] | e eq AX.k];
        error if #matches ne 1,
            "rho is not a pure coordinate-projection map onto distinct ambient coordinates, cannot cache this way.";
        Append(~coords, matches[1]);
    end for;
    Xdata := [PolyCoeffData(f) : f in DefiningEquations(X311)];
    Ydata := [PolyCoeffData(f) : f in DefiningEquations(Ystar)];
    body := Sprintf("<%o, [* %o *], %o, [* %o *], %o>",
        nX, StrJoin(Xdata, ", "), nY, StrJoin(Ydata, ", "), coords);
    tmp := EqsQuosCachePath(N) cat ".tmp" cat Sprint(Random(10^9));
    Write(tmp, body : Overwrite := true);
    System(Sprintf("mv %o %o", tmp, EqsQuosCachePath(N)));
    printf "[cache] saved eqs_quos data for level %o\n", N;
end procedure;

results := NewResults();

target_degree2_discs   := {Integers() | -123, -232};
target_rational_disc   := -19;


// ------------------------------------------------------------------------
// Step 1: the star-form model. Build the exact plane through the
// exceptional point and the D=-123 conjugate pair via
// CertifiedPlaneFromCMPair, then confirm (exactly) it contains D=-19 and
// (algebraically, via AlgebraicDeg2Matches) that its degree-2 components
// are {D=-123, D=-232}.
// ------------------------------------------------------------------------

interesting := check_exceptional_example(311);
N      := interesting[1][1];
rats   := interesting[1][3];
X      := interesting[1][4];
fs     := interesting[1][5];
cm_pts := interesting[1][7];

g := Genus(X);
error if N ne 311 or g ne 4,
    Sprintf("Expected N=311, genus 4; got N=%o, genus %o.", N, g);

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
if #cusp_idxs eq 1 then
    idx_to_disc[cusp_idxs[1]] := 0;
end if;

exceptional_idxs := [j : j in [1..#rats] | not IsDefined(idx_to_disc, j)];
error if #exceptional_idxs ne 1,
    Sprintf("Expected exactly one exceptional point on X_0(311)*; got %o.", exceptional_idxs);
exc_idx := exceptional_idxs[1];
exc_coords := [Rationals()!c : c in Eltseq(rats[exc_idx])];

certified123 := CertifiedPlaneFromCMPair(exc_coords, -123, N, fs, ell_pts, disc_ell_pts);
error if #certified123 eq 0,
    "CertifiedPlaneFromCMPair found no certified plane through the exceptional point and the D=-123 conjugate pair.";

vi := certified123[1][3];
printf "\nN=311 plane (from exceptional point + D=-123 conjugate pair): vi = %o\n", vi;

plane_eqn, comp_degs, on_plane := IntersectWithHyperplane(X, rats, vi);

AssertEqual(~results, comp_degs, [1,1,2,2],
    "N=311: plane meets X in components of degree [1,1,2,2]");

AssertEqual(~results, exc_idx in on_plane, true,
    Sprintf("N=311: exceptional point rats[%o] is on the plane", exc_idx));

rational_labels_on_plane := Sort([
    idx_to_disc[j] : j in on_plane | IsDefined(idx_to_disc, j)
]);
AssertEqual(~results, rational_labels_on_plane, [-19],
    "N=311: rational CM label on plane is {-19}");

deg2pts, rc_cache := Degree2Points(N : max_class_num := 0, compute_fields := true);
matches, inconclusive, records, comp_status :=
    AlgebraicDeg2Matches(X, plane_eqn, deg2pts, N, fs, ell_pts, disc_ell_pts);

AssertEqual(~results, matches, target_degree2_discs,
    Sprintf("N=311: plane's degree-2 components confirm exactly {D=-123,D=-232}  (inconclusive: %o)",
        inconclusive));


// ------------------------------------------------------------------------
// Step 2: build X_0(311) and X_0(311)* independently, not via eqs_quos
// (or load from cache, see EqsQuosCachePath above).
//
// eqs_quos's own g_quo>1/non-hyperelliptic branch (QuadraticPoints/
// models_and_maps.m) does exactly this: all_diag_basis(N), find the
// degree-2 relations among the resulting q-expansions via linear algebra,
// then verify the result via Radical/Dimension/IsIrreducible/Genus on the
// resulting scheme. At genus 26 that verification is the entire cost;
// diagnostics (2026-08-04) showed all_diag_basis, the q-expansions, the
// degree-2 relation-finding, Curve() construction, and Dimension() are
// each under a second and jointly find exactly the Petri-expected 276
// quadrics (Binomial(24,2)) for a genus-26 curve, but IsIrreducible(X)
// alone did not return in 90 seconds (and, per an earlier overnight run,
// not in 10 hours either).
//
// We don't need that verification: canonic() already has a cheap,
// rigorous correctness check that doesn't touch Groebner bases at all:
// re-evaluate each relation against the q-expansions out to the Sturm
// bound and check it vanishes to high enough order (done below). Beyond
// that, we cross-check the final computed j-invariant of the exceptional
// point against Galbraith's independently published value (S. Galbraith,
// "Rational Points on X_0^+(p)", Experimental Math. 8:4 (1999), Table 1)
// in Step 5, a stronger correctness check than Magma's own Genus/
// IsIrreducible on this model would have given us anyway.
// ------------------------------------------------------------------------

have_eqsquos_cache, X311, Ystar, rho := LoadEqsQuosCache(311);
if have_eqsquos_cache then
    printf "\n[cache] loaded eqs_quos data for level 311\n";
else
    printf "\n[cache] no eqs_quos cache for level 311 found, computing (fast: quadrics-only, no Genus/IsIrreducible check)...\n";

    time NB311, new_als311 := all_diag_basis(311);
    dim311 := #NB311;
    error if dim311 ne 26,
        Sprintf("expected all_diag_basis(311) to have dimension 26 (genus of X_0(311)); got %o", dim311);

    prec311 := 5*311;
    L311<q311> := LaurentSeriesRing(Rationals(), prec311);
    time Bexp311 := [L311!qExpansion(NB311[i], prec311) : i in [1..dim311]];

    R311<[xx]> := PolynomialRing(Rationals(), dim311);
    mons311 := MonomialsOfDegree(R311, 2);
    monsq311 := [Evaluate(mon, Bexp311) : mon in mons311];
    V311 := VectorSpace(Rationals(), #mons311);
    W311 := VectorSpace(Rationals(), prec311-10);
    time h311 := hom<V311 -> W311 | [W311![Coefficient(monsq311[i],j) : j in [1..(prec311-10)]] : i in [1..#mons311]]>;
    K311 := Kernel(h311);
    eqns311 := [&+[Eltseq(V311!k)[j]*mons311[j] : j in [1..#mons311]] : k in Basis(K311)];
    eqns311 := [LCM([Denominator(c) : c in Coefficients(eqn)])*eqn : eqn in eqns311];

    printf "found %o degree-2 relations (Petri expectation for genus 26: %o)\n",
        #eqns311, Binomial(dim311-2, 2);
    error if #eqns311 ne Binomial(dim311-2, 2),
        Sprintf("Expected exactly %o quadric relations (Petri, genus 26); got %o; X_0(311) may need cubics too (not implemented here).",
            Binomial(dim311-2,2), #eqns311);

    // Cheap, rigorous correctness check (mirrors canonic()'s own post-loop
    // verification): re-evaluate every relation against the q-expansions
    // out to the Sturm bound for its weight, and require it vanish to
    // higher order than that bound, q-expansion identity to a
    // sufficiently high, weight-dependent precision, not a Groebner-basis
    // argument.
    indexGam311 := Integers()!(311*&*[Rationals() | 1+1/p : p in PrimeDivisors(311)]);
    for eqn in eqns311 do
        wt := 2*Degree(eqn);
        hecke := Ceiling(indexGam311*wt/12);
        Bexp1 := [qExpansion(NB311[i], hecke+10) : i in [1..dim311]];
        error if Valuation(Evaluate(eqn, Bexp1)) le hecke+1,
            "A degree-2 relation failed its Sturm-bound correctness check.";
    end for;
    printf "Sturm-bound correctness check passed for all %o relations.\n", #eqns311;

    time X311 := Curve(ProjectiveSpace(R311), eqns311);
    error if Dimension(X311) ne 1,
        Sprintf("Expected X_0(311) to be 1-dimensional; got %o.", Dimension(X311));

    // Ystar: the w_311-invariant (+1 eigenspace) coordinate subset, same
    // logic as eqs_quos's own g_quo>1/non-hyperelliptic branch, but this
    // sub-curve is only genus 4, so canonic()'s Radical/Genus check on it
    // is cheap (already exercised successfully at N=137).
    w311diag := new_als311[1];
    coordsY := [i : i in [1..dim311] | w311diag[i,i] eq 1];
    error if #coordsY ne g,
        Sprintf("Expected %o w_311-invariant coordinates (genus of X_0(311)*); got %o.", g, #coordsY);

    BplY := [NB311[i] : i in coordsY];
    time Ystar := canonic(BplY);

    AX311 := AmbientSpace(X311);
    rho := map<X311 -> Ystar | [AX311.i : i in coordsY]>;

    SaveEqsQuosCache(311, X311, Ystar, rho);
end if;

// Canonical-curve degree check: a genus-h curve embedded by its own
// canonical map sits in P^{h-1} with degree exactly 2h-2 (Riemann-Roch on
// the canonical divisor class). This is a real, independent invariant of
// the model, unlike Dimension() and the Sturm-bound relation check
// above, it was not verified anywhere else in Step 2. It is also cheap:
// Degree() on a scheme rides on the same Hilbert-series machinery as
// Dimension() (both already shown fast, unlike IsIrreducible; see this
// file's header), not a Groebner-basis/primary-decomposition computation,
// so it costs nothing extra whether X311 came from cache or was just built.
gX311_check := Dimension(AmbientSpace(X311)) + 1;
AssertEqual(~results, gX311_check, 26,
    "N=311: X_0(311) canonical model has 26 ambient coordinates");
AssertEqual(~results, Degree(X311), 2*gX311_check - 2,
    "N=311: X_0(311) canonical model has degree 2*26-2=50 (Riemann-Roch on the canonical embedding)");

AY := AmbientSpace(Ystar);
same_coords := &and[
    &and[Evaluate(eqn, [Rationals()!c : c in Eltseq(rats[j])]) eq 0 : eqn in DefiningEquations(Ystar)]
    : j in [1..#rats]
];
AssertEqual(~results, same_coords, true,
    "N=311: the eqs_quos X_0(311)* model shares coordinates with the star-form model (every rats[] point lies on it)");

error if not same_coords,
    "Cannot continue: the two X_0(311)* models do not share coordinates.";


// ------------------------------------------------------------------------
// Step 3: re-derive the plane natively on Ystar, and confirm it meets it
// in the same component shape [1,1,2,2] found in Step 1.
// ------------------------------------------------------------------------

plane_eqnY := &+[vi[l]*AY.l : l in [1..g]];
ScutY   := Scheme(Ystar, [plane_eqnY]);
compsY  := IrreducibleComponents(ScutY);
degsY   := Sort([Degree(c) : c in compsY]);

AssertEqual(~results, degsY, [1,1,2,2],
    "N=311: plane meets the eqs_quos X_0(311)* model in components of degree [1,1,2,2]");

comps2Y := [c : c in compsY | Degree(c) eq 2];
error if #comps2Y ne 2,
    Sprintf("Expected exactly two degree-2 components; got %o.", #comps2Y);


// ------------------------------------------------------------------------
// Step 4: pull every CM locus on the plane back through rho to X_0(311).
//
// rho is (for this branch of eqs_quos) literally the raw coordinate
// projection x |-> [x[1]:...:x[g]] on X_0(311)'s ambient, checked
// explicitly below (see tests/test_137_jmap.m's Step 4 for why this
// justifies the direct-substitution pullback shortcut used here).
// ------------------------------------------------------------------------

rho_eqns := DefiningEquations(rho);
AX311    := AmbientSpace(X311);

AssertEqual(~results, rho_eqns, [AX311.i : i in [1..g]],
    Sprintf("N=311: rho is the raw coordinate-projection map x |-> [x[1]:...:x[%o]]", g));

error if rho_eqns ne [AX311.i : i in [1..g]],
    "Cannot continue: the direct-substitution pullback shortcut is invalid for this rho.";

BS := BaseScheme(rho);

// Dimension(AmbientSpace(X311))+1, not Genus(X311); Genus() on this
// model is the exact computation we're deliberately avoiding (see Step 2's
// header comment); the ambient coordinate count is already known (26,
// dim of all_diag_basis(311)) without needing it.
gX311 := Dimension(AmbientSpace(X311)) + 1;
R_num := PolynomialRing(Rationals(), gX311);

have_jmap_cache, num, denom := LoadJmapCache(311, R_num);
if have_jmap_cache then
    printf "\n[cache] loaded jmap for level 311\n";
else
    printf "\n[cache] no jmap cache for level 311 found, computing (this is slow at genus %o)...\n", gX311;
    // Call find_rels directly (jmap()'s own internal worker), not jmap(X311,311)
    // itself, jmap's only use of its X parameter is the final
    // map<X -> P^1 | [num,denom]> wrapper, which we never use (only
    // num/denom below). Building that map object would require Magma to
    // reason about X311's structure (e.g. common components with the base
    // locus) that we deliberately did not verify in Step 2, calling
    // find_rels directly avoids touching X311 for this at all.
    jL<jq> := LaurentSeriesRing(Rationals());
    jE4 := Eisenstein(4, jq : Precision := 5*311);
    jE6 := Eisenstein(6, jq : Precision := 5*311);
    jfun := 1728*jE4^3/(jE4^3 - jE6^2);
    jdegj := 311*(&*[Rationals() | 1+1/p : p in PrimeFactors(311)]);
    jB := all_diag_basis(311);
    jBexp := [jL!qExpansion(jB[i], 5*311+1) : i in [1..#jB]];
    jr := Ceiling((jdegj / (2*(#jB-1))) + 1/2);
    time num, denom := find_rels(jL, jB, jBexp, 311, jfun, jdegj, jr, 5*311, 5*311+1, #jB);
    SaveJmapCache(311, num, denom);
end if;

function PointLocusEqns(AY, g, y)
    piv := [k : k in [1..g] | y[k] ne 0][1];
    return [AY.k*y[piv] - AY.piv*y[k] : k in [1..g] | k ne piv];
end function;

// Pull ay_eqns (the AY-side equations of a locus) back through rho, and
// return the 0-dimensional fiber scheme's geometric points (over its own
// splitting field), plus the fiber's dimension and degree for the caller
// to Expect(), a plain function, not a procedure, so it cannot itself
// take the ~nfail/~failures ref-parameters (Magma reserves those for
// procedures); the Expect() calls happen at each call site instead.
function PullbackFiberRaw(X311, AX311, BS, g, ay_eqns)
    eqns_X      := [Evaluate(e, [AX311.i : i in [1..g]]) : e in ay_eqns];
    FiberScheme := Scheme(AX311, DefiningEquations(X311) cat eqns_X);
    Dfib        := Difference(FiberScheme, BS);
    dim         := Dimension(Dfib);
    deg         := Degree(Dfib);
    pb, split   := PointsOverSplittingField(Dfib);
    return pb, dim, deg;
end function;

// jmap-evaluate every point in pb; return true iff all are roots of
// HilbertClassPolynomial(D).
function AllRootsOfH(pb, num, denom, D)
    HD := HilbertClassPolynomial(D);
    for P in pb do
        Pcoords := Eltseq(P);
        L := Universe(Pcoords);
        numval := Evaluate(num, Pcoords);
        denval := Evaluate(denom, Pcoords);
        if denval eq 0 then return false; end if;
        jval := numval/denval;
        HDL  := ChangeRing(HD, L);
        if Evaluate(HDL, jval) ne 0 then return false; end if;
    end for;
    return true;
end function;

// --- D=-19: single rational point on Ystar. ---
d19_idxs := [j : j in [1..#rats] | IsDefined(idx_to_disc, j) and idx_to_disc[j] eq target_rational_disc];
error if #d19_idxs ne 1,
    Sprintf("Expected exactly one rats[] index labelled D=-19; got %o.", d19_idxs);
y19 := [Rationals()!c : c in Eltseq(rats[d19_idxs[1]])];
ay_eqns19 := PointLocusEqns(AY, g, y19);

pb19, dim19, deg19 := PullbackFiberRaw(X311, AX311, BS, g, ay_eqns19);

AssertEqual(~results, dim19, 0,
    "N=311: the pullback of the D=-19 locus under rho is 0-dimensional");
AssertEqual(~results, deg19, 2,
    "N=311: the pullback of the D=-19 locus under rho has degree 2");
AssertEqual(~results, #pb19, 2,
    "N=311: found 2 geometric preimage points on X_0(311) for the D=-19 locus");

all_roots19 := AllRootsOfH(pb19, num, denom, target_rational_disc);
AssertEqual(~results, all_roots19, true,
    "N=311: jmap(preimage point) is a root of HilbertClassPolynomial(-19) for both preimages of the D=-19 locus");

for P in pb19 do
    Pcoords := Eltseq(P);
    numval := Evaluate(num, Pcoords); denval := Evaluate(denom, Pcoords);
    printf "  D=-19 preimage j = %o\n", denval eq 0 select "undefined" else numval/denval;
end for;


// --- D=-123, D=-232: the two degree-2 components, identified by which
// Hilbert class polynomial their preimages' j-invariants satisfy (not
// assumed in advance, see file header). ---
matched_discs := {Integers()|};
// Indexed rather than `for compY in comps2Y` so each assertion label names
// which of the two degree-2 components failed.
for ci in [1..#comps2Y] do
    compY := comps2Y[ci];
    pb, dim, deg := PullbackFiberRaw(X311, AX311, BS, g, DefiningEquations(compY));

    AssertEqual(~results, dim, 0,
        Sprintf("N=311: degree-2 component %o: pullback under rho is 0-dimensional", ci));
    AssertEqual(~results, deg, 4,
        Sprintf("N=311: degree-2 component %o: pullback under rho has degree 4", ci));
    AssertEqual(~results, #pb, 4,
        Sprintf("N=311: degree-2 component %o: found 4 geometric preimage points on X_0(311)", ci));

    hits := [D : D in target_degree2_discs | AllRootsOfH(pb, num, denom, D)];

    printf "\ndegree-2 component %o: matches HilbertClassPolynomial candidates %o\n",
        DefiningEquations(compY), hits;
    for P in pb do
        Pcoords := Eltseq(P);
        numval := Evaluate(num, Pcoords); denval := Evaluate(denom, Pcoords);
        printf "  preimage j = %o\n", denval eq 0 select "undefined" else numval/denval;
    end for;

    AssertEqual(~results, #hits, 1,
        Sprintf("N=311: degree-2 component %o: preimages are roots of exactly one of HilbertClassPolynomial(-123)/(-232) (matches: %o)", ci, hits));

    if #hits eq 1 then
        AssertEqual(~results, hits[1] notin matched_discs, true,
            Sprintf("N=311: degree-2 component %o: D=%o not already claimed by the other component (duplicate match)", ci, hits[1]));
        Include(~matched_discs, hits[1]);
    end if;
end for;

AssertEqual(~results, matched_discs, target_degree2_discs,
    "N=311: the two degree-2 components jmap-match {D=-123,D=-232} bijectively");


// ------------------------------------------------------------------------
// Step 5: the exceptional point itself. Everything above certifies the CM
// discriminants on the plane, it says nothing about the exceptional
// point, which is the actual substance of the claim (a non-CM point
// sitting coplanar with CM points). Pull it back through rho, compute its
// j-invariant via jmap, and confirm it is not a root of
// HilbertClassPolynomial(D) for any D in rat_cm_discs (computed in Step 1
// via RationalCMDiscs(311)).
//
// rat_cm_discs is not an arbitrary bound to sweep, exactly as for
// N=137 (see tests/test_137_jmap.m's Step 6), RationalCMDiscs only ever
// considers discriminants with class number in {2^i : i=0..omega(N)}, and
// the field-of-definition-degree formula forces h(R) in {1,2} for deg=1
// to be possible at all when N=311 is prime (omega(N)=1). So
// rat_cm_discs is the provably complete list of discriminants that could
// ever give a rational CM point on X_0(311)*, not a heuristic sweep.
// D=-19 already claims one of its members (Step 1); if the exceptional
// point's j-invariant matches none of them, it is not a rational-CM point
// of any discriminant, full stop.
// ------------------------------------------------------------------------

ay_eqns_exc := PointLocusEqns(AY, g, exc_coords);
pb_exc, dim_exc, deg_exc := PullbackFiberRaw(X311, AX311, BS, g, ay_eqns_exc);

AssertEqual(~results, dim_exc, 0,
    "N=311: the pullback of the exceptional point under rho is 0-dimensional");
AssertEqual(~results, deg_exc, 2,
    "N=311: the pullback of the exceptional point under rho has degree 2");
AssertEqual(~results, #pb_exc, 2,
    "N=311: found 2 geometric preimage points on X_0(311) for the exceptional point");

printf "\n=== Exceptional point: preimage on X_0(311) and its j-invariant ===\n";
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
    Sprintf("N=311: exceptional point's j-invariant is NOT a root of HilbertClassPolynomial(D) for any D in rat_cm_discs=%o (the complete list of discs that could give a rational CM point on X_0(311)*; matched_disc if failed: %o)",
        rat_cm_discs, matched_disc));


// =========================================================================
// Summary
// =========================================================================
printf "\n";
Report(~results, "test_311_jmap");
