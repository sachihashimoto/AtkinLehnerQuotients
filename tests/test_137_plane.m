///////////////////////////////////////////////////////////////////////////
// Exact coplanarity test for {-32, -11, -4, 0} on the N = 137 example.
// The label 0 denotes the cusp.
///////////////////////////////////////////////////////////////////////////

load "src/AtkinLehner.m";
load "tests/assertions.m";

results := NewResults();

// Construct the example.
interesting := check_exceptional_example(137);
N:=interesting[1][1];
 n:=interesting[1][2];
 rats:= interesting[1][3];
  X:=interesting[1][4];
   fs:= interesting[1][5];
    Sstar:=interesting[1][6];
     cm_pts :=interesting[1][7];
   
///////////////////////////////////////////////////////////////////////////
// Test the configuration {-32, -11, -4, 0} on X_0(137)^*.
//
// Interpretation:
//   -11, -4, and 0 are rational points (0 = cusp);
//   -32 is a degree-2 closed CM point, consisting of two conjugate
//   geometric points.
//
// This script:
//   1. identifies the rational CM points and cusp;
//   2. constructs the exact plane through {-11, -4, 0};
//   3. checks the D=-32 conjugates numerically at independent precisions;
//   4. confirms D=-32 against an exact degree-2 intersection component.
///////////////////////////////////////////////////////////////////////////


// ------------------------------------------------------------------------
// Parameters.
// ------------------------------------------------------------------------

target_degree2_disc := -32;
target_rational_labels := {Integers() | -11, -4, 0};

prec_lo   := 200;
prec_hi   := 600;
resid_C   := 10^3;
error_max := 10^-12;
expected_exceptional_idx := 8;


// ------------------------------------------------------------------------
// Construct the N=137 example.
// ------------------------------------------------------------------------

g := Genus(X);

error if N ne 137,
    Sprintf("Expected N=137, but received N=%o.", N);

error if g ne 4,
    Sprintf(
        "Expected a genus-4 canonical curve in P^3, but genus is %o.",
        g
    );

printf "\nN = %o\n", N;
printf "Genus = %o\n", g;
printf "Number of rational points = %o\n", #rats;


// ------------------------------------------------------------------------
// Extract the rational CM discriminants.
// ------------------------------------------------------------------------

if Type(cm_pts) eq Assoc then
    rat_cm_discs := {Integers() | d : d in Keys(cm_pts)};

elif Type(cm_pts) eq SetEnum then
    rat_cm_discs := {Integers() | d : d in cm_pts};

elif Type(cm_pts) eq SeqEnum then
    rat_cm_discs := {Integers() | d : d in cm_pts};

else
    error Sprintf(
        "Unexpected type for cm_pts: %o. Expected an associative array, set, or sequence.",
        Type(cm_pts)
    );
end if;

printf "Rational CM discriminants: %o\n",
    Sort(Setseq(rat_cm_discs));


// ------------------------------------------------------------------------
// Match the rational CM discriminants to rats[].
// ------------------------------------------------------------------------

CC  := ComplexField(200);
tol := 10^-15;

rats_cc := [
    [CC!c : c in Eltseq(rats[j])]
    : j in [1..#rats]
];

ell_pts, disc_ell_pts := EllipticDiscsByOrder(N);

matched, match_nfail, disc_to_idx, fail_reason :=
    MatchRationalCMPoints(
        N,
        fs,
        rats_cc,
        rats,
        CC,
        tol,
        rat_cm_discs,
        ell_pts,
        disc_ell_pts
    );

// match_nfail is MatchRationalCMPoints' own failure count, unrelated to (and
// previously accidentally aliased with) this file's Expect-harness `nfail`
// accumulator above, kept as a distinct name so the harness counter is
// never silently reset.
error if match_nfail ne 0,
    Sprintf("Rational CM matching failed: %o", fail_reason);


// Construct the inverse map rats-index -> discriminant.

idx_to_disc := AssociativeArray();

for disc in Keys(disc_to_idx) do
    for j in disc_to_idx[disc] do
        error if IsDefined(idx_to_disc, j),
            Sprintf(
                "rats[%o] received both labels %o and %o.",
                j,
                idx_to_disc[j],
                disc
            );

        idx_to_disc[j] := disc;
    end for;
end for;


// ------------------------------------------------------------------------
// Locate the cusp and assign it the sentinel label 0.
// ------------------------------------------------------------------------

cusp_cc := [
    CC!Coefficient(fs[i], 1)
    : i in [1..g]
];

cusp_idxs := [
    j : j in [1..#rats]
    | IsProjectivelyEquivalent(rats_cc[j], cusp_cc, tol)
];

error if #cusp_idxs eq 0,
    "The cusp was not found among rats.";

error if #cusp_idxs gt 1,
    Sprintf(
        "The cusp matched multiple rational points: %o.",
        cusp_idxs
    );

cusp_idx := cusp_idxs[1];

error if IsDefined(idx_to_disc, cusp_idx),
    Sprintf(
        "The cusp rats[%o] was already labelled D=%o.",
        cusp_idx,
        idx_to_disc[cusp_idx]
    );

idx_to_disc[cusp_idx] := 0;

printf "\nCusp D=0 -> rats[%o] = %o\n",
    cusp_idx,
    rats[cusp_idx];


// ------------------------------------------------------------------------
// Identify the exceptional point (the one rats[] index with no CM/cusp
// label): N=137's genus-4 model has exactly one, at rats[8].
// ------------------------------------------------------------------------

exceptional_idxs := [j : j in [1..#rats] | not IsDefined(idx_to_disc, j)];

AssertEqual(~results, #exceptional_idxs, 1,
    Sprintf("N=137: exactly one exceptional point  (got %o)", exceptional_idxs));

// Sentinel -1 (never a valid rats[] index) if the count check above failed,
// so the equality check below can never index out of range.
exc_idx := (#exceptional_idxs eq 1) select exceptional_idxs[1] else -1;

AssertEqual(~results, exc_idx, expected_exceptional_idx,
    "N=137: exceptional point index");

error if #exceptional_idxs ne 1,
    "Cannot continue: need exactly one exceptional point.";
printf "\nExceptional point -> rats[%o] = %o\n", exc_idx, rats[exc_idx];


// ------------------------------------------------------------------------
// Find the three rational points D=-11, D=-4, and the cusp.
// ------------------------------------------------------------------------

target_idxs := Sort([
    j : j in Keys(idx_to_disc)
    | idx_to_disc[j] in target_rational_labels
]);

found_labels := {
    Integers() | idx_to_disc[j]
    : j in target_idxs
};

error if found_labels ne target_rational_labels,
    Sprintf(
        "Could not find all rational target labels. Requested %o; found %o.",
        Sort(Setseq(target_rational_labels)),
        Sort(Setseq(found_labels))
    );

error if #target_idxs ne 3,
    Sprintf(
        "Expected three rational target points, but found indices %o.",
        target_idxs
    );

printf "\nRational target points:\n";

for j in target_idxs do
    printf "  D=%o -> rats[%o] = %o\n",
        idx_to_disc[j],
        j,
        rats[j];
end for;


// ------------------------------------------------------------------------
// Construct the exact plane through the three rational points.
// ------------------------------------------------------------------------

target_coords := [
    [Rationals()!c : c in Eltseq(rats[j])]
    : j in target_idxs
];

M := Matrix(Rationals(), target_coords);

error if Rank(M) lt 3,
    "The three rational target points are collinear, so they do not determine a unique plane.";

ok, vi := HyperplaneFromPoints(g, target_coords);

error if not ok,
    "HyperplaneFromPoints failed to construct the plane.";


// Verify the three rational points exactly.

for j in target_idxs do
    value := &+[
        vi[k] * Eltseq(rats[j])[k]
        : k in [1..g]
    ];

    error if value ne 0,
        Sprintf(
            "Internal error: D=%o at rats[%o] does not satisfy the plane equation.",
            idx_to_disc[j],
            j
        );
end for;

// The plane is built only from the three rational points {-11,-4,cusp};
// this checks (exactly, in rational arithmetic, no floating point involved)
// that it also contains the exceptional point rats[8], which is the claim
// this whole test exists to certify.
exc_value := &+[
    vi[k] * Eltseq(rats[exc_idx])[k]
    : k in [1..g]
];

AssertEqual(~results, exc_value, 0,
    Sprintf("N=137: plane through {D=-11,D=-4,cusp} contains the exceptional point rats[%o] exactly", exc_idx));

// Canonical (sign-normalized) coefficient check: the distinct plane
// 2*z[2] - z[3] - 2*z[4] = 0, i.e. primitive vector [0,2,-1,-2] up to sign.
AssertEqual(~results, CanonicalPlaneKey(vi), [0,2,-1,-2],
    "N=137: plane coefficients are [0,2,-1,-2] up to sign");


plane_eqn, comp_degs, on_plane :=
    IntersectWithHyperplane(X, rats, vi);

rational_labels_on_plane := Sort([
    idx_to_disc[j]
    : j in on_plane
    | IsDefined(idx_to_disc, j)
]);

printf "\nExact plane through D=-11, D=-4, and the cusp:\n";
printf "  primitive coefficients: %o\n", vi;
printf "  plane equation: %o = 0\n", plane_eqn;
printf "  intersection component degrees: %o\n", comp_degs;
printf "  rational CM/cusp labels on plane: %o\n",
    rational_labels_on_plane;

AssertEqual(~results, comp_degs, [1,1,1,1,2],
    "N=137: plane meets X in components of degree [1,1,1,1,2]");

AssertEqual(~results, rational_labels_on_plane, [-11,-4,0],
    "N=137: rational CM/cusp labels on plane are {-11,-4,0}");

AssertEqual(~results, exc_idx in on_plane, true,
    Sprintf("N=137: exceptional point rats[%o] is in on_plane index list", exc_idx));


// ------------------------------------------------------------------------
// Preliminary numerical check:
// test pairs of independently converged D=-32 evaluations against the plane.
// ------------------------------------------------------------------------

CC_lo, CC_hi, evs32 :=
    CertifiedConjugateEvaluations(
        target_degree2_disc,
        N,
        fs,
        ell_pts,
        disc_ell_pts,
        prec_lo,
        prec_hi
    );

orbit_ids := Sort(Setseq(Keys(evs32)));

printf "\nConverged orbit IDs for D=%o: %o\n",
    target_degree2_disc,
    orbit_ids;

numerically_on_plane_pairs := [* *];

if #orbit_ids ge 2 then
    for ii in [1..#orbit_ids] do
        for jj in [ii+1..#orbit_ids] do
            i := orbit_ids[ii];
            j := orbit_ids[jj];

            observed_error :=
                Maximum(evs32[i][3], evs32[j][3]);

            ok_tol, pair_tol :=
                AdaptiveTol(
                    observed_error,
                    resid_C,
                    error_max,
                    prec_lo
                );

            if not ok_tol then
                printf
                    "  orbit pair (%o,%o): INCONCLUSIVE; observed error %o exceeds error_max %o\n",
                    i, j, observed_error, error_max;
                continue;
            end if;

            residuals := [
                ScaleInvariantResidual(vi, evs32[i][1]),
                ScaleInvariantResidual(vi, evs32[j][1]),
                ScaleInvariantResidual(vi, evs32[i][2]),
                ScaleInvariantResidual(vi, evs32[j][2])
            ];

            printf
                "  orbit pair (%o,%o): max residual=%o, tolerance=%o, observed error=%o\n",
                i,
                j,
                Maximum(residuals),
                pair_tol,
                observed_error;

            if Maximum(residuals) le pair_tol then
                Append(
                    ~numerically_on_plane_pairs,
                    <i, j, Maximum(residuals), pair_tol>
                );
            end if;
        end for;
    end for;
end if;

if #numerically_on_plane_pairs eq 0 then
    printf
        "Preliminary result: no D=%o conjugate pair passed the plane-residual test.\n",
        target_degree2_disc;
else
    printf
        "Preliminary result: D=%o has %o conjugate pair(s) passing both independent runs.\n",
        target_degree2_disc,
        #numerically_on_plane_pairs;

    print numerically_on_plane_pairs;
end if;


// ------------------------------------------------------------------------
// Strong component-level check.
//
// Degree2Points computes the degree-2 CM data and possible fields of
// definition. AlgebraicDeg2Matches compares the exact algebraic points on
// each degree-2 intersection component with the independently evaluated
// D=-32 CM conjugates.
// ------------------------------------------------------------------------

rc_cache := AssociativeArray();

deg2pts, rc_cache :=
    Degree2Points(
        N :
        max_class_num := 0,
        compute_fields := true,
        rc_cache := rc_cache
    );

error if not IsDefined(deg2pts, target_degree2_disc),
    Sprintf(
        "D=%o was not returned by Degree2Points(%o).",
        target_degree2_disc,
        N
    );

matches, inconclusive, records, comp_status :=
    AlgebraicDeg2Matches(
        X,
        plane_eqn,
        deg2pts,
        N,
        fs,
        ell_pts,
        disc_ell_pts :
        prec_lo := prec_lo,
        prec_hi := prec_hi,
        resid_C := resid_C,
        error_max_match := error_max
    );

// Per-(component,disc) records status is one of {"confirmed","rejected","inconclusive"}
//, field-incompatible pairs are absent entirely (a prefilter). The aggregate,
// final per-component conclusion is in comp_status instead, status in
// {"confirmed","ambiguous","inconclusive","unlabelled"}; see
// AlgebraicDeg2Matches's header in src/labelling.m for exactly what each means
// and why "unlabelled" is a component-level, not per-disc, outcome.
records32 := [*
    r : r in records
    | r[2] eq target_degree2_disc
*];

comp_status32 := [*
    c : c in comp_status
    | target_degree2_disc in c[3]
*];

confirmed_records32   := [* r : r in records32 | r[3] eq "confirmed" *];
rejected_records32     := [* r : r in records32 | r[3] eq "rejected" *];
inconclusive_records32 := [* r : r in records32 | r[3] eq "inconclusive" *];
ambiguous_components32 := [* c : c in comp_status32 | c[2] eq "ambiguous" *];
unlabelled_components32 := [* c : c in comp_status32 | c[2] eq "unlabelled" *];

printf "\nComponent records for D=%o:\n",
    target_degree2_disc;

print records32;

printf "All confirmed degree-2 discriminants on the plane: %o\n",
    Sort(Setseq(matches));

printf "All inconclusive degree-2 discriminants on the plane: %o\n",
    Sort(Setseq(inconclusive));


// ------------------------------------------------------------------------
// Final conclusion: this is the regression check this test exists for.
// ------------------------------------------------------------------------

// The authoritative claim is comp_status (the final, aggregate per-component
// outcome), not merely "some per-disc record says confirmed"; a disc whose
// record says "confirmed" but whose component is "ambiguous" is not actually
// confirmed. matches already encodes this correctly (see AlgebraicDeg2Matches
// header), so target_degree2_disc in matches is the right test.
degree2_confirmed := target_degree2_disc in matches;

AssertEqual(~results, degree2_confirmed, true,
    Sprintf("N=137: plane {D=-11,D=-4,cusp} + exceptional point confirms its remaining degree-2 component as D=-32  (records: %o, comp_status: %o)",
        records32, comp_status32));

printf "\n============================================================\n";

if degree2_confirmed then

    printf "CONFIRMED:\n";
    printf "  The exact plane %o = 0 contains:\n", plane_eqn;
    printf "    - the rational CM point D=-11;\n";
    printf "    - the rational CM point D=-4;\n";
    printf "    - the cusp D=0;\n";
    printf "    - the exceptional point rats[%o];\n", exc_idx;
    printf "    - the degree-2 CM point D=%o.\n",
        target_degree2_disc;

    printf "  Confirmed component record(s): %o\n",
        confirmed_records32;

elif #ambiguous_components32 gt 0 then

    printf "AMBIGUOUS:\n";
    printf "  D=%o's component also confirmed a DIFFERENT discriminant,\n",
        target_degree2_disc;
    printf "  needs manual disambiguation, not an automatic label.\n";
    printf "  Ambiguous component(s): %o\n",
        ambiguous_components32;

elif #inconclusive_records32 gt 0 then

    printf "INCONCLUSIVE:\n";
    printf "  The exact rational plane was found, but D=%o could not be\n",
        target_degree2_disc;
    printf "  conclusively matched to its degree-2 component (insufficient\n";
    printf "  numerical accuracy). Increase q-expansion length and/or prec_hi.\n";
    printf "  Inconclusive record(s): %o\n",
        inconclusive_records32;

else

    printf "NOT CONFIRMED:\n";
    printf "  The exact plane through {-11,-4,0} was found, but D=%o was\n",
        target_degree2_disc;
    printf "  tested at sufficient accuracy and definitively did NOT match\n";
    printf "  any degree-2 component of that plane.\n";
    printf "  Rejected record(s): %o\n",
        rejected_records32;
    printf "  Unlabelled component(s) (if any): %o\n",
        unlabelled_components32;

end if;

printf "============================================================\n";


Report(~results, "test_137_plane");