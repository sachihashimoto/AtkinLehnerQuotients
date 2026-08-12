// tests/test_cm_field_observed.m
//
// Cross-check FieldsOfDefinitionOfCMPoint (src/fields_of_definition.m) against the
// field the curve actually has: evaluate the CM point on the star model of
// X_0(N)^*, recognize its coordinates as algebraic numbers, and compare the field
// they generate with the predicted candidate list.
//
// This is deliberately a different kind of check from
// tests/test_cm_field_of_definition.m.  That test pins our implementation against a
// second implementation of the same Gonzalez-Rotger formula (SchoferFormula.m via
// scripts/gen_cm_field_expectations.m), so a shared misunderstanding of the formula
// would pass it.  Nothing on the observed side here consults
// FieldsOfDefinitionOfCMPoint at all, the observed field comes from
// PowerRelation on the numerical coordinates (RecognizePoint, src/labelling.m).
//
// The motivating row is N = 286, d = -39: the exact case that prompted the 2026-08-08
// fast port (see the header of tests/test_cm_field_of_definition.m for the spurious
// multi-valuedness it removed).  The old H_R-based code returned
// {Q(sqrt -3), Q(sqrt 13)}; the current code returns {Q(sqrt 13)}.  The curve
// independently says Q(sqrt 13).
//
// Two evaluation paths.  The evaluator must match the model class, and this is not a
// detail: running the canonical evaluator on a hyperelliptic model yields the field
// of a P^1 x-coordinate rather than of a point on the curve, which at N = 286,
// d = -352 reports Q for a genuinely quadratic point.
//   canonical      (109, 113, 137, 311): EvaluateAtCM via CertifiedConjugateEvaluations
//   hyperelliptic  (154, 285, 286):      EvaluateAtCM_hyperelliptic, plus a y^2 - P(x)
//                                        residual as an independent on-curve check
// 154, 285 and 286 are the only hyperelliptic levels among the 84 committed
// data/starmodels/starforms_*.m caches (the only ones with #fs <= 2); none of
// Hasegawa's genus->=3 hyperelliptic levels (136, 171, 176, 207, 252, 279, 315) is
// cached.  Only cached levels are used, so this test never triggers an
// all_diag_basis rebuild.
//
// Precision truncation is the load-bearing step.  PowerRelation works at the full
// working precision of its argument, but the evaluation is only accurate to as many
// digits as the q-expansion length supports; feeding it 600 digits when 47 are real
// makes it fit the noise.  Measured: N = 137, d = -1507 returns a spurious degree-4
// field that way, and at 500 q-expansion terms one orbit (error 2.5e-4) returned a
// degree-8 field and took 34 seconds.  So the working precision is derived from the
// measured error, in the same spirit as AdaptiveTol deriving a tolerance from a run's
// own noise.
//
// The recognition window is bounded on both sides, too few digits and PowerRelation
// fits a spurious low-height relation, too many and it fits noise; which is why a
// single truncation is not enough and both FRACS must agree.  Every measured
// degree-4 misfire sat below 20 digits of truncation:
//     N=154 d=-8008 orb2 (66 digits): wrong at 19, right at 33 and 59
//     N=154 d=-2772 orb2 (50 digits): wrong at 15, right at 25 and 45
//     N=154 d=-616  orb2 (54 digits): wrong at 16, right at 27 and 48
//     N=154 d=-308  orb2 (66 digits): wrong at 19, right at 33 and 59
//     N=285 d=-8835 orb2 (58 digits): wrong at 17, right at 29 and 52
//     N=285 d=-915  orb2 (27 digits): wrong at  8, right at 13 and 24
//     N=286 d=-8008 orb2 (34 digits): wrong at 10 and 17, right at 30
//     N=286 d=-468  orb2 (18 digits): wrong at  8 and  9, right at 16
// GATE_DIGITS = 40 forces Floor(0.5*digits) >= 20, above every misfire above; under
// that rule there were zero wrong or unstable recognitions across all 78 rows.
// Fractions 0.3/0.5 and 0.5/0.9 were also verified to agree on all 104 canonical
// recognitions, so the window is wide wherever the gate passes.
//
// The gate errs toward excluding usable rows, not toward admitting bad ones:
// observed_error is dominated by the half-length truncation, so a row reporting 41
// digits typically has a full-length evaluation good to ~87 (confirmed by the
// y^2 - P(x) residuals, which run from 1e-87 at N=286 d=-39 to 1e-597 at d=-1768).
//
// Each row is <N, d, expected_tag, n_usable_orbits>.  expected_tag is recorded as a
// third, independent value so the prediction and the observation cannot drift
// together into agreement.  n_usable_orbits is recorded so a convergence regression
// fails the row rather than silently shrinking the work done, `magma -b` happily
// continues past errors, so a test that skips quietly is a test that passes for free.
//
// Roughly half the degree-2 discriminants at the canonical levels are absent below
// because CMTauReps returns a representative with small Im(tau) (see
// docs/handoff/TAU-REWORK-SPEC.md); better representatives would widen coverage with
// no change to this test's logic.
//
// This is a strong numerical check, not a proof: EvaluateAtCM and
// EvaluateAtCM_hyperelliptic are not ball arithmetic and carry no certified
// q-expansion tail bound (the same caveat CertifiedPlaneFromCMPair's header states).
//
// Run from the repo root: tests/run.sh test_cm_field_observed

load "src/AtkinLehner.m";
load "tests/assertions.m";

results := NewResults();

// Tag a field of degree <= 2 by the squarefree part of its discriminant (1 for Q);
// tag higher-degree fields by 10000*degree.  Must match FieldTag() in
// tests/test_cm_field_of_definition.m and Tag() in
// scripts/gen_cm_field_expectations.m.
function FieldTag(F)
    if Type(F) eq FldRat then return 1; end if;
    if Degree(F) eq 1 then return 1; end if;
    if Degree(F) gt 2 then return 10000*Degree(F); end if;
    return Squarefree(Discriminant(MaximalOrder(F)));
end function;

function FieldDegree(K)
    return Type(K) eq FldRat select 1 else Degree(K);
end function;

// IsIsomorphic is not available across FldRat/FldNum, so compare degrees first.
function SameField(K1, K2)
    d1 := FieldDegree(K1); d2 := FieldDegree(K2);
    if d1 ne d2 then return false; end if;
    if d1 eq 1 then return true; end if;
    return IsIsomorphic(K1, K2);
end function;

EVAL_PREC   := 3000;   // matches the committed cache length; no rebuild is triggered
PREC_LO     := 200;
PREC_HI     := 600;
GATE_DIGITS := 40;
FRACS       := [0.5, 0.9];

// Trustworthy decimal digits implied by a measured error, capped at the working
// precision when the error rounds to exactly 0.
function DigitsOf(err, cap)
    if err eq 0 then return cap; end if;
    return Minimum(cap, Floor(-Log(10, err)));
end function;

// Recognize ev as a point over a number field at both truncations in FRACS.
// Returns <ok, K, why>: ok is false (with a reason) if either recognition throws or
// the two disagree, a lucky recognition at one truncation is not evidence.
function ObservedField(ev, digits)
    Ks := [* *];
    for frac in FRACS do
        r   := Floor(frac*digits);
        CCr := ComplexField(r);
        try
            K, _ := RecognizePoint([CCr ! z : z in ev], CCr);
            Append(~Ks, K);
        catch e
            return false, 0, Sprintf("RecognizePoint threw at truncation %o", r);
        end try;
    end for;
    if not SameField(Ks[1], Ks[2]) then
        return false, 0, Sprintf("truncations %o and %o disagree (deg %o tag %o vs deg %o tag %o)",
            Floor(FRACS[1]*digits), Floor(FRACS[2]*digits),
            FieldDegree(Ks[1]), FieldTag(Ks[1]), FieldDegree(Ks[2]), FieldTag(Ks[2]));
    end if;
    return true, Ks[1], "";
end function;

// Elliptic ramification order at CM discriminant d, as EvaluateAtCM* expects it.
function EllOrder(d, ell_pts, disc_ell_pts)
    if d notin disc_ell_pts then return 1; end if;
    for ell in [2, 3, 4, 6] do
        if d in Keys(ell_pts[ell]) then return ell; end if;
    end for;
    return 1;
end function;

// <N, d, expected_tag, n_usable_orbits>.  Rows marked "multi-valued" are the ones
// where FieldsOfDefinitionOfCMPoint returns more than one candidate and the
// observation selects exactly one of them.
CANON_ROWS := [
    // N = 109
    <109, -267, 89, 2>,
    <109, -187, -11, 2>,
    <109, -100, 5, 2>,        // multi-valued: {5, -5} -> 5    (contrast N = 137 below)
    <109, -88, -11, 2>,
    <109, -64, -2, 2>,        // multi-valued: {2, -2} -> -2
    // N = 113
    <113, -267, -3, 2>,
    <113, -235, -47, 2>,
    <113, -115, -23, 2>,
    <113, -100, -5, 2>,       // multi-valued: {5, -5} -> -5
    <113, -99, -3, 2>,        // multi-valued: {33, -3} -> -3
    <113, -88, 2, 2>,
    <113, -72, -3, 2>,        // multi-valued: {6, -3} -> -3
    <113, -60, -3, 2>,
    <113, -51, -3, 2>,
    <113, -36, -3, 2>,        // multi-valued: {3, -3} -> -3
    // N = 137
    <137, -403, -31, 2>,
    <137, -267, -3, 2>,
    <137, -235, -47, 2>,
    <137, -148, 37, 2>,
    <137, -123, -3, 2>,
    <137, -115, -23, 2>,
    <137, -100, -5, 2>,       // multi-valued: {5, -5} -> -5, where N = 109 gives 5
    <137, -99, -3, 2>,        // multi-valued: {33, -3} -> -3
    <137, -72, -3, 2>,        // multi-valued: {6, -3} -> -3
    <137, -60, -3, 2>,
    <137, -36, -3, 2>,        // multi-valued: {3, -3} -> -3
    // N = 311
    <311, -427, -7, 2>,
    <311, -232, -2, 2>
];

HYP_ROWS := [
    // N = 154
    <154, -8932, 319, 2>,
    <154, -8008, 14, 2>,
    <154, -2772, 11, 2>,
    <154, -1672, -2, 2>,
    <154, -952, -119, 2>,
    <154, -868, -31, 2>,
    <154, -616, 22, 2>,
    <154, -448, -14, 2>,      // multi-valued: {2, -14} -> -14
    <154, -420, 15, 2>,
    <154, -308, 11, 2>,
    <154, -292, 73, 2>,
    <154, -264, -2, 2>,
    <154, -252, -3, 2>,       // multi-valued: {21, -3} -> -3, where d = -63 gives 21
    <154, -220, -11, 2>,
    <154, -68, 17, 2>,
    <154, -63, 21, 2>,        // multi-valued: {21, -3} -> 21, same level, same list
    <154, -55, 5, 2>,
    // N = 285
    <285, -8835, 589, 2>,
    <285, -2451, -3, 2>,
    <285, -2280, 6, 2>,
    <285, -1380, -5, 2>,
    <285, -1155, -11, 2>,
    <285, -960, -6, 2>,       // multi-valued: {10, -6} -> -6
    <285, -915, 61, 1>,       // orbit 2 sits at 27 digits, below the gate
    <285, -660, -11, 2>,
    <285, -456, -2, 2>,
    <285, -420, -5, 2>,
    <285, -219, -3, 2>,
    <285, -171, -3, 2>,       // multi-valued: {57, -3} -> -3
    <285, -155, -31, 2>,
    <285, -84, -3, 2>,
    // N = 286
    <286, -8008, 14, 1>,      // orbit 2 sits at 34 digits, below the gate
    <286, -3432, 22, 1>,      // orbit 2 sits at 20 digits, below the gate
    <286, -1768, -26, 2>,
    <286, -1716, 3, 2>,
    <286, -792, -6, 2>,       // multi-valued: {33, -6} -> -6
    <286, -660, 3, 2>,
    <286, -568, 2, 2>,
    <286, -468, 3, 1>,        // multi-valued: {3, -39} -> 3; orbit 2 below the gate
    <286, -352, -2, 2>,       // multi-valued: {11, -2} -> -2  (see header: canonical
                              //   evaluator wrongly reports Q here)
    <286, -308, -7, 2>,
    <286, -264, -2, 2>,
    <286, -260, -1, 2>,
    <286, -220, -11, 2>,
    <286, -208, -1, 2>,
    <286, -156, -3, 2>,
    <286, -120, 2, 2>,
    <286, -68, -1, 2>,
    <286, -55, 5, 2>,
    <286, -39, 13, 2>         // the fast-port divergence case; the curve says 13
];

function LevelsOf(rows)
    return Sort(Setseq({r[1] : r in rows}));
end function;

// Shared judgement over one row's usable orbit evaluations.
// obs: list of <orbit_id, K, digits>.  Returns a reason string ("" if all checks pass).
function JudgeRow(N, d, expected_tag, obs, flds)
    reasons := [];
    for o in obs do
        K := o[2];
        if FieldDegree(K) ne 2 then
            Append(~reasons, Sprintf("orbit %o has degree %o, expected 2", o[1], FieldDegree(K)));
            continue;
        end if;
        if FieldTag(K) ne expected_tag then
            Append(~reasons, Sprintf("orbit %o observed tag %o, expected %o",
                o[1], FieldTag(K), expected_tag));
        end if;
        // the comparison this test exists for: the observed field must be one of the
        // predicted candidates.  The prediction is genuinely multi-valued, so
        // membership, not equality with a single field, is the right check.
        if not exists{F : F in flds | SameField(K, F)} then
            Append(~reasons, Sprintf("orbit %o observed tag %o is NOT among the predicted %o",
                o[1], FieldTag(K), [FieldTag(F) : F in flds]));
        end if;
    end for;
    // Galois conjugates share Q(P), so every usable orbit must give the same field.
    for i in [2..#obs] do
        if not SameField(obs[1][2], obs[i][2]) then
            Append(~reasons, Sprintf("orbits %o and %o give different fields (tags %o, %o)",
                obs[1][1], obs[i][1], FieldTag(obs[1][2]), FieldTag(obs[i][2])));
        end if;
    end for;
    if #reasons eq 0 then return ""; end if;
    return Join(reasons, "; ");
end function;

printf "\n=== canonical models: observed field of definition vs prediction ===\n";

rc := AssociativeArray();
for N in LevelsOf(CANON_ROWS) do
    error if IsHyperellipticX0Nstar(N),
        Sprintf("N=%o is hyperelliptic and must not be in CANON_ROWS, EvaluateAtCM "
                * "would return a P^1 x-coordinate, not a point on the curve", N);
    X, fs := StarModelWithForms(N, EVAL_PREC);
    ell_pts, disc_ell_pts := EllipticDiscsByOrder(N);
    for row in [r : r in CANON_ROWS | r[1] eq N] do
        d := row[2]; expected_tag := row[3]; expected_n := row[4];
        flds, rc := FieldsOfDefinitionOfCMPoint(N, d : rc_cache := rc);

        _, _, evs := CertifiedConjugateEvaluations(d, N, fs, ell_pts, disc_ell_pts,
                                                   PREC_LO, PREC_HI);
        obs    := [* *];
        reason := "";
        for i in Sort(Setseq(Keys(evs))) do
            digits := DigitsOf(evs[i][3], PREC_HI);
            if digits lt GATE_DIGITS then continue; end if;
            ok, K, why := ObservedField(evs[i][2], digits);
            if not ok then
                reason cat:= Sprintf("orbit %o: %o; ", i, why);
                continue;
            end if;
            Append(~obs, <i, K, digits>);
        end for;

        AssertEqual(~results, #obs, expected_n,
            Sprintf("N=%o, d=%o: %o orbit(s) recognized at >= %o digits%o",
                N, d, expected_n, GATE_DIGITS,
                reason eq "" select "" else Sprintf(" [%o]", reason)));

        if #obs eq 0 then continue; end if;
        why := JudgeRow(N, d, expected_tag, obs, flds);
        AssertEqual(~results, why, "",
            Sprintf("N=%o, d=%o: observed Q(P) has tag %o and is among the predicted %o",
                N, d, expected_tag, [FieldTag(F) : F in flds]));
    end for;
end for;

printf "\n=== hyperelliptic models: observed field of definition vs prediction ===\n";

for N in LevelsOf(HYP_ROWS) do
    error if not IsHyperellipticX0Nstar(N),
        Sprintf("N=%o is not hyperelliptic and must not be in HYP_ROWS", N);
    X, fs := StarModelWithForms(N, EVAL_PREC);
    P_poly := HyperellipticPolynomials(X);
    ell_pts, disc_ell_pts := EllipticDiscsByOrder(N);
    CC := ComplexField(PREC_HI);

    // Full- vs half-length truncations of the same series: the convergence check
    // EvaluateOrbitsWithConvergence performs on the canonical path, done here for the
    // hyperelliptic evaluator (which CertifiedConjugateEvaluations does not call).
    len_hi  := Minimum([AbsolutePrecision(f) : f in fs]);
    fs_full := [ChangePrecision(f, len_hi) : f in fs];
    fs_half := [ChangePrecision(f, Ceiling(len_hi/2)) : f in fs];

    for row in [r : r in HYP_ROWS | r[1] eq N] do
        d := row[2]; expected_tag := row[3]; expected_n := row[4];
        flds, rc := FieldsOfDefinitionOfCMPoint(N, d : rc_cache := rc);

        ell_order := EllOrder(d, ell_pts, disc_ell_pts);
        taus      := CMTauReps(d, N, CC);
        obs       := [* *];
        reason    := "";
        for oi in [1..#taus] do
            ev_f := EvaluateAtCM_hyperelliptic(fs_full, taus[oi], CC :
                        ell_order := ell_order, P_poly := P_poly);
            ev_h := EvaluateAtCM_hyperelliptic(fs_half, taus[oi], CC :
                        ell_order := ell_order, P_poly := P_poly);
            // #ev = 3 is the WPS-infinity branch, which is not an affine (x, y) point.
            if #ev_f ne 2 or #ev_h ne 2 then continue; end if;

            gap := Maximum([Abs(ev_f[1] - ev_h[1]) / Maximum(Abs(ev_f[1]), 1),
                            Abs(ev_f[2] - ev_h[2]) / Maximum(Abs(ev_f[2]), 1)]);
            digits := DigitsOf(gap, PREC_HI);
            if digits lt GATE_DIGITS then continue; end if;

            // Independent on-curve check, available only on this path: a point that
            // fails y^2 = P(x) is not a point of X, whatever its coordinates recognize
            // to.  Held to half the trustworthy digits, the same scale the recognition
            // truncations use.
            resid := Abs(ev_f[2]^2 - Evaluate(P_poly, ev_f[1])) / Maximum(Abs(ev_f[2]^2), 1);
            if resid ge 10^(-Floor(0.5*digits)) then
                reason cat:= Sprintf("orbit %o: y^2-P(x) residual %o exceeds 10^-%o; ",
                    oi, resid, Floor(0.5*digits));
                continue;
            end if;

            ok, K, why := ObservedField(ev_f, digits);
            if not ok then
                reason cat:= Sprintf("orbit %o: %o; ", oi, why);
                continue;
            end if;
            Append(~obs, <oi, K, digits>);
        end for;

        AssertEqual(~results, #obs, expected_n,
            Sprintf("N=%o, d=%o: %o orbit(s) on-curve and recognized at >= %o digits%o",
                N, d, expected_n, GATE_DIGITS,
                reason eq "" select "" else Sprintf(" [%o]", reason)));

        if #obs eq 0 then continue; end if;
        why := JudgeRow(N, d, expected_tag, obs, flds);
        AssertEqual(~results, why, "",
            Sprintf("N=%o, d=%o: observed Q(P) has tag %o and is among the predicted %o",
                N, d, expected_tag, [FieldTag(F) : F in flds]));
    end for;
end for;

// Guard the table itself: these two contrasts are the sharpest evidence that the
// observed field tracks the level and the discriminant, not just the candidate list,
// and a careless edit to the tables above would quietly remove them.
printf "\n=== the multi-valued contrasts are still in the table ===\n";

AssertEqual(~results,
    exists{r : r in CANON_ROWS | r[1] eq 109 and r[2] eq -100 and r[3] eq 5} and
    exists{r : r in CANON_ROWS | r[1] eq 137 and r[2] eq -100 and r[3] eq -5},
    true,
    "d=-100 resolves to Q(sqrt 5) at N=109 but Q(sqrt -5) at N=137 (same candidate list)");

AssertEqual(~results,
    exists{r : r in HYP_ROWS | r[1] eq 154 and r[2] eq -252 and r[3] eq -3} and
    exists{r : r in HYP_ROWS | r[1] eq 154 and r[2] eq -63 and r[3] eq 21},
    true,
    "at N=154 the list {21,-3} resolves to -3 for d=-252 but 21 for d=-63");

AssertEqual(~results,
    exists{r : r in HYP_ROWS | r[1] eq 286 and r[2] eq -39 and r[3] eq 13},
    true,
    "N=286, d=-39 (the fast-port divergence case) is covered and observed as Q(sqrt 13)");

Report(~results, "test_cm_field_observed");
