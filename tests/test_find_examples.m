// tests/test_find_examples.m
// Regression tests for LabelAndAnalyze (src/labelling.m) and EvaluateAtCM (src/cm_numerics.m).
// Run with: tests/run.sh test_find_examples
// All tests run regardless of failures; summary printed at the end.

load "src/AtkinLehner.m";
load "tests/assertions.m";

results := NewResults();

// CONFIRM_DEG2: when false, LabelAndAnalyze skips the slow FieldsOfDefinitionOfCMPoint /
// AlgebraicDeg2Matches confirmatory step. Planes are still found (same counts), but the
// degree-2 components are not algebraically labelled, so deg2_matched is always false and
// the recovered-disc assertions don't apply. Set false to keep the suite under ~10 min;
// set true to also exercise the algebraic matching.
//
// COVERAGE GAP, deliberate but worth knowing: because this is false, the 13
// assertions guarded by `if CONFIRM_DEG2 then` below never run. That is every
// matched/unmatched discriminant-set expectation for N=310, N=329 and N=137,
// so a regression in AlgebraicDeg2Matches at those three levels would not be
// caught here. tests/test_311_jmap.m is the only suite that exercises the
// confirm_deg2 path, and tests/test_exceptional_tables.m passes
// confirm_deg2 := true for the genus-3 and genus-4 collinearity tables.
// Flip this to true to close the gap, at the cost of the runtime noted above.
CONFIRM_DEG2 := false;

// =========================================================================
// N = 310
// =========================================================================
printf "\n=== LabelAndAnalyze regression test for N=310 ===\n";

N310 := 310;
X310, fs310 := XZeroNstarWithForms(N310, 3000);
AssertEqual(~results, Genus(X310), 3,
    Sprintf("N=310: genus = 3  (got %o)", Genus(X310)));
rats310 := PointSearch(X310, 1000);
cm310 := RationalCMDiscs(N310);

exc310, planes310, all_matched310, fail310 := LabelAndAnalyze(N310, X310, fs310, rats310, Keys(cm310) : confirm_deg2 := CONFIRM_DEG2);
AssertEqual(~results, fail310, "",
    Sprintf("N=310: LabelAndAnalyze succeeded  (fail_reason: %o)", fail310));

AssertEqual(~results, exc310, [1],
    Sprintf("N=310: exceptional_idxs = [1]  (got %o)", exc310));
AssertEqual(~results, #planes310, 7,
    Sprintf("N=310: 7 planes found  (got %o)", #planes310));
AssertEqual(~results, all_matched310, true,
    "N=310: all_matched = true");

if #planes310 gt 0 then
    AssertEqual(~results, &and[p[3] eq [1, 1, 2] : p in planes310], true,
        "N=310: all planes have comp_degs [1,1,2]");

    if CONFIRM_DEG2 then
    AssertEqual(~results, #{i : i in [1..#planes310] | planes310[i][5]}, 2,
        Sprintf("N=310: exactly 2 planes have deg2_matched = true  (got %o)",
        #{i : i in [1..#planes310] | planes310[i][5]}));

    // matched planes: D=-55 (with cusp) and D=-840,-15
    matched_planes310 := [p : p in planes310 | p[5]];
    if #matched_planes310 gt 0 then
        all_matched_discs := &join[p[4] : p in matched_planes310];
        AssertEqual(~results, -55 in all_matched_discs and 0 in all_matched_discs and
            -840 in all_matched_discs and -15 in all_matched_discs, true,
            Sprintf("N=310: matched planes contain {-55, cusp, -840, -15}  (got %o)",
            all_matched_discs));
    else
        AssertEqual(~results, false, true,
            "N=310: matched planes contain expected discs  (no matched planes)");
    end if;

    // unmatched planes each contain exactly one disc
    unmatched_planes310  := [p : p in planes310 | not p[5]];
    unmatched_disc_sets  := [p[4] : p in unmatched_planes310];
    AssertEqual(~results, &and[#s eq 1 : s in unmatched_disc_sets], true,
        Sprintf("N=310: unmatched planes each contain exactly one CM disc  (sizes: %o)",
        [#s : s in unmatched_disc_sets]));
    if #unmatched_disc_sets gt 0 then
        unmatched_discs := &join unmatched_disc_sets;
        AssertEqual(~results, unmatched_discs, {Integers()| -60, -24, -120, -520, -340},
            Sprintf("N=310: unmatched discs = {-60,-24,-120,-520,-340}  (got %o)",
            unmatched_discs));
    else
        AssertEqual(~results, false, true,
            "N=310: unmatched planes contain expected discs  (no unmatched planes)");
    end if;
    end if;  // CONFIRM_DEG2
else
    printf "  (skipping plane structure checks: planes310 is empty)\n";
    for msg in ["N=310: all planes have comp_degs [1,1,2]",
                "N=310: exactly 2 planes have deg2_matched = true",
                "N=310: matched planes contain expected discs",
                "N=310: unmatched planes contain expected discs"] do
        AssertEqual(~results, false, true, msg);
    end for;
end if;

// =========================================================================
// N = 329  (7*47)
// =========================================================================
printf "\n=== LabelAndAnalyze regression test for N=329 (7*47) ===\n";

N329 := 7*47;
rats329, X329, fs329 := point_search_X0Nstar(N329, 1000);
cm329 := RationalCMDiscs(N329);

exc329, planes329, all_matched329, fail329 := LabelAndAnalyze(N329, X329, fs329, rats329, Keys(cm329) : confirm_deg2 := CONFIRM_DEG2);
AssertEqual(~results, fail329, "",
    Sprintf("N=329: LabelAndAnalyze succeeded  (fail_reason: %o)", fail329));

AssertEqual(~results, exc329, [1],
    Sprintf("N=329: exceptional_idxs = [1]  (got %o)", exc329));
AssertEqual(~results, #planes329, 4,
    Sprintf("N=329: 4 planes found  (got %o)", #planes329));
AssertEqual(~results, all_matched329, true,
    "N=329: all_matched = true");

if #planes329 gt 0 then
    AssertEqual(~results, &and[p[3] eq [1, 1, 2] : p in planes329], true,
        "N=329: all planes have comp_degs [1,1,2]");

    if CONFIRM_DEG2 then
    AssertEqual(~results, #{i : i in [1..#planes329] | planes329[i][5]}, 1,
        Sprintf("N=329: exactly 1 plane has deg2_matched = true  (got %o)",
        #{i : i in [1..#planes329] | planes329[i][5]}));

    // The matched plane contains D=-52 and D=-35 but not D=-763 or D=-595
    // (those were false positives: isomorphic field but CM point off the component).
    matched_planes329 := [p : p in planes329 | p[5]];
    if #matched_planes329 gt 0 then
        all_matched_discs329 := &join[p[4] : p in matched_planes329];
        AssertEqual(~results, -52 in all_matched_discs329 and -35 in all_matched_discs329 and
            -763 notin all_matched_discs329 and -595 notin all_matched_discs329, true,
            Sprintf("N=329: matched plane has {-52,-35}, not {-763,-595}  (got %o)",
            all_matched_discs329));
    else
        AssertEqual(~results, false, true,
            "N=329: matched plane contains expected discs  (no matched planes)");
    end if;

    // unmatched planes: {cusp}, {-19}, {-91}
    unmatched_planes329 := [p : p in planes329 | not p[5]];
    unmatched_disc_sets329 := [p[4] : p in unmatched_planes329];
    AssertEqual(~results, &and[#s eq 1 : s in unmatched_disc_sets329], true,
        Sprintf("N=329: unmatched planes each contain exactly one CM disc  (sizes: %o)",
        [#s : s in unmatched_disc_sets329]));
    if #unmatched_disc_sets329 gt 0 then
        unmatched_discs329 := &join unmatched_disc_sets329;
        AssertEqual(~results, unmatched_discs329, {Integers()| 0, -19, -91},
            Sprintf("N=329: unmatched discs = {cusp,-19,-91}  (got %o)",
            unmatched_discs329));
    else
        AssertEqual(~results, false, true,
            "N=329: unmatched planes contain expected discs  (no unmatched planes)");
    end if;
    end if;  // CONFIRM_DEG2
else
    printf "  (skipping plane structure checks: planes329 is empty)\n";
    for msg in ["N=329: all planes have comp_degs [1,1,2]",
                "N=329: exactly 1 plane has deg2_matched = true",
                "N=329: matched plane contains expected discs",
                "N=329: unmatched planes contain expected discs"] do
        AssertEqual(~results, false, true, msg);
    end for;
end if;

// =========================================================================
// N = 137
// =========================================================================
printf "\n=== LabelAndAnalyze regression test for N=137 ===\n";

N137 := 137;
rats137, X137, fs137 := point_search_X0Nstar(N137, 5000 : eval_prec := 3000);
AssertEqual(~results, Genus(X137), 4,
    Sprintf("N=137: genus = 4  (got %o)", Genus(X137)));

// CM identification: verify RationalCMDiscs returns the paper's discriminants
// (from Table 10 of Castano-Bernard). If this fails, CM identification is broken.
cm137 := RationalCMDiscs(N137);
AssertEqual(~results, -4 in Keys(cm137) and -7 in Keys(cm137) and
    -8 in Keys(cm137) and -11 in Keys(cm137), true,
    Sprintf("N=137: RationalCMDiscs includes D=-4,-7,-8,-11  (got %o)",
    Sort([d : d in Keys(cm137)])));

exc137, planes137, all_matched137, fail137 := LabelAndAnalyze(N137, X137, fs137, rats137, Keys(cm137) : confirm_deg2 := CONFIRM_DEG2);
AssertEqual(~results, fail137, "",
    Sprintf("N=137: LabelAndAnalyze succeeded  (fail_reason: %o)", fail137));

AssertEqual(~results, #exc137, 1,
    Sprintf("N=137: exactly 1 exceptional point  (got %o)", #exc137));
AssertEqual(~results, all_matched137, true,
    "N=137: all_matched = true");

// There must exist a deg2-matched plane whose disc_set contains the expected
// discriminants from 311example.txt.  We do not assert plane ordering,
// equation, or comp_degs; these depend on the choice of basis.
// (Algebraic match only, skipped when CONFIRM_DEG2 is false; see N=311 for the
// confirmatory-match regression at a lowered class-number bound.)
if CONFIRM_DEG2 then
AssertEqual(~results, exists{p : p in planes137 | p[5] and
    0   in p[4] and   // cusp (sentinel 0)
    -4  in p[4] and   // D=-4
    -11 in p[4] and   // D=-11
    -32 in p[4]}, true,
    // D=-32 conjugate pair (Q(sqrt(-2)) points)
    Sprintf("N=137: exists deg2-matched plane with discs {cusp,-4,-11,-32}  (plane disc sets: %o)",
    [p[4] : p in planes137 | p[5]]));
end if;

// =========================================================================
// N = 311
// =========================================================================
printf "\n=== LabelAndAnalyze regression test for N=311 ===\n";

N311 := 311;
rats311, X311, fs311 := point_search_X0Nstar(N311, 2000 : eval_prec := 3000);
AssertEqual(~results, Genus(X311), 4,
    Sprintf("N=311: genus = 4  (got %o)", Genus(X311)));

// CM identification: from 311example.txt, rational CM points are D=-11,-19,-43
cm311 := RationalCMDiscs(N311);
AssertEqual(~results, -11 in Keys(cm311) and -19 in Keys(cm311) and -43 in Keys(cm311), true,
    Sprintf("N=311: RationalCMDiscs includes D=-11,-19,-43  (got %o)",
    Sort([d : d in Keys(cm311)])));

// N=311 is the confirmatory-match regression: run with confirm_deg2 := true so
// AlgebraicDeg2Matches is exercised, but cap max_class_num := 2 so the slow
// FieldsOfDefinitionOfCMPoint step only builds class-number-<=2 ring class fields.
// The expected matched discs (-19 h=1, -123 h=2, -232 h=2) are all within that bound.
exc311, planes311, all_matched311, fail311 := LabelAndAnalyze(N311, X311, fs311, rats311, Keys(cm311) : confirm_deg2 := true, max_class_num := 2);
AssertEqual(~results, fail311, "",
    Sprintf("N=311: LabelAndAnalyze succeeded  (fail_reason: %o)", fail311));

AssertEqual(~results, #exc311, 1,
    Sprintf("N=311: exactly 1 exceptional point  (got %o)", #exc311));
AssertEqual(~results, all_matched311, true,
    Sprintf("N=311: all_matched = true  (planes found: %o)", #planes311));

// From 311example.txt: the plane -w+x+y+2z=0 contains exc, D=-19, and
// conjugate pairs D=-123 and D=-232.
AssertEqual(~results, exists{p : p in planes311 | p[5] and
    -19  in p[4] and   // D=-19 rational CM point
    -123 in p[4] and   // D=-123 conjugate pair
    -232 in p[4]}, true,
    // D=-232 conjugate pair
    Sprintf("N=311: exists deg2-matched plane with discs {-19,-123,-232}  (plane disc sets: %o)",
    [p[4] : p in planes311 | p[5]]));

// =========================================================================
// N = 399  (3*7*19)
// All 8 rational CM discriminants match at eval_prec=7000.
// =========================================================================
printf "\n=== MatchRationalCMPoints regression test for N=399 (3*7*19) ===\n";

N399 := 3*7*19;
rats399, X399, fs399 := point_search_X0Nstar(N399, 1000 : eval_prec := 7000);
AssertEqual(~results, Genus(X399), 4,
    Sprintf("N=399: genus = 4  (got %o)", Genus(X399)));

// Verify RationalCMDiscs returns all 8 expected rational CM discriminants.
cm399 := RationalCMDiscs(N399);
AssertEqual(~results, -3 in Keys(cm399) and -12 in Keys(cm399) and
    -27 in Keys(cm399) and -48 in Keys(cm399) and
    -75 in Keys(cm399) and -147 in Keys(cm399) and
    -483 in Keys(cm399) and -1995 in Keys(cm399), true,
    Sprintf("N=399: RationalCMDiscs includes D=-3,-12,-27,-48,-75,-147,-483,-1995  (got %o)",
    Sort([d : d in Keys(cm399)])));

// Direct CM matching. D=-3 is an order-3 elliptic point (all cusp forms vanish
// to order 2, so EvaluateAtCM uses n^2-weighting) and D=-12 is related to
// Q(sqrt(-3)); both are the awkward cases here, and both match.
CC399 := ComplexField(200);
rats_cc399 := [[CC399!c : c in Eltseq(r)] : r in rats399];
ell_pts399 := NumberOfEllipticPointsByCMOrder(N399);
disc_ell_pts399 := {};
for ell in [2,3,4,6] do disc_ell_pts399 join:= Keys(ell_pts399[ell]); end for;
matched399, nfail399, dmap399 :=
    MatchRationalCMPoints(N399, fs399, rats_cc399, rats399, CC399, 10^-15, Keys(cm399), ell_pts399, disc_ell_pts399);
AssertEqual(~results, nfail399, 0,
    Sprintf("N=399: MatchRationalCMPoints nfail = 0  (got %o, unmatched: %o)",
    nfail399,
    Sort([d : d in Keys(cm399) | d notin Keys(dmap399)])));
AssertEqual(~results, -3 in Keys(dmap399), true,
    Sprintf("N=399: D=-3 CM point matched  (matched discs: %o)",
    Sort([d : d in Keys(dmap399)])));
AssertEqual(~results, -12 in Keys(dmap399), true,
    Sprintf("N=399: D=-12 CM point matched  (matched discs: %o)",
    Sort([d : d in Keys(dmap399)])));

// =========================================================================
// retry_precision_failures integration test for N=399
// =========================================================================
// Covers analyze_exceptional / retry_precision_failures, a documented
// quickstart entry point.
//
// The three assertions below cover D=-3 via the eval_prec retry
// path. D=-3 at N=399 is an order-6 elliptic point,
// so EvaluateAtCM (src/cm_numerics.m) evaluates it with n^5-weighting. At
// eval_prec=3000 the weighted value is under-converged (max coordinate error
// 6.9e-11 against the 10^-15 match tolerance used by MatchRationalCMPoints),
// but the *classical* residual MatchRationalCMPoints inspects to detect
// "returned zero" (src/labelling.m:1115) is 5.2e-16, just under that same
// 10^-15 gate, so the zero-detector never fires. Instead of falling
// through to the old "evaluation ok but point not found in PointSearch
// results" message (src/labelling.m:1145), the classifier now re-evaluates
// the same point with a half-length series and compares it against the
// full-length result; when the two disagree (as they do here) it reports
// "D=-3: evaluation not converged at this eval_prec (half-length series
// disagrees; needs higher eval_prec)" instead. retry_precision_failures
// (src/point_search.m:204-214) filters on exactly that "needs higher
// eval_prec" substring, so this D=-3 failure is now caught and retried, and
// the retry succeeds at eval_prec=7000, where the same point matches rats[2]
// to error 9.6e-33 (see the N=399 MatchRationalCMPoints section above, which
// runs at eval_prec=7000 directly and passes). See
// .superpowers/sdd/release_plan_steps1-5/task-4-investigation.md for the
// original trace of the under-convergence issue this retry path fixes. The
// hyperelliptic labeller has the same shape of hazard at
// src/labelling.m:305 ("affine eval ok but no rat matched"), whose message
// does not contain "needs higher eval_prec", so that particular failure
// mode is still never retried.
printf "\n=== retry_precision_failures integration test for N=399 ===\n";
// Build interesting with eval_prec=3000 so N=399 fails in LabelAndAnalyze.
// Note: the snapshot hand-assembled a 6-element tuple
// <N399_retry, 0, rats399_low, X399_low, fs399_low, Sstar399> here. That
// predates the cm_pts field analyze_exceptional now reads at entry[7]
// (src/point_search.m:216), so the snapshot's literal tuple no longer matches
// the current API (a straight port crashes with a runtime index-range error).
// Rebuilt via check_exceptional_example (src/point_search.m:139), the documented
// quickstart entry point, which produces the current
// <N, n, rats, X, fs, Sstar, cm_pts> shape and gives that entry point its
// first automated coverage.
N399_retry := 399;
interesting_low := check_exceptional_example(N399_retry : eval_prec := 3000);
// max_class_num := 2 bounds Degree2Points(399), which is otherwise
// unbounded and does not terminate in practice (disc -14763 alone costs
// 831 s, -3192 exceeded 1277 s). Same bound and same reason as the N=311
// call earlier in this file. The three assertions below concern the
// eval_prec retry path, not degree-2 field computation, so the bound does
// not weaken what they assert.
results_low := analyze_exceptional(interesting_low : max_class_num := 2);
AssertEqual(~results, results_low[1][5] ne "" and "needs higher eval_prec" in results_low[1][5], true,
    Sprintf("N=399: expected eval_prec failure at prec=3000, got: '%o'", results_low[1][5]));

// Retry at higher precision.
results_retried := retry_precision_failures(results_low, interesting_low : new_eval_prec := 7000, max_class_num := 2);
AssertEqual(~results, results_retried[1][5], "",
    Sprintf("N=399: expected retry to succeed at prec=7000, got fail_reason: '%o'", results_retried[1][5]));
AssertEqual(~results, results_retried[1][4], true,
    // all_matched
    "N=399: expected all_matched=true after retry at prec=7000");

// =========================================================================
// EvaluateAtCM: derivative weighting for D=-4
// =========================================================================
printf "\n=== Unit test: EvaluateAtCM derivative weighting for D=-4 ===\n";
// At an order-2 elliptic point (D=-4), all weight-2 cusp forms vanish.
// Plain q-expansion gives 0/0 noise; n-weighted evaluation (the 1st-derivative
// trick) gives well-defined projective coordinates.
// This test uses the N=137 default basis (fs137), known to fail without the fix
// because all four form values are O(10^-58) at the D=-4 CM tau.
// After the fix, MatchRationalCMPoints must find D=-4 with nfail=0.
CC_ep := ComplexField(200);
rats_cc137_ep := [[CC_ep!c : c in Eltseq(r)] : r in rats137];
ell_pts137 := NumberOfEllipticPointsByCMOrder(137);
disc_ell_pts137 := {};
for ell in [2,3,4,6] do disc_ell_pts137 join:= Keys(ell_pts137[ell]); end for;
matched_ep, nfail_ep, dmap_ep := MatchRationalCMPoints(137, fs137, rats_cc137_ep, rats137, CC_ep, 10^-15, Keys(cm137), ell_pts137, disc_ell_pts137);
AssertEqual(~results, nfail_ep, 0,
    Sprintf("D=-4 (default basis): MatchRationalCMPoints nfail = 0  (got %o)", nfail_ep));
AssertEqual(~results, -4 in Keys(dmap_ep), true,
    Sprintf("D=-4 (default basis): D=-4 in matched discs  (got %o)",
    Sort([d : d in Keys(dmap_ep)])));

// =========================================================================
// N = 158  (2*79): hyperelliptic genus-2
// Tests three things introduced to fix the D=-7 WPS-infinity matching:
//
//   1. LabelAndAnalyze_hyperelliptic succeeds (fail_reason = "") including
//      the D=-7 CM point, which previously could not be matched.
//
//   2. BoostFsPrec: returns the right number of forms (normal operation).
//
//   3. retry_precision_failures: dispatches to LabelAndAnalyze_hyperelliptic
//      for genus-2 hyperelliptic N and succeeds.
// =========================================================================
printf "\n=== LabelAndAnalyze_hyperelliptic regression test for N=158 (2*79) ===\n";

N158 := 2*79;
AssertEqual(~results, IsHyperellipticX0Nstar(N158), true,
    "N=158: IsHyperellipticX0Nstar = true");
AssertEqual(~results, GenusStarQuotient(N158), 2,
    Sprintf("N=158: genus = 2  (got %o)", GenusStarQuotient(N158)));

pts158, X158, fs158, Sstar158 := point_search_X0Nstar(N158, 3000 : eval_prec := 3000);
cm158, _ := RationalCMDiscs(N158);

AssertEqual(~results, #pts158, 8,
    Sprintf("N=158: PointSearch found 8 points  (got %o)", #pts158));
AssertEqual(~results, -7 in Keys(cm158), true,
    Sprintf("N=158: RationalCMDiscs includes D=-7  (got %o)", Sort([d : d in Keys(cm158)])));

exc158, planes158, all_matched158, fail158 :=
    LabelAndAnalyze_hyperelliptic(N158, X158, fs158, pts158, Keys(cm158));
AssertEqual(~results, fail158, "",
    Sprintf("N=158: LabelAndAnalyze_hyperelliptic succeeded  (fail_reason: %o)", fail158));
AssertEqual(~results, #exc158, 1,
    Sprintf("N=158: exactly 1 exceptional point  (got %o)", #exc158));

// BoostFsPrec: normal operation, returns the same number of forms as the genus.
printf "\n=== BoostFsPrec test for N=158 ===\n";

boosted158 := BoostFsPrec(Sstar158, 2000);
AssertEqual(~results, #boosted158, 2,
    Sprintf("N=158: BoostFsPrec(Sstar, 2000) returns 2 forms  (got %o)", #boosted158));

// retry_precision_failures: hyperelliptic dispatch.
// Build a synthetic results/interesting pair whose fail_reason triggers retry.
// The retry must call LabelAndAnalyze_hyperelliptic (not LabelAndAnalyze) and succeed.
printf "\n=== retry_precision_failures hyperelliptic dispatch for N=158 ===\n";

fake_interesting158 := [* <N158, 1, pts158, X158, fs158, Sstar158, cm158> *];
fake_results158 := [*
    <N158, [], [* *], false,
     "D=-7: g(q)~0 at CM point and WPS infinity match failed (needs higher eval_prec)">
*];
retry158 := retry_precision_failures(fake_results158, fake_interesting158 : new_eval_prec := 3000);
AssertEqual(~results, retry158[1][5], "",
    Sprintf("N=158: retry_precision_failures (hyperelliptic) succeeds  (fail_reason: %o)",
    retry158[1][5]));
AssertEqual(~results, #retry158[1][2], 1,
    Sprintf("N=158: retry returns 1 exceptional index  (got %o)", #retry158[1][2]));

// =========================================================================
// N = 106  (2*53): hyperelliptic genus-2 with rational elliptic CM point
//
// 53 ≡ 1 (mod 4) gives an order-4 elliptic point on X_0(106)* with CM disc D=-4.
// Without the elliptic-point fix, LabelAndAnalyze_hyperelliptic would fail for
// D=-4: both f and g vanish at the CM tau, the code incorrectly falls into
// WPSInfinityMatch (which checks g≈0 but f≠0), and returns a false failure.
// =========================================================================
printf "\n=== LabelAndAnalyze_hyperelliptic elliptic-CM test for N=106 (2*53) ===\n";

N106 := 2*53;
AssertEqual(~results, IsHyperellipticX0Nstar(N106), true,
    "N=106: IsHyperellipticX0Nstar = true");
AssertEqual(~results, GenusStarQuotient(N106), 2,
    Sprintf("N=106: genus = 2  (got %o)", GenusStarQuotient(N106)));

// D=-4 must be an elliptic disc for N=106 (53 ≡ 1 mod 4 gives order-4 elliptic points).
ell_pts106 := NumberOfEllipticPointsByCMOrder(N106);
disc_ell_pts106 := {};
for ell in [2,3,4,6] do disc_ell_pts106 join:= Keys(ell_pts106[ell]); end for;
AssertEqual(~results, -4 in disc_ell_pts106, true,
    Sprintf("N=106: D=-4 is in disc_ell_pts  (got %o)", disc_ell_pts106));

pts106, X106, fs106, Sstar106 := point_search_X0Nstar(N106, 3000 : eval_prec := 3000);
cm106, _ := RationalCMDiscs(N106);

AssertEqual(~results, -4 in Keys(cm106), true,
    Sprintf("N=106: RationalCMDiscs includes D=-4  (got %o)", Sort([d : d in Keys(cm106)])));

exc106, planes106, all_matched106, fail106 :=
    LabelAndAnalyze_hyperelliptic(N106, X106, fs106, pts106, Keys(cm106));
AssertEqual(~results, fail106, "",
    Sprintf("N=106: LabelAndAnalyze_hyperelliptic succeeded  (fail_reason: %o)", fail106));

// =========================================================================
// N = 107: hyperelliptic genus-2 with WPS-infinity CM point
//
// At least one rational CM disc on X_0*(107) has g(q)=0 at its CM tau,
// so the model map sends it to a point at WPS infinity.  Before the fix,
// EvaluateAtCM_hyperelliptic returned garbage [huge_x, garbage_y] instead
// of detecting the infinity case, causing LabelAndAnalyze_hyperelliptic to
// fail with "affine eval ok but no rat matched".
// =========================================================================
printf "\n=== LabelAndAnalyze_hyperelliptic regression test for N=107 ===\n";

N107 := 107;
AssertEqual(~results, IsHyperellipticX0Nstar(N107), true,
    "N=107: IsHyperellipticX0Nstar = true");
AssertEqual(~results, GenusStarQuotient(N107), 2,
    Sprintf("N=107: genus = 2  (got %o)", GenusStarQuotient(N107)));

pts107, X107, fs107, Sstar107 := point_search_X0Nstar(N107, 3000 : eval_prec := 3000);
cm107, _ := RationalCMDiscs(N107);

exc107, planes107, all_matched107, fail107 :=
    LabelAndAnalyze_hyperelliptic(N107, X107, fs107, pts107, Keys(cm107));
AssertEqual(~results, fail107, "",
    Sprintf("N=107: LabelAndAnalyze_hyperelliptic succeeded  (fail_reason: %o)", fail107));

// =========================================================================
// N = 103: hyperelliptic involution partner of a CM point
//
// rats[7] = (3:-19:1) is exceptional after CM+cusp matching; it is the
// hyperelliptic involution of rats[8] (disc=-3, elliptic order 3).
// HyperellipticInvolutionSearch should detect this and set all_matched=true.
// =========================================================================
printf "\n=== LabelAndAnalyze_hyperelliptic involution test for N=103 ===\n";

N103 := 103;
pts103, X103, fs103, Sstar103 := point_search_X0Nstar(N103, 3000 : eval_prec := 3000);
cm103, _ := RationalCMDiscs(N103);

exc103, pairs103, all_matched103, fail103 :=
    LabelAndAnalyze_hyperelliptic(N103, X103, fs103, pts103, Keys(cm103));
AssertEqual(~results, fail103, "",
    Sprintf("N=103: LabelAndAnalyze_hyperelliptic succeeded  (fail_reason: %o)", fail103));
AssertEqual(~results, all_matched103, true,
    "N=103: all_matched = true (involution partner detected)");
AssertEqual(~results, exc103, [7],
    Sprintf("N=103: exceptional_idxs = [7]  (got %o)", exc103));
AssertEqual(~results, #pairs103, 1,
    Sprintf("N=103: 1 involution pair found  (got %o)", #pairs103));
if #pairs103 ge 1 then
    AssertEqual(~results, pairs103[1][1], 7,
        Sprintf("N=103: involution pair exc_idx = 7  (got %o)", pairs103[1][1]));
    AssertEqual(~results, -3 in pairs103[1][4], true,
        Sprintf("N=103: involution partner has disc -3  (got %o)", pairs103[1][4]));
end if;

// =========================================================================
// N = 209: one hyperelliptic involution pair
//
// disc=-88 -> rats[4]=(0:2:1) and disc=-19 -> rats[3]=(0:-2:1): the order-2
// elliptic evaluation resolves these to their two distinct points (previously
// both discs collapsed onto (0:2:1), leaving (0:-2:1) spuriously exceptional).
// disc=-627 -> rats[6]=(-1:19:2); its hyperelliptic involution rats[5]=(-1:-19:2)
// has no CM disc of its own and is found by HyperellipticInvolutionSearch.
// So exactly 1 exceptional point (rats[5]) and 1 CM-backed involution pair.
// =========================================================================
printf "\n=== LabelAndAnalyze_hyperelliptic involution test for N=209 (11*19) ===\n";

N209 := 11*19;
pts209, X209, fs209, Sstar209 := point_search_X0Nstar(N209, 3000 : eval_prec := 3000);
cm209, _ := RationalCMDiscs(N209);

exc209, pairs209, all_matched209, fail209 :=
    LabelAndAnalyze_hyperelliptic(N209, X209, fs209, pts209, Keys(cm209));
AssertEqual(~results, fail209, "",
    Sprintf("N=209: LabelAndAnalyze_hyperelliptic succeeded  (fail_reason: %o)", fail209));
AssertEqual(~results, all_matched209, true,
    "N=209: all_matched = true (involution partner detected)");
AssertEqual(~results, #exc209, 1,
    Sprintf("N=209: 1 exceptional_idx  (got %o)", #exc209));
AssertEqual(~results, #pairs209, 1,
    Sprintf("N=209: 1 involution pair found  (got %o)", #pairs209));

// =========================================================================
// N = 129: exceptional-exceptional involution pair does not count as explained
//
// rats[13]=(7:-383:12) and rats[14]=(7:383:12) are each other's hyperelliptic
// involution.  Both are exceptional (no CM disc), so they must not satisfy
// all_matched.  The other two exceptional points are involution partners of
// CM points (discs -51 and -3), so those two are covered.
// (The order-2/order-6 elliptic evaluation now matches disc=-12 directly to its
// own point rather than leaving its involution partner exceptional, so there are
// 4 exceptional points and 2 CM-backed pairs, previously 5 and 3.)
// =========================================================================
printf "\n=== LabelAndAnalyze_hyperelliptic exc-exc pair test for N=129 ===\n";

N129 := 129;
pts129, X129, fs129, Sstar129 := point_search_X0Nstar(N129, 3000 : eval_prec := 3000);
cm129, _ := RationalCMDiscs(N129);

exc129, pairs129, all_matched129, fail129 :=
    LabelAndAnalyze_hyperelliptic(N129, X129, fs129, pts129, Keys(cm129));
AssertEqual(~results, fail129, "",
    Sprintf("N=129: LabelAndAnalyze_hyperelliptic succeeded  (fail_reason: %o)", fail129));
AssertEqual(~results, not all_matched129, true,
    "N=129: all_matched = false (exc-exc pair does not count as explained)");
AssertEqual(~results, #exc129, 4,
    Sprintf("N=129: 4 exceptional_idxs  (got %o)", #exc129));
AssertEqual(~results, #pairs129, 2,
    Sprintf("N=129: 2 involution pairs found (CM-backed only)  (got %o)", #pairs129));

// =========================================================================
// N = 330: order-2 elliptic CM at D=-120, with D=-24 and D=-1320 as controls
//
// There are deliberately NO numeric assertions about f(tau) at D=-120 here,
// because at this precision none of them would carry information.
//
// Im(tau) = sqrt(120)/(2*330) ≈ 0.0166, so |q| ≈ 0.9010, and a 3000-term
// q-expansion has truncation error bounded by n*|q|^n/(1-|q|) ≈ 1e-131.
// Nothing smaller than that is resolved at all.  Against tol = 10^-10 the
// measured values are
//
//     |f(tau)|  = 2.1e-134     |gf(tau)| = 8.0e-135     |Dgf(tau)| = 2.4e-131
//
// all of which sit at that truncation floor and are consistent with
// f(tau) = 0 and f'(tau) = 0 exactly, correctly resolved.  The numerics work.
// Any "< tol" assertion on D=-120 would therefore be asserting noise: it
// would pass today and change the moment eval_prec moves.
//
// D=-24 (|f| = 2.9e-59) and D=-1320 (|f| = 0.0) have larger Im(tau) and do
// converge, which is why they are asserted as controls below.  D=-120's
// 2.1e-134 is truncation, not convergence -- a "< tol" test cannot tell those
// two apart, so folding D=-120 in with the controls would enshrine the noise
// floor as expected behaviour.
//
// The coverage of D=-120 that does hold is end-to-end: the
// LabelAndAnalyze_hyperelliptic assertions at the foot of this block exercise
// it, and they pass.
// =========================================================================
printf "\n=== Order-2 elliptic CM regression tests for N=330 ===\n";

pts330e, C330e, fs330e, Sstar330e := point_search_X0Nstar(330, 3000 : eval_prec := 3000);
cm330e, _ := RationalCMDiscs(330);
CC330e    := ComplexField(200);
tol330e   := 10^-10;  // same tolerance as LabelAndAnalyze_hyperelliptic

AssertEqual(~results, -24 in Keys(cm330e) and -120 in Keys(cm330e) and -1320 in Keys(cm330e), true,
    Sprintf("N=330: RationalCMDiscs includes D=-24,-120,-1320  (got %o)",
    Sort([d : d in Keys(cm330e)])));

// ---- Controls: D=-24 and D=-1320 zero check passes (Im(tau) large enough) ----
for disc_ctrl330 in [-24, -1320] do
    taus_ctrl330 := TauFromForms(HeegnerForms(330, disc_ctrl330), CC330e);
    tau_ctrl330  := taus_ctrl330[1];
    q_ctrl330    := Exp(2*Pi(CC330e)*CC330e.1*tau_ctrl330);
    fv_ctrl330   := Evaluate(fs330e[1], q_ctrl330);
    gfv_ctrl330  := Evaluate(fs330e[2], q_ctrl330);
    AssertEqual(~results, Abs(fv_ctrl330) lt tol330e and Abs(gfv_ctrl330) lt tol330e, true,
        Sprintf("N=330 D=%o: zero check passes (control) |f|=%o |gf|=%o",
        disc_ctrl330, Abs(fv_ctrl330), Abs(gfv_ctrl330)));
end for;

// ---- Integration: full LabelAndAnalyze_hyperelliptic for N=330 ----
// This is the coverage D=-120 does have: it exercises the whole path
// end-to-end, without depending on any numeric assertion about f(tau).
exc330e, pairs330e, allm330e, fail330e :=
    LabelAndAnalyze_hyperelliptic(330, C330e, fs330e, pts330e, Keys(cm330e));
AssertEqual(~results, fail330e, "",
    Sprintf("N=330: LabelAndAnalyze_hyperelliptic succeeded  (fail: %o)", fail330e));

// =========================================================================
// N = 93: order-2 elliptic D=-12 (failing before fix)
// =========================================================================
printf "\n=== Order-2 elliptic CM regression test for N=93 (D=-12) ===\n";

pts93e, C93e, fs93e, Sstar93e := point_search_X0Nstar(93, 3000 : eval_prec := 3000);
cm93e, _ := RationalCMDiscs(93);
AssertEqual(~results, -12 in Keys(cm93e), true,
    Sprintf("N=93: RationalCMDiscs includes D=-12  (got %o)", Sort([d : d in Keys(cm93e)])));
exc93e, pairs93e, allm93e, fail93e :=
    LabelAndAnalyze_hyperelliptic(93, C93e, fs93e, pts93e, Keys(cm93e));
AssertEqual(~results, fail93e, "",
    Sprintf("N=93: LabelAndAnalyze_hyperelliptic succeeded  (fail: %o)", fail93e));

// =========================================================================
// N = 161  (7*23): order-2 elliptic D=-7 (failing before fix)
// =========================================================================
printf "\n=== Order-2 elliptic CM regression test for N=161 (D=-7) ===\n";

pts161e, C161e, fs161e, Sstar161e := point_search_X0Nstar(7*23, 3000 : eval_prec := 3000);
cm161e, _ := RationalCMDiscs(7*23);
AssertEqual(~results, -7 in Keys(cm161e), true,
    Sprintf("N=161: RationalCMDiscs includes D=-7  (got %o)", Sort([d : d in Keys(cm161e)])));
exc161e, pairs161e, allm161e, fail161e :=
    LabelAndAnalyze_hyperelliptic(7*23, C161e, fs161e, pts161e, Keys(cm161e));
AssertEqual(~results, fail161e, "",
    Sprintf("N=161: LabelAndAnalyze_hyperelliptic succeeded  (fail: %o)", fail161e));

// =========================================================================
// N = 166  (2*83): order-2 elliptic D=-8 (failing before fix)
// =========================================================================
printf "\n=== Order-2 elliptic CM regression test for N=166 (D=-8) ===\n";

pts166e, C166e, fs166e, Sstar166e := point_search_X0Nstar(2*83, 3000 : eval_prec := 3000);
cm166e, _ := RationalCMDiscs(2*83);
AssertEqual(~results, -8 in Keys(cm166e), true,
    Sprintf("N=166: RationalCMDiscs includes D=-8  (got %o)", Sort([d : d in Keys(cm166e)])));
exc166e, pairs166e, allm166e, fail166e :=
    LabelAndAnalyze_hyperelliptic(2*83, C166e, fs166e, pts166e, Keys(cm166e));
AssertEqual(~results, fail166e, "",
    Sprintf("N=166: LabelAndAnalyze_hyperelliptic succeeded  (fail: %o)", fail166e));

// =========================================================================
// N = 165  (3*5*11): order-2 elliptic D=-11 (failing before fix)
// =========================================================================
printf "\n=== Order-2 elliptic CM regression test for N=165 (D=-11) ===\n";

pts165e, C165e, fs165e, Sstar165e := point_search_X0Nstar(3*5*11, 3000 : eval_prec := 3000);
cm165e, _ := RationalCMDiscs(3*5*11);
AssertEqual(~results, -11 in Keys(cm165e), true,
    Sprintf("N=165: RationalCMDiscs includes D=-11  (got %o)", Sort([d : d in Keys(cm165e)])));
exc165e, pairs165e, allm165e, fail165e :=
    LabelAndAnalyze_hyperelliptic(3*5*11, C165e, fs165e, pts165e, Keys(cm165e));
AssertEqual(~results, fail165e, "",
    Sprintf("N=165: LabelAndAnalyze_hyperelliptic succeeded  (fail: %o)", fail165e));

// =========================================================================
// Cusp identification on hyperelliptic genus-2 X_0(N)*  (N = 230, 285, 330)
//
// Regression for the cusp-at-infinity bug: LabelAndAnalyze_hyperelliptic used to
// hard-code the cusp at WPS point (1:-1:0), which assumes the echelon star basis
// has leading coefficient 1.  all_diag_basis actually returns forms with leading
// coefficient 2, so x = f_1/f_2 -> infinity with WPS y-coordinate
//   Y/X^3 = lim_{q->0} Wron(f_1,f_2)/f_1^3 = -c_2/c_1^2 = -2/4 = -1/2,
// i.e. the cusp is (1:-1/2:0), not (1:-1:0).  Before the fix the cusp was never
// matched and got silently absorbed as the "hyperelliptic involution" of the CM
// point at the opposite infinity point (1:1/2:0).
// =========================================================================
printf "\n=== Cusp identification regression test (N=230, 285, 330) ===\n";

for Ncusp in [230, 285, 330] do
    AssertEqual(~results, IsHyperellipticX0Nstar(Ncusp) and GenusStarQuotient(Ncusp) eq 2, true,
        Sprintf("N=%o: hyperelliptic genus 2", Ncusp));

    ptsCu, Ccu, fsCu, _ := point_search_X0Nstar(Ncusp, 2000 : eval_prec := 3000);
    cmCu, _ := RationalCMDiscs(Ncusp);

    // Independent computation of the cusp's WPS y-coordinate from the forms.
    c1cu := Coefficient(fsCu[1], 1); c2cu := Coefficient(fsCu[2], 2);
    cusp_ycu := -c2cu / c1cu^2;
    AssertEqual(~results, cusp_ycu, -1/2,
        Sprintf("N=%o: cusp WPS-y = -c2/c1^2 = %o (expected -1/2)", Ncusp, cusp_ycu));

    // The cusp is the infinity point (1:-1/2:0); its hyperelliptic conjugate
    // (1:1/2:0) is a genuine CM point (e.g. D=-40 for N=230, D=-51 for N=285).
    cusp_idxcu := 0;
    for i in [1..#ptsCu] do
        s := Eltseq(ptsCu[i]);
        if s[3] eq 0 and s[1] ne 0 and s[2]/s[1]^3 eq cusp_ycu then cusp_idxcu := i; break; end if;
    end for;
    AssertEqual(~results, cusp_idxcu gt 0 and Eltseq(ptsCu[cusp_idxcu]) eq [Rationals() | 1, -1/2, 0], true,
        Sprintf("N=%o: cusp is the infinity point (1:-1/2:0)  (idx %o)", Ncusp, cusp_idxcu));

    excCu, pairsCu, allmCu, failCu :=
        LabelAndAnalyze_hyperelliptic(Ncusp, Ccu, fsCu, ptsCu, Keys(cmCu));
    AssertEqual(~results, failCu, "",
        Sprintf("N=%o: LabelAndAnalyze_hyperelliptic succeeded  (fail: %o)", Ncusp, failCu));
    AssertEqual(~results, allmCu, true,
        Sprintf("N=%o: all exceptional points explained", Ncusp));
    // The cusp must now be matched, not left exceptional / faked as an involution.
    AssertEqual(~results, cusp_idxcu notin excCu, true,
        Sprintf("N=%o: cusp (idx %o) is identified, not exceptional  (exc: %o)", Ncusp, cusp_idxcu, excCu));
end for;

// =========================================================================
// Summary
// =========================================================================
printf "\n";
Report(~results, "test_find_examples");
