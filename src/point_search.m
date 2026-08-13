// src/point_search.m
//
// Search a model of X_0(N)* for rational points and work out which of them are
// exceptional: that is, neither a cusp, nor an elliptic point, nor a known
// CM point.
//
// Entry points:  check_exceptional_example(N)     search one level and report
//                check_exceptional_X0Nstar(g)     sweep every level of genus g
//                analyze_exceptional(result)      explain the points found
//                point_search_X0Nstar(N, B)       rational points up to height B
//                count_special_points_X0Nstar(N)     CM points plus cusp,
//                    straight from class-number data, with no search or model
//
// The search functions build the model from the data/starmodels/ cache when a
// usable entry is there (UseCache, on by default), which saves the
// Atkin-Lehner diagonalization that is almost all the cost of a level.  They
// never rewrite an existing entry: see StarModelWithForms in
// src/star_model_cache.m.
//
// A cache hit costs one thing.  The Sstar it returns is a materialized
// fixed-precision series list rather than a live form basis, so BoostFsPrec
// cannot ask it for more q-expansion terms; retry_precision_failures below
// handles that by rebuilding the level fresh, so it is a slower retry rather
// than a lost one.  A cache miss costs nothing: the build produced a live
// basis and that is what comes back, exactly as with UseCache := false.
// Pass UseCache := false to force a fresh build outright --
// what scripts/gen_genus_models.m does, since a cached rebuild reproduces the
// same curve through a different choice of ideal generators and that script
// diffs its output against committed files.
//
// Depends on star_quotients.m, fields_of_definition.m, cm_numerics.m and
// labeling.m, so it loads last in src/AtkinLehner.m.


function PointsOriginalModel(C, B)
    Qx<x> := PolynomialRing(Rationals());

    f := HyperellipticPolynomials(C);
    den := LCM([ Denominator(c) : c in Coefficients(f) ]);

    s := den;
    fint := s^2 * f;
    Cint := HyperellipticCurve(fint);

    pts_int := Points(Cint : Bound := B);

    Q := Rationals();
    s_rat := Q!s;

    pts_orig := [];
    for P in pts_int do
        coords := Eltseq(P);
        // HyperellipticCurve Eltseq always returns [X, Y, Z] in WPS(1,g+1,1).
        // Cint has y^2 = s^2*f(x), so Y_{int} = s*Y_orig. Undo the scaling: Y -> Y/s.
        // Force rational arithmetic to avoid integer-division failure when s does not
        // divide coords[2] exactly as a RngIntElt.
        Y_orig := Q!coords[2] / s_rat;
        if #coords eq 2 then
            Append(~pts_orig, C![Q!coords[1], Y_orig]);
        else
            Append(~pts_orig, C![Q!coords[1], Y_orig, Q!coords[3]]);
        end if;
    end for;

    return pts_orig;
end function;

// Nonsingular: forwarded to PointSearch on the canonical (non-hyperelliptic)
// branch only. PointSearch's default preprocessing runs a singularity check
// that is a Groebner computation over the ambient variety. cCeap for the
// low-degree, low-genus models this pipeline was first used on, but it
// measurably dominates runtime at genus 8 (330s at N=293, B=1000, vs whatever
// the bounded search itself costs) and hangs outright at some higher-omega
// genus-8 levels (scripts/pointsearch_g8.m's header: "unbounded at the
// omega=4 levels"). 
function point_search_X0Nstar(N, B : eval_prec := 3000, UseCache := true)
    if IsHyperellipticX0Nstar(N) then
        g := GenusStarQuotient(N);
        if g le 1 then
            X := X0Nstar(N);
            X := SimplifiedModel(X);
            return [], X, [], [];
        end if;
        // Build model from cusp forms so CM evaluation is consistent for all genus >= 2.
        if UseCache then
            // Prefer the live basis when the cache missed and one was built:
            // it is the only form of Sstar BoostFsPrec can extend later.
            C, fs, full, live := StarModelWithForms(N, eval_prec);
            Sstar := #live gt 0 select live else full;
        else
            C, fs, Sstar := XZeroNstarWithForms_hyperelliptic(N, eval_prec);
        end if;
        pts := PointsOriginalModel(C, B);
        return pts, C, fs, Sstar;
    else
        if UseCache then
            X, fs, full, live := StarModelWithForms(N, eval_prec);
            Sstar := #live gt 0 select live else full;
        else
            X, fs, Sstar := XZeroNstarWithForms(N, eval_prec);
        end if;
        pts := PointSearch(X, B : Nonsingular := true);
        return pts, X, fs, Sstar;
    end if;
end function;

// BoostFsPrec / BoostFsPrec_hyperelliptic moved to src/star_model_cache.m
// (loaded earlier in src/AtkinLehner.m) since StarModelWithForms there needs
// them too; still in scope here via the shared load chain.

function count_special_points_X0Nstar(N)
  // count CM points and cusp on X0(N)*, but only rational ones
    assert IsSquarefree(Integers()!N);
    cm_pts := RationalCMDiscs(N);
    special := 0;
    for disc in Keys(cm_pts) do
        special +:= cm_pts[disc];
    end for;
    special +:= 1; // add 1 for the cusp, which is also a special rational point
    return special, cm_pts;
end function;


function exceptional_pts_X0Nstar(N, B : eval_prec := 3000, UseCache := true)
    pts, X, fs, Sstar := point_search_X0Nstar(N, B : eval_prec := eval_prec, UseCache := UseCache);
    if Genus(X) le 1 then return false, [], X, fs, Sstar, AssociativeArray(); end if;
    // Note: count_special_points_X0Nstar calls RationalCMDiscs dynamically and
    // works for any squarefree N, but the discriminant search bound grows with
    // omega(N) so could be slow for N with many prime factors.
    special_pts, cm_pts := count_special_points_X0Nstar(N);
    exc := #pts - special_pts;
    print "Actual points:", pts;
    print "Special points:", special_pts;
    if exc lt 0 then
        print "ERROR: negative pts";
    end if;
    return exc, pts, X, fs, Sstar, cm_pts;
end function;


function check_exceptional_example(N :B := 1000, eval_prec := 3000, UseCache := true)
    interesting := [* *];
    n, rats, X, fs, Sstar, cm_pts := exceptional_pts_X0Nstar(N, B : eval_prec := eval_prec, UseCache := UseCache);
    Append(~interesting, <N, n, rats, X, fs, Sstar, cm_pts>);
    return interesting;
end function;

function check_exceptional_X0Nstar(g : B := 1000, eval_prec := 3000, skip := {}, UseCache := true)
  interesting := [* *];
  // Note: RationalCMDiscs assumes N is squarefree; skip non-squarefree N.
  for entry in StarQuotientsOfGenusExactly(g) do
    N := entry[1];
    if entry[2] le 1 then continue; end if;
    if N in skip then continue; end if;
    if not IsSquarefree(N) then continue; end if;
    print "--------------------------------";
    print Factorization(N);
    print "Genus:", entry[2];
    n, rats, X, fs, Sstar, cm_pts := exceptional_pts_X0Nstar(N, B : eval_prec := eval_prec, UseCache := UseCache);
    if Type(n) eq BoolElt then
      continue;
    end if;
    if n gt 0 then
      printf "Found %o exceptional points on level %o\n", n, PrimeFactors(N);
      Append(~interesting, <N, n, rats, X, fs, Sstar, cm_pts>);
    end if;
  end for;
  return interesting;
end function;

// Result entries: <N, exceptional_idxs, planes, all_matched, fail_reason>
// fail_reason: "" on success, or a string describing the first CM disc that blocked analysis.
// confirm_deg2: passed through to LabelAndAnalyze; set false to skip the slow field-of-definition
//   build and the confirmatory AlgebraicDeg2Matches check.
// One rc_cache (FieldsOfDefinitionOfCMPoint's disc-keyed ring-class-field cache) is shared across
// every N in this loop's non-hyperelliptic branch, so a discriminant that is degree-2 at more than
// one level in `interesting` (they are drawn from the same fixed CMClassListsDeg2 disc pool) has
// its ring class field built at most once for the whole call, not once per level.
// LabelAndAnalyze_hyperelliptic never touches Degree2Points / FieldsOfDefinitionOfCMPoint, so the
// hyperelliptic branch has no cache to thread.
function analyze_exceptional(interesting : max_class_num := 0, confirm_deg2 := true)
  results := [* *];
  rc_cache := AssociativeArray();
  for entry in interesting do
    N := entry[1]; rats := entry[3]; X := entry[4]; fs := entry[5]; cm_pts := entry[7];
    if IsHyperellipticX0Nstar(N) then
      g := GenusStarQuotient(N);
      printf "\n=== LabelAndAnalyze_hyperelliptic for N=%o (genus %o) ===\n", N, g;
      exc, planes, all_matched, fail_reason :=
          LabelAndAnalyze_hyperelliptic(N, X, fs, rats, Keys(cm_pts));
      Append(~results, <N, exc, planes, all_matched, fail_reason>);
      continue;
    end if;
    printf "\n=== LabelAndAnalyze for N=%o ===\n", N;
    exc, planes, all_matched, fail_reason, _, rc_cache := LabelAndAnalyze(N, X, fs, rats, Keys(cm_pts) : max_class_num := max_class_num, confirm_deg2 := confirm_deg2, rc_cache := rc_cache);
    Append(~results, <N, exc, planes, all_matched, fail_reason>);
  end for;
  return results;
end function;

// Retry entries in results that failed with "needs higher eval_prec".
// interesting must be the list passed to analyze_exceptional (same index order).
// Uses stored Sstar to recompute fs at new_eval_prec without rerunning all_diag_basis
// or any CM discriminant computations.
//
// When Sstar came from a cache hit it is a fixed-precision series list that
// BoostFsPrec cannot extend, so that shortcut is unavailable and the level is
// instead rebuilt from scratch at new_eval_prec (fresh, since the point of the
// retry is more terms than the cache holds).  B is the point-search bound for
// those rebuilds; entries do not record the bound they were found with, so pass
// the one the caller used if it was not the default.
// Returns an updated copy of results.
function retry_precision_failures(results, interesting : new_eval_prec := 7000, B := 1000, max_class_num := 0, confirm_deg2 := true)
    assert #results eq #interesting;  // pre-condition: both built from same ordered loop
    updated := results;
    for i in [1..#results] do
        fail_reason := results[i][5];
        if "needs higher eval_prec" notin fail_reason then continue; end if;

        entry := interesting[i];
        N      := entry[1];
        rats   := entry[3];
        X      := entry[4];
        Sstar  := entry[6];
        cm_pts := entry[7];

        assert results[i][1] eq N;  // sanity: index correspondence holds

        printf "\n=== Retrying N=%o with eval_prec=%o ===\n", N, new_eval_prec;
        if IsHyperellipticX0Nstar(N) then
            new_fs := BoostFsPrec_hyperelliptic(Sstar, new_eval_prec);
        else
            new_fs := BoostFsPrec(Sstar, new_eval_prec);
        end if;
        if #new_fs eq 0 then
            // Either Sstar is a cache hit's materialized series list (BoostFsPrec
            // fails soft on those by design) or the boost itself failed. Both are
            // recoverable the same way: rebuild the level fresh at new_eval_prec,
            // which gives a live basis at the precision wanted. Take that build's
            // X, rats and cm_pts too, so fs and the points being labelled come
            // from one construction rather than being mixed across two.
            printf "  Sstar cannot be extended to %o terms; rebuilding N=%o fresh (UseCache := false, B = %o)\n",
                new_eval_prec, N, B;
            fresh := check_exceptional_example(N : B := B, eval_prec := new_eval_prec, UseCache := false);
            rats   := fresh[1][3];
            X      := fresh[1][4];
            new_fs := fresh[1][5];
            cm_pts := fresh[1][7];
            if #new_fs eq 0 then
                printf "WARNING: fresh rebuild of N=%o at prec=%o produced no forms; skipping retry\n", N, new_eval_prec;
                continue;
            end if;
        end if;
        // Dispatch to the correct labeling function; hyperelliptic curves have WPS
        // coordinates that are incompatible with the projective matching in LabelAndAnalyze.
        if IsHyperellipticX0Nstar(N) then
            printf "  (hyperelliptic genus-%o path)\n", GenusStarQuotient(N);
            exc, planes, all_matched, new_fail := LabelAndAnalyze_hyperelliptic(N, X, new_fs, rats, Keys(cm_pts) : cc_prec := 500);
        else
            exc, planes, all_matched, new_fail := LabelAndAnalyze(N, X, new_fs, rats, Keys(cm_pts) : max_class_num := max_class_num, confirm_deg2 := confirm_deg2);
        end if;
        updated[i] := <N, exc, planes, all_matched, new_fail>;
    end for;
    return updated;
end function;
