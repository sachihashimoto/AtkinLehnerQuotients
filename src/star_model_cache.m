// src/star_model_cache.m
//
// Cache of the star cusp forms for a level, kept in data/starmodels/.  Almost
// all the cost of building a model of X_0(N)* is one Atkin-Lehner
// diagonalization; storing the resulting q-expansions lets a later run rebuild
// both the forms and the model cheaply.
//
// Entry point:  StarModelWithForms(N, eval_prec)
//
// Reading the cache is the default everywhere.  Writing it is not: an entry is
// created when none exists, but an existing entry is only rewritten for a
// caller that passes GrowCache := true (see StarModelWithForms below).
//
// Not loadable standalone: load "src/AtkinLehner.m" instead.  Depends on
// src/modelsX0Nstar.m, and must load before src/point_search.m.

STAR_CACHE_DIR := "data/starmodels";

function StarFormsCachePath(M)
    return STAR_CACHE_DIR cat "/starforms_" cat Sprint(M) cat ".m";
end function;

function LoadStarForms(M)
    // The eval and the destructuring sit inside the try alongside the Read: a
    // truncated or hand-edited cache file parses badly rather than failing to
    // open, and this is a cache, so every such failure should fall through to a
    // rebuild rather than abort the run. SaveStarForms guards the write side
    // the same way with its tmp-file-plus-mv, though that mv's exit status goes
    // unchecked, so a half-installed cache is reachable here.
    try
        s := Read(StarFormsCachePath(M));
        dat := eval s;
        prec := dat[1];
        R := PowerSeriesRing(Rationals());
        fs := [(R ! c) + O(R.1^prec) : c in dat[2]];
    catch e
        return false, 0, [];
    end try;
    return true, prec, fs;
end function;

procedure SaveStarForms(M, fs_series, prec)
    // stage to a temp file and move, so a partial write never clobbers a
    // good cache (and never overwrites silently)
    coeffs := [[Coefficient(f, j) : j in [0..prec - 1]] : f in fs_series];
    tmp := StarFormsCachePath(M) cat ".tmp" cat Sprint(Random(10^9));  // unique per process (parallel-safe)
    Write(tmp, Sprintf("<%o, %o>", prec, coeffs) : Overwrite := true);
    System(Sprintf("mv %o %o", tmp, StarFormsCachePath(M)));
    printf "[cache] saved %o-term star forms for level %o\n", prec, M;
end procedure;

// Given the raw Sstar (either a list of CuspForms elements from XZeroNstarWithForms,
// or a ModSym subspace from XZeroNstarWithForms_hyperelliptic), return q-expansions
// at new_eval_prec terms without rerunning all_diag_basis. Also used (and
// designed to fail soft, not throw) when Sstar is actually an already-
// materialized, fixed-precision list of power series (e.g. StarModelWithForms's
// cache-hit fs_full), qExpansion on a power series isn't meaningful, so the
// catch below just reports "can't boost further" rather than erroring.
function BoostFsPrec(Sstar, new_eval_prec)
    if ISA(Type(Sstar), ModSym) then
        try
            return qExpansionBasis(Sstar, new_eval_prec);
        catch e
            printf "WARNING: BoostFsPrec (ModSym) failed at prec=%o: %o\n", new_eval_prec, e`Object;
            return [];
        end try;
    end if;
    try
        return [qExpansion(f, new_eval_prec) : f in Sstar];
    catch e
        printf "WARNING: BoostFsPrec failed at prec=%o: %o\n", new_eval_prec, e`Object;
        return [];
    end try;
end function;

// Hyperelliptic variant: re-applies the echelon transformation so the returned
// fs matches the basis used by XZeroNstarWithForms_hyperelliptic.
function BoostFsPrec_hyperelliptic(Sstar, new_eval_prec)
    try
        fs_raw := [qExpansion(f, new_eval_prec) : f in Sstar];
        M := Matrix([AbsEltseq(fs_raw[j] : FixedLength) : j in [1..#fs_raw]]);
        _, T := EchelonForm(M);
        return [&+[T[i][j]*fs_raw[j] : j in [1..#fs_raw]] : i in [1..#fs_raw]];
    catch e
        printf "WARNING: BoostFsPrec_hyperelliptic failed at prec=%o: %o\n", new_eval_prec, e`Object;
        return [];
    end try;
end function;

// Certify equations (homogeneous, possibly mixed degree) against fixed
// cached forms fs_full, unlike CertifyCanonicalEquations, there's no live
// Sstar to ask for more precision from, so this only ever compares against
// what's already cached, and errors out (rather than looping forever) if
// that isn't enough.
function CertifyEquationsAgainstCache(equations, fs_full, Np)
    weights := [];
    for e in equations do
        assert IsHomogeneous(e);
        Append(~weights, 2 * Degree(e));
    end for;
    B_max := Max([ModularSturmBound(Np, w) : w in weights]);
    maxprec := Minimum([AbsolutePrecision(f) : f in fs_full]);
    error if maxprec le B_max,
        Sprintf("CanonicalModelFromForms: cached forms have too few terms to certify, need precision > %o (Sturm bound for weight %o on Gamma_0(%o)), got %o",
                B_max, Max(weights), Np, maxprec);
    for e in equations do
        val := Evaluate(e, fs_full);
        ok, _ := CertifyModularIdentity(val, Np, 2*Degree(e));
        if not ok then
            return false;
        end if;
    end for;
    return true;
end function;

// canonical model from cached forms (same relations logic as the builders)
function CanonicalModelFromForms(fs_full, Np)
    g := #fs_full;
    Rq := Parent(fs_full[1]);
    maxprec := Minimum([AbsolutePrecision(f) : f in fs_full]);
    number_of_terms := 20;
    repeat
        number_of_terms +:= 10;
        error if number_of_terms ge maxprec, "CanonicalModelFromForms: cached forms have too few terms";
        bas := [f + O(Rq.1^number_of_terms) : f in fs_full];
        Pg1<[z]> := PolynomialRing(Rationals(), g);
        if g eq 3 then
            d := 4;
        elif g eq 4 or g eq 5 then
            d := 3;
        else
            d := 2;
        end if;
        relsOfDeg := function(deg)
            monsd := MonomialsOfDegree(Pg1, deg);
            mat := Matrix([[Coefficient(m, j) : j in [2..number_of_terms]]
                            where m := Evaluate(mm, bas) : mm in monsd]);
            kermat := KernelMatrix(mat);
            return [&+[kermat[i,j]*monsd[j] : j in [1..#monsd]] : i in [1..Nrows(kermat)]];
        end function;
        equations := relsOfDeg(d);
        X0_N_Scheme := Scheme(ProjectiveSpace(Pg1), equations);
        if (g ge 6) and (Dimension(X0_N_Scheme) ne 1) then
            equations cat:= relsOfDeg(3);
            X0_N_Scheme := Scheme(ProjectiveSpace(Pg1), equations);
        end if;
        if Dimension(X0_N_Scheme) ne 1 then continue; end if;
        candidate := Curve(X0_N_Scheme);
        if Genus(candidate) ne g then continue; end if;
        // Dimension/genus agreeing with expectation is evidence, not proof.
        // Certify past the Sturm bound before accepting (see modelsX0Nstar.m).
        if not CertifyEquationsAgainstCache(equations, fs_full, Np) then continue; end if;
        X0_N := candidate;
    until assigned X0_N;
    return X0_N;
end function;

// hyperelliptic model from cached (echelonized) forms; mirrors
// XZeroNstarWithForms_hyperelliptic, including its cleared-denominator Sturm
// certification of the resulting identity.
function HyperellipticModelFromForms(fs_full, Np)
    g := #fs_full;
    fg1c := fs_full[g - 1];
    fgc  := fs_full[g];
    Rc := Parent(fg1c);
    qc := Rc.1;

    deg    := 2*g + 2;
    weight := 4*g + 4;
    B_hyp  := ModularSturmBound(Np, weight);
    maxprec := Minimum([AbsolutePrecision(f) : f in fs_full]);
    error if maxprec le B_hyp,
        Sprintf("HyperellipticModelFromForms: cached forms have too few terms to certify, need precision > %o (Sturm bound for weight %o on Gamma_0(%o)), got %o",
                B_hyp, weight, Np, maxprec);

    t := Minimum(Floor(Index(Gamma0(Np)) * g / 6), maxprec - 3);

    Dfg1c := qc * Derivative(fg1c);
    Dfgc  := qc * Derivative(fgc);
    Wc := Dfg1c * fgc - fg1c * Dfgc;

    L<ql> := LaurentSeriesRing(Rationals());
    fg1L := L ! fg1c;
    fgL  := L ! fgc;
    xq  := fg1L / fgL;
    y2q := (L ! Wc)^2 / fgL^6;

    mat   := Matrix([[Coefficient(xq^k, j) : j in [0..t]] : k in [0..deg]]);
    y2vec := Vector([Coefficient(y2q,   j) : j in [0..t]]);
    P_coeffs := Solution(mat, y2vec);

    LHS := Wc^2 * fgc^(2*g - 4);
    RHS := &+[P_coeffs[k+1] * fg1c^k * fgc^(deg-k) : k in [0..deg]];
    ok, _ := CertifyModularIdentity(LHS - RHS, Np, weight);
    error if not ok, "HyperellipticModelFromForms: cleared identity failed Sturm certification";

    Px<x> := PolynomialRing(Rationals());
    return HyperellipticCurve(Px ! Eltseq(P_coeffs));
end function;

// Unified model builder with caching.  Returns X, fs (eval_prec terms),
// fs_full (cache-precision series, used downstream in place of Sstar), and the
// live form basis if this call built one -- empty on a cache hit, where the
// forms came off disk as series and no live basis was ever constructed.
//
// That fourth return exists because only a live basis can be asked for more
// q-expansion terms (BoostFsPrec); frozen series have the terms they have.  A
// cache hit therefore has nothing better to offer, but a miss does: it built
// the basis on the way through, and callers that may need more precision later
// would otherwise have to rebuild the level to get back what this call already
// had.  Callers content with fixed-precision series keep taking three returns.
//
// Requires GenusStarQuotient(Np) ge 2, caller is responsible for the genus <= 1
// special case (X0Nstar(Np) directly).
//
// GrowCache controls the write side when an entry already exists but holds
// fewer terms than cp.  Creating an absent entry is always safe, but rewriting
// an existing one at a different precision is not: data/starmodels/ is
// committed, so it turns an ordinary search into a diff in a tracked file, and
// (see the README's "Regenerating the cache") it silently invalidates every
// map_<Np>_*.m built against the old forms, since those record polynomial
// exponents but not the coordinate system they were built in.  So by default a
// too-short entry is rebuilt in memory and left alone on disk; callers that
// genuinely want the file grown to cp -- BuildTripleCover, which is the thing
// that owns those map_*.m files -- ask for it.
function StarModelWithForms(Np, eval_prec : cache_prec := 3000, GrowCache := false)
    hyp := IsHyperellipticX0Nstar(Np);
    cp := Max(eval_prec, cache_prec);
    ok, prec, fs_full := LoadStarForms(Np);
    if ok and prec ge cp then
        printf "[cache] loaded %o-term star forms for level %o\n", prec, Np;
        X := hyp select HyperellipticModelFromForms(fs_full, Np)
                 else CanonicalModelFromForms(fs_full, Np);
        fs := [f + O(Parent(f).1^eval_prec) : f in fs_full];
        return X, fs, fs_full, [];   // no live basis: nothing was built here
    end if;
    if hyp then
        X, fs, Sstar := XZeroNstarWithForms_hyperelliptic(Np, eval_prec);
        full := BoostFsPrec_hyperelliptic(Sstar, cp);
    else
        X, fs, Sstar := XZeroNstarWithForms(Np, eval_prec);
        full := BoostFsPrec(Sstar, cp);
    end if;
    if #full gt 0 then
        // ok here means LoadStarForms returned usable forms that were merely too
        // short; a missing or unparseable file leaves it false and is (re)written.
        if not ok or GrowCache then
            SaveStarForms(Np, full, cp);
        else
            printf "[cache] level %o has a %o-term entry, need %o: rebuilt in memory, on-disk entry left as is (pass GrowCache := true to rewrite it)\n",
                Np, prec, cp;
        end if;
    else
        full := fs;
    end if;
    return X, fs, full, Sstar;
end function;
