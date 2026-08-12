// src/classify_covers.m
//
// The complete classification of the degree-3 covers X_0(N)* -> E for
// squarefree N, obtained by sweeping over every newform that could give one.
// scripts/classify_triple_covers.m formats the output;
// tests/test_triple_cover_table.m pins it against the table in the paper.
//
// Entry point:  ClassifyTripleCovers()
//
// Not loadable standalone: load "src/AtkinLehner.m" instead.  Depends on
// src/star_degree.m and src/star_quotients.m.

// A branch bound: only levels with CoverPsiHalf(M) <= CoverBranchBound(M) can
// admit a degree-3 cover at all, which is what makes the sweep below finite.
// The bound holds for any degree-3 cover, whatever newform underlies it.
function CoverBranchBound(M)
    p := 2;
    while M mod p eq 0 do p := NextPrime(p); end while;
    return 12*(3*(p+1)^2 - 1)/(p - 1);
end function;

CoverPsiHalf := func<M | &*[Rationals() | (q+1)/2 : q in PrimeDivisors(M)]>;

// The 667 squarefree levels that satisfy their own branch bound.
function TripleCoverCandidateLevels()
    GROWTH := 588;  // >= every branch bound; valid for the growth loop because a
                    // candidate's initial segments (primes added in increasing
                    // order) have CoverPsiHalf no larger than the candidate's
    prs := [p : p in [2..1200] | IsPrime(p) and (p+1)/2 le GROWTH];
    cands := {@ 1 @};
    repeat
        grew := false;
        for M in cands do
            for p in prs do
                if M mod p eq 0 or p lt Max(PrimeDivisors(M) cat [1]) then continue; end if;
                if CoverPsiHalf(M*p) le GROWTH then
                    if not M*p in cands then Include(~cands, M*p); grew := true; end if;
                end if;
            end for;
        end for;
    until not grew;
    cands := {@ M : M in cands | CoverPsiHalf(M) le CoverBranchBound(M) @};
    return Sort([M : M in cands | M ge 11]);
end function;

// Necessary conditions on delta_f in {1,3} from cheap exact data only, so the
// modular-symbols computation of C is skipped for nearly every class.  |C|
// divides #E(Q)[2] and is 1, 2 or 4; delta_f = |C| * ModularDegree / 2^omega.
// The obstruction lemma gives C = 0 outright when E(Q)[2] = 0, which is the
// common case.  Neither condition can discard a genuine cover: both are
// necessary for delta_f in {1,3}.
function StarDegreeIsPlausible(E)
    om := #PrimeDivisors(Conductor(E));
    md := ModularDegree(E);
    T  := TorsionSubgroup(E);
    n2 := #[t : t in T | 2*t eq T ! 0];
    for n in [1, 2, 4] do
        if IsDivisibleBy(n2, n) then
            r := n * md / 2^om;
            if Denominator(r) eq 1 and (Integers() ! r) in {1, 3} then
                return true;
            end if;
        end if;
    end for;
    return false;
end function;

// The complete classification.  Returns a sorted list of tuples
//   <g, N, d, target label, E_f label, |C|, delta_f, factors>
// where factors is the list of <l, l + 1 + a_l(f)> for l | N/d, and
// g = GenusStarQuotient(N) >= 2.
// verbose := true prints sweep progress.
function ClassifyTripleCovers(: verbose := false)
    delta_cache  := AssociativeArray();   // Cremona label -> delta_f (0 = ruled out)
    target_cache := AssociativeArray();   // Cremona label -> target label
    ncl_cache    := AssociativeArray();   // Cremona label -> |C|
    class_cache  := AssociativeArray();   // d -> totally-+1 optimal curves

    levels := TripleCoverCandidateLevels();
    if verbose then printf "== sweeping %o candidate levels ==\n", #levels; end if;

    rows := [];
    nseen := 0;
    for N in levels do
        nseen +:= 1;
        if verbose and nseen mod 50 eq 0 then
            printf "  ... %o/%o levels, %o covers so far\n", nseen, #levels, #rows;
        end if;
        for d in Divisors(N) do
            if d lt 11 then continue; end if;
            if not IsDefined(class_cache, d) then
                class_cache[d] := TotallyPlusOptimalCurves(d);
            end if;
            for E in class_cache[d] do
                lab := CremonaReference(E);
                if not IsDefined(delta_cache, lab) then
                    if not StarDegreeIsPlausible(E) then
                        delta_cache[lab] := 0;
                    else
                        ncl_cache[lab]    := ALTranslations(E);
                        delta_cache[lab]  := StarDegree(E);
                        target_cache[lab] := CremonaReference(StarTargetCurve(E));
                    end if;
                end if;
                delta := delta_cache[lab];
                if delta notin {1, 3} then continue; end if;
                factors := [<l, l + 1 + TraceOfFrobenius(E, l)> : l in PrimeDivisors(N div d)];
                F := &*[Integers() | t[2] : t in factors];
                if delta * F ne 3 then continue; end if;
                g := GenusStarQuotient(N);
                if g lt 2 then continue; end if;
                // delta_f = 1 means X_0(d)* is the target curve, so d is a
                // genus-1 star level; delta_f = 3 means it is not.  Independent
                // cross-check of delta_f against a quantity computed a
                // completely different way.
                gd := GenusStarQuotient(d);
                error if (delta eq 1) ne (gd eq 1),
                    Sprintf("delta_f = %o at d = %o but g(X_0(%o)*) = %o", delta, d, d, gd);
                Append(~rows, <g, N, d, target_cache[lab], lab, ncl_cache[lab], delta, factors>);
            end for;
        end for;
    end for;

    Sort(~rows, func<a, b | a[1] ne b[1] select a[1] - b[1]
                            else (a[2] ne b[2] select a[2] - b[2] else a[3] - b[3])>);
    return rows;
end function;
