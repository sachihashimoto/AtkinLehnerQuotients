// src/star_quotients.m
//
// Genus of X_0(N) and of its Atkin-Lehner quotients, and the search for the
// levels N whose quotient has a given genus, which is what drives the
// whole-genus sweep in point_search.m.
//
// Entry points:  GenusX0N(N)                     genus of X_0(N)
//                GenusStarQuotient(N)            genus of X_0(N)*
//                StarQuotientsOfGenusExactly(g)               levels, as <N, g>
//                SquarefreeStarQuotientsOfGenusExactly(g)     the squarefree ones
//                StarQuotientsOfGenusAtMost(g)
//
// Depends on cm_points.m (NuOgg) and cm_orders.m, and is loaded before
// modelsX0Nstar.m, which calls GenusStarQuotient.


function NumEllipticPtsD1(N, order)
    // Elliptic point counts for X0(N): order=2 gives cusps, order=3/4 give e_3/e_2
    if order eq 2 then
        return &+[EulerPhi(GCD(d, N div d)) : d in Divisors(N)];
    end if;
    Q := (order eq 3) select 9 else 4;
    if N mod Q eq 0 then return 0; end if;
    return &*[Integers() | 1 + KroneckerSymbol(-order, p) : p in PrimeDivisors(N)];
end function;

function GenusX0N(N)
    //Genus of the big curve X0(N)
    primes := PrimeDivisors(N);
    P1N := Floor(N * &*[Rationals() | 1 + 1/p : p in primes]);
    g := 1 + P1N / 12;
    for h in [2, 3, 4] do
        g -:= NumEllipticPtsD1(N, h) / h;
    end for;
    assert IsIntegral(g);
    return Floor(g);
end function;


function NumFixedPtsWm(N, m)
    // Fixed points of w_m on X0(N), D=1
    assert m ne 1;
    e := 0;
    for R in CMOrdersForAL(m) do
        h := PicardNumber(R);
        prod := &*[Integers() | NuOgg(p, R, N) : p in PrimeDivisors(N) | m mod p ne 0];
        e +:= h * prod;
    end for;
    if (m eq 4) then
        M := N div 4;
        num_fixed_cusps := &+[Integers() | EulerPhi(GCD(d, M div d)) : d in Divisors(M)];
        e +:= num_fixed_cusps;
    end if;
    return e;
end function;


function AtkinLehnerMul(w, m, N)
// multiply Atkin-Lehners w and m in X0(N)
    ps := PrimeDivisors(N);
    wvals := Vector(Integers(), [Valuation(w, p) : p in ps]);
    mvals := Vector(Integers(), [Valuation(m, p) : p in ps]);
    wmvals := Vector(Integers(), [0 : p in ps]);
    for i in [1..#ps] do
        if wvals[i] eq 0 then
            wmvals[i] := mvals[i];
        elif mvals[i] eq 0 then
            wmvals[i] := wvals[i];
        else
            wmvals[i] := 0;
        end if;
    end for;
    wm := &*[ps[i]^(wmvals[i]) : i in [1..#ps]];
    return wm;
end function;

function AllALsFromGens(Ws, N)
    // Get all ALs from a generating set
    allws := {Integers()|};
    S := Subsets(Ws);
    for s in S do
        if #s eq 0 then
            Include(~allws, 1);
        else
            prod := 1;
            for w in s do
                prod := AtkinLehnerMul(w,prod, N);
            end for;
            Include(~allws, prod);
        end if;
    end for;
    return allws;
end function;

function GenusStarQuotient(N)
    //Genus of X0(N)/<als>
    als := AllALsFromGens({pa[1]^pa[2] : pa in Factorization(N)}, N);
    total_e := 0;
    for al in als do
        assert GCD(al, N div al) eq 1;
        if (al ne 1) then
            total_e +:= NumFixedPtsWm(N, al );
        end if;
    end for;
    if #als eq 1 then
        s := 0;
    else
        is_prime_power, two, s := IsPrimePower(#als);
        assert is_prime_power and (two eq 2);
    end if;
    g_big := GenusX0N(N);
    g := 1 + (g_big - 1)/2^s - total_e/2^(s+1);
    assert IsIntegral(g);
    return Floor(g);
end function;



function PrimePowerContribution(p, a)
    /*
        Contribution of p^a to

            mu(N) / 2^omega(N),

        where

            mu(N) = N * Product_{p | N} (1 + 1/p).

        If N = Product p^a, then

            mu(N) / 2^omega(N)
              = Product_{p^a || N} p^(a-1)(p+1)/2.
    */

    assert IsPrime(p);
    assert a ge 1;

    return Rationals()!(p^(a - 1) * (p + 1)) / 2;
end function;


procedure ExtendCandidates(~cands, N, remaining, next_p)
    /*
        Recursively builds all N satisfying

            mu(N) / 2^omega(N) <= original_bound.

        Primes are added in increasing order so each N is generated once.
    */

    Append(~cands, N);

    pmax := Floor(2*remaining - 1);
    p := NextPrime(next_p - 1);

    while p le pmax do
        a := 1;

        while true do
            contrib := PrimePowerContribution(p, a);

            if contrib gt remaining then
                break;
            end if;

            ExtendCandidates(~cands, N*p^a, remaining/contrib, NextPrime(p));

            a +:= 1;
        end while;

        p := NextPrime(p);
    end while;
end procedure;


function CandidateLevelsByGonality(g)
    /*
        Certified finite superset of all N such that

            genus X_0(N)^* <= g.

        Uses the necessary condition

            mu(N) / 2^omega(N) <= 2^(15)/325 * (g + 1).

        This comes from Abramovich's bound
            gon(X_0(N)) >= (lambda_1/24) * mu(N),

        with lambda_1 >= 975/4096 (Kim-Sarnak), giving (975/4096)/24 = 325/32768,
        and if genus X_0(N)^* <= g, then

            gon(X_0(N)) <= 2^omega(N) * (g + 3).
    */

    assert g ge 0;

    bound := Rationals()!(2^15 * (g + 3)) / 325;

    cands := [];
    ExtendCandidates(~cands, 1, bound, 2);

    cands := Sort(SetToSequence(Seqset(cands)));

    return cands, bound;
end function;


function StarQuotientsOfGenusExactly(g)
    /*
        Returns exactly the levels N for which X_0(N)^* has genus g.

        The candidate set is certified by the gonality bound, and then
        filtered using the exact genus computation.

        Output:
            out = [ <N, g> : genus X_0(N)^* = g ]
    */

    assert g ge 0;

    candidates, gon_bound := CandidateLevelsByGonality(g);

    out := [];

    for N in candidates do
        gs := GenusStarQuotient(N);

        if gs eq g then
            Append(~out, <N, gs>);
        end if;
    end for;

    return Sort(out);
end function;

function SquarefreeStarQuotientsOfGenusExactly(g);
    S := StarQuotientsOfGenusExactly(g);
    Snew := [pair : pair in S | IsSquarefree(pair[1])];
    return Snew;
end function;


function StarQuotientsOfGenusAtMost(g)
    /*
        Returns exactly the levels N for which X_0(N)^* has genus <= g.

        Output:
            out = [ <N, genus X_0(N)^*> : genus X_0(N)^* <= g ]
    */

    assert g ge 0;
    candidates, gon_bound := CandidateLevelsByGonality(g);
    out := [];

    for N in candidates do
        gs := GenusStarQuotient(N);
        if gs le g then
            Append(~out, <N, gs>);
        end if;
    end for;

    return Sort(out);
end function;


function StarLevelBoundGenusAtMost(g)
    /*
        Returns the largest actual N such that genus X_0(N)^* <= g.

        If there are no such N, returns 0.
        In practice N = 1 usually appears, depending on conventions.
    */

    vals := StarQuotientsOfGenusAtMost(g);
    if #vals eq 0 then
        return 0;
    end if;

    return Maximum([x[1] : x in vals]);
end function;
