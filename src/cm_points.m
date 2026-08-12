///////////////////////////////////////////////////////////////////////////
// src/cm_points.m
//
// Exact construction of the CM points of discriminant D on X_0(N),
// N squarefree, via optimal embeddings of the order of discriminant D
// into the Eichler order O_0(N).
//
// Entry point:  CMTauReps(D, N, CC)
//
// Self-contained: depends on nothing else in the repo.  src/AtkinLehner.m
// loads this file.
//
///////////////////////////////////////////////////////////////////////////

 function PsiOgg(p, n)
    if (n eq 1) then
    return 1;
    end if;
    is_prime_power, q, k := IsPrimePower(n);
    if (is_prime_power) then
    return ((q eq p) select Floor(p^k *(1 + 1/p)) else 1);
    end if;
    fac := Factorization(n);
    return &*[Integers() | PsiOgg(p, pe[1]^pe[2]) : pe in fac];
end function;

function LegendreSymbol(R, p)
//special Legendre symbol of R at p
    f := Conductor(R);
    if (f mod p eq 0) then
        return 1;
    end if;
    ZF := MaximalOrder(R);
    return KroneckerSymbol(Discriminant(ZF),p);
end function;

function NuOgg(p, R, F)
//Local embedding number of R, where R is a CM order
    if Valuation(F, p) eq 1 then
        return 1 + LegendreSymbol(R, p);
    end if;
    assert Valuation(F, p) ge 2;
    f := Conductor(R);
    ZF := MaximalOrder(R);
    chip := KroneckerSymbol(Discriminant(ZF),p);
    k := Valuation(f, p);
    K := Valuation(F, p);
    if (K ge 2*(1 + k)) then
    if (chip eq 1) then
        return 2*PsiOgg(p, f);
    end if;
    return 0;
    end if;
    if (K eq 1 + 2*k) then
    if (chip eq 1) then
        return 2*PsiOgg(p, f);
    end if;
    if (chip eq 0) then
        return p^k;
    end if;
    assert chip eq -1;
    return 0;
    end if;
    if (K eq 2*k) then
    return p^(k-1)*(p+1+chip);
    end if;
    if (K le 2*k - 1) then
    if IsEven(K) then
        return p^(k div 2) + p^(k div 2 - 1);
    else
        return 2*p^(k div 2);
    end if;
    end if;
    // Should not reach here
    assert false;
end function;

// Quotient by w_m, m divides DN, following [Ogg]

function NumberOfOptimalEmbeddings(R, N)
    h := PicardNumber(R);
    prod := &*[Integers() | NuOgg(p, R, N) : p in PrimeDivisors(N)];
    return h*prod;
end function;


///////////////////////////////////////////////////////////////////////////
// Atkin-Lehner matrix
//
// q must be an exact divisor of N. Since this script assumes N squarefree,
// every divisor q of N is exact.
///////////////////////////////////////////////////////////////////////////

function AtkinLehnerMatrix(N, q)
    assert N mod q eq 0;

    m := N div q;
    assert GCD(q, m) eq 1;

    g, s, t := XGCD(q, m);
    assert g eq 1;

    if q eq 1 then
        return IdentityMatrix(Rationals(), 2);
    end if;

    W := Matrix(Rationals(), 2, 2, [
        q,  -t,
        N, q*s
    ]);

    assert Determinant(W) eq q;

    return W;
end function;


///////////////////////////////////////////////////////////////////////////
// Does a root modulo p lift to a root modulo p^2?
//
// For squarefree level, Voight Proposition 30.6.12 says that such a lift produces
// the extra Atkin-Lehner local embedding class when p divides D.
///////////////////////////////////////////////////////////////////////////

function RootLiftsModuloSquare(s, p, tr, nm)

    pp := p^2;

    for k in [0..p-1] do
        x := s + k*p;

        if (x^2 - tr*x + nm) mod pp eq 0 then
            return true;
        end if;
    end for;

    return false;
end function;


///////////////////////////////////////////////////////////////////////////
// Optimality test inside O_0(N)
//
// Write
//
//             M = [ a   b  ]
//                 [ N*c d  ].
//
// The embedding is nonoptimal at a prime ell precisely when
//
//             ell | b,
//             ell | c,
//             ell | a-d.
//
// Thus the global embedding is optimal iff gcd(b,c,a-d) = 1.
//
// Notice that this is not the content of the fixed-point quadratic form.
///////////////////////////////////////////////////////////////////////////

function IsOptimalEmbeddingMatrix(M, N)

    if M[2,1] mod N ne 0 then
        return false;
    end if;

    b  := M[1,2];
    c  := M[2,1] div N;
    ad := M[1,1] - M[2,2];

    return GCD(GCD(Abs(b), Abs(c)), Abs(ad)) eq 1;
end function;


///////////////////////////////////////////////////////////////////////////
// Find an oriented representative of a form class
//
// Given a primitive form f, find an equivalent primitive form
//
//                        [a,b,c]
//
// satisfying
//
//             gcd(a,N) = 1,
//             b = B0 mod 2N,
//             N | c.
//
// This supplies one of the local branches. Extra branches at primes common
// to the conductor and level are added later using Atkin-Lehner matrices.
///////////////////////////////////////////////////////////////////////////

function OrientedClassRepresentative(f, N, B0)

    G := SL(2, Integers());

    //---------------------------------------------------------------------
    // Find a representative whose first coefficient is coprime to N.
    //---------------------------------------------------------------------

    if GCD(f[1], N) eq 1 then

        f1 := f;

    elif GCD(f[3], N) eq 1 then

        S := G![
             0, -1,
             1,  0
        ];

        f1 := f*S;

    else

        found := false;
        H := 0;

        while not found do
            H +:= 1;

            for r in [-H..H] do
                for t in [-H..H] do

                    if Maximum([Abs(r), Abs(t)]) ne H then continue; end if;
                    if GCD(r,t) ne 1 then   continue;  end if;

                    a1 := f[1]*r^2 + f[2]*r*t + f[3]*t^2;

                    if GCD(a1,N) ne 1 then  continue; end if;

                    gg, u, v := XGCD(r,t);
                    assert gg eq 1;

                    // determinant = r*u + v*t = 1
                    U := G![  r, -v, t,  u ];
                    f1 := f*U;
                    found := true;
                    break;
                end for;

                if found then  break;  end if;
            end for;
        end while;

    end if;

    a1 := f1[1];
    b1 := f1[2];

    assert GCD(a1,N) eq 1;
    assert (B0-b1) mod 2 eq 0;

    // Apply [1 k; 0 1], changing b1 to b1 + 2*a1*k.
    gg, ainv, tmp := XGCD(a1,N);
    assert gg eq 1;

    k := (((B0-b1) div 2)*ainv) mod N;

    if k gt N div 2 then
        k -:= N;
    end if;

    T := G![ 1, k, 0, 1  ];

    f2 := f1*T;

    assert Discriminant(f2) eq Discriminant(f);
    assert GCD(f2[1],N) eq 1;
    assert f2[2] mod (2*N) eq B0 mod (2*N);
    assert f2[3] mod N eq 0;

    return f2;
end function;


///////////////////////////////////////////////////////////////////////////
// Integral Atkin-Lehner conjugate
///////////////////////////////////////////////////////////////////////////

function AtkinLehnerConjugate(M, N, q)

    W := AtkinLehnerMatrix(N,q);

    MQ := ChangeRing(M, Rationals());
    C  := W^(-1)*MQ*W;

    assert Denominator(C[1,1]) eq 1;
    assert Denominator(C[1,2]) eq 1;
    assert Denominator(C[2,1]) eq 1;
    assert Denominator(C[2,2]) eq 1;

    C := Matrix(Integers(), 2, 2, [
        Integers()!C[1,1], Integers()!C[1,2],
        Integers()!C[2,1], Integers()!C[2,2]
    ]);

    assert C[2,1] mod N eq 0;

    return C;
end function;


///////////////////////////////////////////////////////////////////////////
// Fixed-point form of an embedding matrix
//
// For M = [a b; c e] the fixed-point equation is c*tau^2 + (e-a)*tau - b = 0,
// giving the form [A,B,C] = [-c, a-e, b], normalised to A > 0.
//
// This form need not be primitive: when gcd(N, Conductor(R)) > 1 its content
// can exceed 1 while the embedding is still optimal (N = 399, D = -147 gives
// content 7).  Content is a Gamma_0(N)-invariant, so it is a coarse
// equivalence invariant rather than a defect.
///////////////////////////////////////////////////////////////////////////

function FixedPointForm(M)

    A := -M[2,1];
    B :=  M[1,1] - M[2,2];
    C :=  M[1,2];

    if A lt 0 then
        A := -A;
        B := -B;
        C := -C;
    end if;

    assert A gt 0;

    return [Integers() | A, B, C];
end function;


///////////////////////////////////////////////////////////////////////////
// Proper automorphisms of a binary quadratic form
//
// Parameterized by the solutions of t^2 - D*u^2 = 4:
//
//     Aut(f) = { [ (t - b u)/2 , -c u ; a u , (t + b u)/2 ] : t^2 - D u^2 = 4 }
//
// Order 2 for D < -4, order 4 for D = -4, order 6 for D = -3.  Both special
// discriminants occur in production (D = -3 at N = 399, D = -4 at N = 178),
// so the general parameterization is not optional.
///////////////////////////////////////////////////////////////////////////

function AutForm(f, D)

    a := f[1]; b := f[2]; c := f[3];

    sols := [];

    for u in [-2..2] do
        r := 4 + D*u^2;
        if r lt 0 then continue; end if;
        ok, t := IsSquare(r);
        if not ok then continue; end if;
        Append(~sols, <t,u>);
        if t ne 0 then Append(~sols, <-t,u>); end if;
    end for;

    auts := [];

    for s in sols do
        t := s[1]; u := s[2];
        if (t - b*u) mod 2 ne 0 then continue; end if;
        S := Matrix(Integers(), 2, 2, [
            (t - b*u) div 2,  -c*u,
             a*u,             (t + b*u) div 2
        ]);
        if Determinant(S) eq 1 then
            Append(~auts, S);
        end if;
    end for;

    return auts;
end function;


///////////////////////////////////////////////////////////////////////////
// Exact Gamma_0(N)-equivalence of fixed-point forms
//
// t1, t2 are integer triples [A,B,C], not necessarily primitive.
///////////////////////////////////////////////////////////////////////////

function IsGamma0Equivalent(t1, t2, N)

    g1 := GCD([Integers() | t1[1], t1[2], t1[3]]);
    g2 := GCD([Integers() | t2[1], t2[2], t2[3]]);

    if g1 ne g2 then
        return false;
    end if;

    p1 := [Integers() | t1[1] div g1, t1[2] div g1, t1[3] div g1];
    p2 := [Integers() | t2[1] div g2, t2[2] div g2, t2[3] div g2];

    d1 := p1[2]^2 - 4*p1[1]*p1[3];
    d2 := p2[2]^2 - 4*p2[1]*p2[3];

    if d1 ne d2 then
        return false;
    end if;

    QF := BinaryQuadraticForms(d1);

    sl2_equiv, M := IsEquivalent(QF!p1, QF!p2);

    if not sl2_equiv then
        return false;
    end if;

    for S in AutForm(p1, d1) do
        if (S*M)[2,1] mod N eq 0 then
            return true;
        end if;
    end for;

    return false;
end function;


///////////////////////////////////////////////////////////////////////////
// CM point fixed by an embedding matrix
//
// For
//
//                 M = [a b]
//                     [c e],
//
// the fixed-point equation is
//
//                 c*tau^2 + (e-a)*tau - b = 0.
//
// Equivalently, use
//
//                 [A,B,C] = [-c, a-e, b].
//
// This form need not be primitive when gcd(N,Conductor(R)) > 1.
//
// Computed by FixedPointForm(M), so there is exactly one definition of the
// fixed-point form in the repo.
///////////////////////////////////////////////////////////////////////////

function TauFromEmbedding(M, CC)

    D := Trace(M)^2 - 4*Determinant(M);

    form := FixedPointForm(M);
    A := form[1];
    B := form[2];
    C := form[3];

    assert A gt 0;
    assert B^2 - 4*A*C eq D;

    sqrtD := Sqrt(CC!D);
    if Imaginary(sqrtD) lt 0 then
        sqrtD := -sqrtD;
    end if;
    tau := (-CC!B + sqrtD)/(2*CC!A);
    assert Imaginary(tau) gt 0;

    fixed_tau :=
        (M[1,1]*tau + M[1,2]) /
        (M[2,1]*tau + M[2,2]);

    // Relative, not absolute: an absolute 10^(-50) threshold can fire
    // spuriously when CC is constructed at low cc_prec (fewer than ~50
    // correct digits), even though fixed_tau and tau genuinely agree to
    // working precision.
    assert Abs(fixed_tau-tau) lt 10^(-50) * Abs(tau);

    return tau;
end function;


///////////////////////////////////////////////////////////////////////////
// Construct all optimal embedding matrices
//
// The indexing set is:
//
//       Pic(R)
//         x normalized local roots
//         x extra Atkin-Lehner branches for roots lifting mod p^2.
//
// For a squarefree level prime p:
//
//   local contribution =
//       #roots mod p
//       +
//       #roots mod p which lift to roots mod p^2, when p | D.
//
// This is exactly Voight Proposition 30.6.12 for e = 1.
///////////////////////////////////////////////////////////////////////////

function OptimalEmbeddingMatrices(D, N)

    QF := BinaryQuadraticForms(D);
    R  := QuadraticOrder(QF);

    gamma := R.2;
    tr := Integers()!Trace(gamma);
    nm := Integers()!Norm(gamma);

    assert D eq tr^2 - 4*nm;

    ps := PrimeFactors(N);

    // Squarefree only: the CRT over ps is wrong for prime powers.  This must be
    // a hard error, never an empty return; silently turning "cannot handle this
    // level" into "no CM points here" is what manufactures spurious exceptional
    // points.
    if &*ps ne N then
        error Sprintf("cm_points: level must be squarefree, got N = %o", N);
    end if;

    Zx<x> := PolynomialRing(Integers());
    poly_R := x^2 - tr*x + nm;

    //---------------------------------------------------------------------
    // Picard group = binary quadratic form class group.
    //---------------------------------------------------------------------

    PicR, class_to_form := ClassGroup(QF);

    //---------------------------------------------------------------------
    // Roots modulo each p and the roots producing extra AL branches.
    //---------------------------------------------------------------------

    local_roots := [];
    local_extra_roots := [];

    expected_local_number := 1;

    for p in ps do

        Fp := GF(p);
        Fpx<xp> := PolynomialRing(Fp);

        poly_p := xp^2 - Fp!tr*xp + Fp!nm;

        roots_p := [
            Integers()!rr[1] : rr in Roots(poly_p)
        ];

        Sort(~roots_p);

        // A local obstruction means there are no embeddings.
        if #roots_p eq 0 then
            return {}, [* *], [* *], PicR;
        end if;

        extra_p := {Integers()|};

        // If p does not divide D, the AL conjugate is equivalent to the
        // conjugate normalized root and is not an additional local class.
        if D mod p eq 0 then
            for s in roots_p do
                if RootLiftsModuloSquare(s,p,tr,nm) then
                    Include(~extra_p, s);
                end if;
            end for;
        end if;

        Append(~local_roots, roots_p);
        Append(~local_extra_roots, extra_p);

        expected_local_number *:= #roots_p + #extra_p;
    end for;

    //---------------------------------------------------------------------
    // CRT the local roots.
    //
    // For every global root tuple, record the primes where the selected
    // local root has an additional Atkin-Lehner branch.
    //---------------------------------------------------------------------

    orientation_data := [* *];

    all_choices := CartesianProduct(local_roots);

    for choice in all_choices do

        residues := [
            choice[i] : i in [1..#ps]
        ];

        s := CRT(residues, ps) mod N;

        extra_primes := [];

        for i in [1..#ps] do
            if choice[i] in local_extra_roots[i] then
                Append(~extra_primes, ps[i]);
            end if;
        end for;

        Append(~orientation_data, <s, extra_primes>);
    end for;

    // Construct the Picard orbit and all extra local AL branches.

    embs := {};
    emb_data := [* *];

    I2 := IdentityMatrix(Integers(),2);

    for orient in orientation_data do

        s := orient[1];
        extra_primes := orient[2];

        // This convention makes the upper-left entry congruent to s mod N.
        B0 := tr - 2*s;

        assert (B0^2-D) mod (4*N) eq 0;

        // Product of primes at which this root has an extra branch.
        extra_q := 1;

        for p in extra_primes do
            extra_q *:= p;
        end for;

        // Divisors of extra_q enumerate all combinations of the extra
        // local Atkin-Lehner involutions.
        branch_divisors := Divisors(extra_q);

        for g in PicR do

            class_form := class_to_form(g);

            f := OrientedClassRepresentative(
                class_form, N, B0
            );

            a := f[1];
            b := f[2];
            c := f[3];

            assert c mod N eq 0;
            assert (tr-b) mod 2 eq 0;
            assert (tr+b) mod 2 eq 0;

            // Base embedding.
            // The form f itself is primitive. The corresponding fixed-point
            // form may become imprimitive when gcd(N,Conductor(QF)) > 1;
            // this does not imply failure of optimality in O_0(N).

            M0 := Matrix(Integers(), 2, 2, [
                (tr-b) div 2,  c div N,
                -N*a,          (tr+b) div 2
            ]);

            assert Trace(M0) eq tr;
            assert Determinant(M0) eq nm;
            assert M0^2 - tr*M0 + nm*I2
                   eq ZeroMatrix(Integers(),2,2);
            assert IsOptimalEmbeddingMatrix(M0,N);

            for q in branch_divisors do

                M := AtkinLehnerConjugate(M0,N,q);

                assert Trace(M) eq tr;
                assert Determinant(M) eq nm;
                assert M^2 - tr*M + nm*I2
                       eq ZeroMatrix(Integers(),2,2);
                assert IsOptimalEmbeddingMatrix(M,N);

                Include(~embs, M);

                // Data:
                // <root mod N, Picard class, AL branch q,
                //  oriented class form, embedding matrix>
                Append(~emb_data, <s, g, q, f, M>);

            end for;
        end for;
    end for;

    expected_global_number :=
        #PicR * expected_local_number;

    assert #emb_data eq expected_global_number;
    assert #embs eq expected_global_number;
    assert #embs eq NumberOfOptimalEmbeddings(R,N);

    return embs, emb_data, orientation_data, PicR;
end function;


// Every optimal embedding's tau, ordered by height.
//
// Im(tau) = sqrt(|D|) / (2A) with A = -M[2,1] > 0, so descending Im is
// ascending A.  We sort on the exact integer A and not on the floating
// Im: sorting on Im would make the returned order depend on working
// precision, which is the defect this construction exists to remove.
//
// Returns [] when there is no optimal embedding.  Raises for non-squarefree N.
//
// Note: this returns one tau per optimal embedding.  It does not group,
// deduplicate, or quotient by any group action, and the ordering is not a
// claim that the first element is best in any sense.
//
// These are not Heegner points, and the function is deliberately not named
// for them.  A Heegner point of discriminant D requires
// End(E) = End(E') = O_D.  This construction also returns points where the
// two endomorphism rings differ and meet only in O_D, optimality in
// O_0(N) asserts R = End(E) cap End(E'), which is weaker.  Example:
// N = 399, D = -147 gives the embedding M = [53, 7; -399, -52], whose
// fixed-point form <399,105,7> has content 7 and primitive part <57,15,1>
// of discriminant -3.  So End(E) = O_-3 while End(E') = O_-147.

function CMTaus(D, N, CC)

    embs := OptimalEmbeddingMatrices(D, N);

    pairs := [];

    for M in embs do
        A := -M[2,1];
        if A lt 0 then
            A := -A;
        end if;
        Append(~pairs, <A, M>);
    end for;

    Sort(~pairs, func<x, y | x[1] - y[1]>);

    return [TauFromEmbedding(p[2], CC) : p in pairs];
end function;


// Gamma_0(N)*-orbits of the optimal-embedding taus
//
// OptimalEmbeddingMatrices is already a bijection onto Gamma_0(N)-conjugacy
// classes, measured over 244 (N,D) pairs, no two of its matrices are ever
// Gamma_0(N)-equivalent, so Gamma_0(N) alone buys no reduction.  The
// redundancy is entirely the Atkin-Lehner action, which collapses the set by
// a factor of den = 2^omega(N) or 2^(omega(N)-1).
//
// Acting by the omega(N) prime-power generators and taking connected
// components gives the same partition as acting by all 2^omega(N)
// involutions, at n^2*omega instead of n^2*2^omega.
//
// Returns a sequence of orbits; each orbit is a sequence of <A, M, tau>
// sorted by the exact form triple (A, B, C); ascending A, ties broken by
// B then C, and the orbits themselves are ordered the same way, on the
// triple of their minimum-A member.  This is a total, deterministic order:
// 180 of 226 measured (N,D) pairs have two or more orbits sharing the same
// minimum A (e.g. N=329, D=-223 gives mins [329,329,329,329,658,658,658]),
// so sorting on A alone leaves those ties resolved only by incidental
// Setseq/Sort behaviour.  A, B, C are all exact integers; nothing here
// sorts on the floating Im(tau), so neither the grouping nor the ordering
// can depend on working precision, and the comparator itself never touches
// a float.
//
// Returns [] when there is no optimal embedding.

function CMTauOrbits(D, N, CC)

    embs := OptimalEmbeddingMatrices(D, N);

    if #embs eq 0 then
        return [];
    end if;

    L     := Setseq(embs);
    n     := #L;
    forms := [FixedPointForm(M) : M in L];

    // N is squarefree here (OptimalEmbeddingMatrices errors otherwise), so the
    // prime-power generators are just the prime divisors.
    gens := [p^Valuation(N,p) : p in PrimeFactors(N)];

    parent := [Integers() | i : i in [1..n]];

    function UFRoot(parent, i)
        while parent[i] ne i do
            i := parent[i];
        end while;
        return i;
    end function;

    for i in [1..n] do
        for q in gens do

            fc := FixedPointForm(AtkinLehnerConjugate(L[i], N, q));

            hits := [j : j in [1..n] | IsGamma0Equivalent(fc, forms[j], N)];

            // Zero hits means the enumeration is incomplete or the equivalence
            // test is wrong; two or more means the constructed matrices are not
            // pairwise Gamma_0(N)-inequivalent, contradicting the measured fact
            // this construction rests on.  Neither may degrade silently into a
            // smaller answer, that is how spurious exceptional points get
            // manufactured.
            error if #hits ne 1,
                Sprintf("cm_points: the w_%o image of embedding %o matched %o embeddings, expected exactly 1 (D = %o, N = %o)",
                        q, i, #hits, D, N);

            ri := UFRoot(parent, i);
            rj := UFRoot(parent, hits[1]);

            if ri lt rj then
                parent[rj] := ri;
            elif rj lt ri then
                parent[ri] := rj;
            end if;

        end for;
    end for;

    roots := [UFRoot(parent, i) : i in [1..n]];

    // Total, deterministic comparator on the exact form triple: ascending A,
    // ties broken by B then C.  Used both within an orbit and between orbits.
    function CompareForms(f, g)
        if f[1] ne g[1] then return f[1] - g[1]; end if;
        if f[2] ne g[2] then return f[2] - g[2]; end if;
        return f[3] - g[3];
    end function;

    orbit_list := [];  // <orb, min_form>, min_form for the between-orbit sort

    for r in Sort(Setseq(Set(roots))) do

        members := [i : i in [1..n] | roots[i] eq r];

        Sort(~members, func<i, j | CompareForms(forms[i], forms[j])>);

        orb := [<forms[i][1], L[i], TauFromEmbedding(L[i], CC)> : i in members];

        Append(~orbit_list, <orb, forms[members[1]]>);
    end for;

    // Genuine closure check on the final orbit structure: for each orbit and
    // each generator q, the AL image of every member's fixed-point form is
    // Gamma_0(N)-equivalent to some member of that same orbit.  This is what
    // the design promises ("each [orbit] is closed under every generator")
    // and is a real check of the union-find result, unlike a sum-of-sizes
    // assert, which is true by construction of the "members" partition
    // above and asserts nothing about correctness.  Recomputed independently
    // of the `roots`/`parent` bookkeeping that built the partition.
    for pair in orbit_list do
        orb := pair[1];
        orbit_forms := [FixedPointForm(t[2]) : t in orb];
        for t in orb do
            for q in gens do
                fc := FixedPointForm(AtkinLehnerConjugate(t[2], N, q));
                assert exists{f : f in orbit_forms | IsGamma0Equivalent(fc, f, N)};
            end for;
        end for;
    end for;

    Sort(~orbit_list, func<x, y | CompareForms(x[2], y[2])>);

    return [pair[1] : pair in orbit_list];
end function;


///////////////////////////////////////////////////////////////////////////
// One tau per Gamma_0(N)*-orbit.
//
// The representative is the minimum-A member of its own orbit.  
//
// D is the discriminant, N is the level, CC is the complex field
///////////////////////////////////////////////////////////////////////////

function CMTauReps(D, N, CC)
    orbits := CMTauOrbits(D, N, CC);
    return [orb[1][3] : orb in orbits];
end function;
