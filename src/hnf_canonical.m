// src/hnf_canonical.m
//
// Re-express a canonical model of X_0(N)* in the saturated Hermite-normal-form
// basis of the star cusp forms.  A canonical model is only defined up to a
// change of basis, and the basis XZeroNstarWithForms starts from is an
// arbitrary one; the HNF basis is canonical, so the equations it produces are
// reproducible rather than an artefact of how the forms were computed.
//
// Entry points:  HNFCanonicalCurve(N, X, g)                    from scratch
//                HNFCanonicalCurveFromForms(N, X, bas, g)      from q-expansions
//                HNFCanonicalCurveFromSstar(N, X, Sstar, g); from forms in hand
//
// Not loaded by src/AtkinLehner.m; load it afterwards, so that all_diag_basis
// (QuadraticPoints) and src/modelsX0Nstar.m are already in scope.

// Variable names for the shared ambient P^{g-1} (g <= 8 supported).
function AmbientVarNames(g)
    all := ["x", "y", "z", "w", "t", "u", "v", "s"];
    assert g le #all;
    return [all[i] : i in [1..g]];
end function;

// Defining equations of C as a Magma-parseable string "[ e1, e2, ... ]" using the
// given variable names (so the emitted file is loadable against a shared P).
function CurveEqnsString(C, varnames)
    g := #varnames;
    R := PolynomialRing(Rationals(), g);
    AssignNames(~R, varnames);
    eqstr := [Sprint(R ! e) : e in DefiningPolynomials(C)];
    return "[\n    " cat Join(eqstr, ",\n    ") cat "\n]";
end function;

// Saturated-HNF change-of-basis matrix V (g_i = sum_j V[i,j] f_j) for whatever
// q-expansion basis `bas` spans. Depends only on the (saturated) lattice
// spanned by bas's Fourier coefficients, not on which particular spanning
// basis produced it, so this gives the same canonical V regardless of
// which all_diag_basis run (or cached forms) bas came from. Shared by
// StarHNFTransform (fresh all_diag_basis) and any cache-based reconstruction
// of V that skips all_diag_basis entirely (e.g. scripts/certify_committed_models.m).
function StarHNFTransformFromBas(bas, g)
    prec := Min([AbsolutePrecision(b) : b in bas]) - 1;
    M := Matrix(Integers(), [[Coefficient(bas[i], j) : j in [1..prec]] : i in [1..g]]);

    // Saturate the q-expansion coefficient lattice (undo the global denominator
    // scaling from all_diag_basis), then reduce to Hermite Normal Form to get the
    // unique canonical integral basis of the saturated lattice.
    Msat := Saturation(M);
    H := HermiteForm(Msat);
    Hrows := [i : i in [1..Nrows(H)] | not IsZero(H[i])];
    assert #Hrows eq g;
    H := Matrix([H[i] : i in Hrows]);

    MQ := ChangeRing(M, Rationals());
    HQ := ChangeRing(H, Rationals());
    V := Solution(MQ, HQ);          // V * M = H  (g_i = sum_j V[i,j] f_j)
    assert V*MQ eq HQ;
    assert Determinant(V) ne 0;
    return V;
end function;

// Saturated-HNF change-of-basis matrix V (g_i = sum_j V[i,j] f_j) for the star
// space, together with the recomputed star q-expansions used to verify the
// stored model's coordinate ordering.
function StarHNFTransform(N, g, prec)
    S, ALs := all_diag_basis(N);
    Sstar := [S[i] : i in [1..#S] | forall{w : w in ALs | w[i,i] eq +1}];
    assert #Sstar eq g;

    // all_diag_basis returns an integral basis, so qExpansion here can come
    // back as a series over Integers() rather than Rationals(), Evaluate
    // against a genuinely rational-coefficient equation then fails with
    // "Illegal coercion". Force the ring explicitly.
    Rq := PowerSeriesRing(Rationals());
    bas := [Rq ! qExpansion(f, prec + 1) : f in Sstar];
    V := StarHNFTransformFromBas(bas, g);
    return V, bas;
end function;

// Return the curve X re-embedded in the saturated-HNF star basis.
//
// Certifies two separate things, each via the Sturm bound for the actual
// weight (2*Degree(e)) of the equation being checked, not a fixed weight-2
// precision (a fixed weight-2 bound understates what a degree-d relation,
// weight 2d, needs to prove):
//   1. Coordinate correspondence: X's own defining equations vanish at the
//      freshly-recomputed star q-expansions (f_1(q):...:f_g(q)), i.e. this
//      bas really does correspond to X's coordinates in the same order.
//   2. The transformed equations vanish at the transformed point V*bas, i.e.
//      the HNF-recoordinatized curve returned here is genuinely the same
//      curve, not just dimension/genus-compatible with it.
function HNFCanonicalCurve(N, X, g)
    oldeqns := DefiningPolynomials(X);
    assert #oldeqns gt 0;

    d := Max([Degree(e) : e in oldeqns]);
    B := ModularSturmBound(N, 2*d);
    prec := B + 21;   // small safety margin over the Sturm bound

    V, bas := StarHNFTransform(N, g, prec);

    // ---- verify coordinate correspondence: eqns vanish on (f_1(q):...:f_g(q)) ----
    for e in oldeqns do
        assert IsHomogeneous(e);
        val := Evaluate(e, bas);
        ok, _ := CertifyModularIdentity(val, N, 2*Degree(e));
        assert ok;
    end for;

    // ---- linear change of coordinates: y = V x, so x = V^{-1} y ----
    Vinv := V^(-1);
    Q := Rationals();
    Pnew := PolynomialRing(Q, g);
    AssignNames(~Pnew, AmbientVarNames(g));
    subst := [ &+[Vinv[i,j]*Pnew.j : j in [1..g]] : i in [1..g] ];

    neweqns := [];
    for e in oldeqns do
        enew := Evaluate(e, subst);
        cs := Coefficients(enew);
        if #cs eq 0 then continue; end if;
        d := LCM([Denominator(c) : c in cs]);
        enew := d * enew;
        ics := [Integers() ! c : c in Coefficients(enew)];
        gg := GCD(ics);
        if gg ne 0 then enew := enew / gg; end if;
        Append(~neweqns, enew);
    end for;

    // ---- verify the transformed equations vanish at the transformed point V*bas ----
    newbas := [&+[V[i,j]*bas[j] : j in [1..g]] : i in [1..g]];
    for e in neweqns do
        assert IsHomogeneous(e);
        val := Evaluate(e, newbas);
        ok, _ := CertifyModularIdentity(val, N, 2*Degree(e));
        assert ok;
    end for;

    Pg1 := ProjectiveSpace(Pnew);
    C := Curve(Pg1, neweqns);
    assert Dimension(C) eq 1;
    assert Genus(C) eq g;
    return C, V;
end function;

// Same as HNFCanonicalCurve but takes the star q-expansions `bas` directly
// (coords of X in the same order as bas), so it does not recompute
// all_diag_basis.  Used when that computation is very expensive (e.g. N=870).
//
// hnf_prec (the saturation/HNF lattice construction) and the Sturm
// certification bound are deliberately kept as separate roles: the lattice
// construction is free to use every cached coefficient, but the certification
// below must independently verify that hnf_prec actually exceeds the bound
// each equation's own weight requires, errors out rather than silently
// certifying at insufficient precision.
function HNFCanonicalCurveFromForms(N, X, bas, g)
    oldeqns := DefiningPolynomials(X);
    assert #oldeqns gt 0;
    assert #bas eq g;

    hnf_prec := Min([AbsolutePrecision(b) : b in bas]) - 1;

    d := Max([Degree(e) : e in oldeqns]);
    B := ModularSturmBound(N, 2*d);
    error if hnf_prec le B,
        Sprintf("HNFCanonicalCurveFromForms: cached forms have too few terms to certify, need precision > %o (Sturm bound for weight %o on Gamma_0(%o)), got %o",
                B, 2*d, N, hnf_prec);

    V := StarHNFTransformFromBas(bas, g);

    for e in oldeqns do
        assert IsHomogeneous(e);
        val := Evaluate(e, bas);
        ok, _ := CertifyModularIdentity(val, N, 2*Degree(e));
        assert ok;
    end for;

    Vinv := V^(-1);
    Q := Rationals();
    Pnew := PolynomialRing(Q, g);
    AssignNames(~Pnew, AmbientVarNames(g));
    subst := [ &+[Vinv[i,j]*Pnew.j : j in [1..g]] : i in [1..g] ];
    neweqns := [];
    for e in oldeqns do
        enew := Evaluate(e, subst);
        cs := Coefficients(enew);
        if #cs eq 0 then continue; end if;
        d := LCM([Denominator(c) : c in cs]);
        enew := d * enew;
        ics := [Integers() ! c : c in Coefficients(enew)];
        gg := GCD(ics);
        if gg ne 0 then enew := enew / gg; end if;
        Append(~neweqns, enew);
    end for;

    newbas := [&+[V[i,j]*bas[j] : j in [1..g]] : i in [1..g]];
    for e in neweqns do
        assert IsHomogeneous(e);
        val := Evaluate(e, newbas);
        ok, _ := CertifyModularIdentity(val, N, 2*Degree(e));
        assert ok;
    end for;

    Pg1 := ProjectiveSpace(Pnew);
    C := Curve(Pg1, neweqns);
    assert Dimension(C) eq 1;
    assert Genus(C) eq g;
    return C, V;
end function;

// Same as HNFCanonicalCurve, but takes a live Sstar (the same CuspForms basis
// XZeroNstarWithForms already used to build X, e.g. as returned by
// exceptional_pts_X0Nstar) instead of calling all_diag_basis a second time.
// V is a canonical function of the saturated lattice spanned by the star
// q-expansions (see StarHNFTransformFromBas), not of which basis produced
// them, so this gives the identical V; and hence the identical committed
// equations, that HNFCanonicalCurve's own fresh all_diag_basis call would.
// Callers that already have Sstar in scope (gen_genus_models.m) should use
// this instead of HNFCanonicalCurve to avoid paying all_diag_basis twice
// per level.
function HNFCanonicalCurveFromSstar(N, X, Sstar, g)
    oldeqns := DefiningPolynomials(X);
    assert #oldeqns gt 0;
    d := Max([Degree(e) : e in oldeqns]);
    B := ModularSturmBound(N, 2*d);
    prec := B + 21;   // small safety margin over the Sturm bound
    // all_diag_basis returns an integral basis, so qExpansion here can come
    // back as a series over Integers() rather than Rationals(), Evaluate
    // against a genuinely rational-coefficient equation then fails with
    // "Illegal coercion". Force the ring explicitly.
    Rq := PowerSeriesRing(Rationals());
    bas := [Rq ! qExpansion(f, prec + 1) : f in Sstar];
    return HNFCanonicalCurveFromForms(N, X, bas, g);
end function;
