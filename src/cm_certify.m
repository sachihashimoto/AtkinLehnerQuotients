// src/cm_certify.m
//
// Proofs, in exact rational arithmetic, about the images of CM points on the
// canonical model of X_0(N)*. The mathematics is in notes/cm_integrality.tex:
// for an integral star form F and a CM point tau the number
//     nu_F(tau)^sigma_0(N)
// is the root of a rational integer when the point is rational, so an upper
// bound below 1 proves F vanishes there, and an upper bound in general bounds
// the height of the point.
//
// Entry points:  CertifyRationalCMPoint(N, fs, Cs, P, form, e)
//                CertifyVanishingAtCM(N, fs, Cs, mvec, forms, e)
//                CMHeightBounds(N, fs, Cs, form, e)
//                DeligneConstants(fs, N)
//
// Depends on cm_points.m only. Not loadable standalone. The drivers that
// apply these to a list of rational points are in labeling.m
// (ProveRationalCMLabels, CertifyRationalCMPoints).
//
// Real numbers are enclosed in balls <mid, rad> with rational entries, and
// complex numbers in discs <x, y, rad>. Floating point is used only to choose
// how many series terms to sum, never in a bound.
//
// The elliptic order e is an input (callers take it from EllipticDiscsByOrder). An e that
// is too small is caught (every form then vanishes and the nonvanishing check
// fails); an e that is too large is not detected here.

// ---------------------------------------------------------------------------
// Rational ball arithmetic
// ---------------------------------------------------------------------------

function RBRound(b, p)
    s := 2^p;
    m := Round(b[1]*s)/s;
    r := Ceiling((b[2] + Abs(b[1] - m))*s*s)/(s*s);
    return <m, r>;
end function;

function RBAdd(a, b)
    return <a[1] + b[1], a[2] + b[2]>;
end function;

function RBMul(a, b, p)
    return RBRound(<a[1]*b[1], Abs(a[1])*b[2] + Abs(b[1])*a[2] + a[2]*b[2]>, p);
end function;

function RBScale(c, a)
    return <c*a[1], Abs(c)*a[2]>;
end function;

// Rational bounds lo <= sqrt(x) <= up for rational x >= 0.
function SqrtBounds(x, p)
    n := Isqrt(Floor(x*4^p));
    return n/2^p, (n + 1)/2^p;
end function;

// Complex balls are discs <x, y, r>: centre x + iy, radius r. A disc, not a
// rectangle: multiplying rectangles by q inflates the radius by up to
// sqrt(2)|q| per step, which diverges over thousands of terms when |q| is
// close to 1, whereas for discs the factor is |q| < 1.
function CBAbsUpper(z, p)
    _, up := SqrtBounds(z[1]^2 + z[2]^2, p);
    return up + z[3];
end function;

function CBAbsLower(z, p)
    lo := SqrtBounds(z[1]^2 + z[2]^2, p);
    return Maximum(0, lo - z[3]);
end function;

function CBMul(z, w, p)
    s := 2^p;
    x := z[1]*w[1] - z[2]*w[2];
    y := z[1]*w[2] + z[2]*w[1];
    _, az := SqrtBounds(z[1]^2 + z[2]^2, p);
    _, aw := SqrtBounds(w[1]^2 + w[2]^2, p);
    xr := Round(x*s)/s; yr := Round(y*s)/s;
    r := az*w[3] + aw*z[3] + z[3]*w[3] + Abs(x - xr) + Abs(y - yr);
    return <xr, yr, Ceiling(r*s*s)/(s*s)>;
end function;

function CBAdd(z, w)
    return <z[1] + w[1], z[2] + w[2], z[3] + w[3]>;
end function;

function CBScale(c, z)
    return <c*z[1], c*z[2], Abs(c)*z[3]>;
end function;

// pi by Machin's formula. Both arctangent series alternate with decreasing
// terms, so each truncation error is at most the first omitted term.
function PiBall(p)
    function AtanInv(k)
        s := 0/1; i := 0; err := 0;
        repeat
            t := 1/((2*i + 1)*k^(2*i + 1));
            if t lt 1/2^(p + 8) then err := t; break; end if;
            s +:= (-1)^i*t;
            i +:= 1;
        until false;
        return <s, err>;
    end function;
    a := AtanInv(5); b := AtanInv(239);
    return RBRound(<16*a[1] - 4*b[1], 16*a[2] + 4*b[2]>, p + 4);
end function;

// Rational bounds lo <= exp(t) <= up for rational t. Halve the argument until
// |s| <= 1/2, sum the Taylor series (remainder at most 2|s|^n/n!), square back.
function ExpBounds(t, p)
    k := 0;
    while Abs(t)/2^k gt 1/2 do k +:= 1; end while;
    s := t/2^k;
    wp := p + 2*k + 20;
    sum := 0/1; term := 1/1; n := 0;
    while Abs(term) ge 1/2^(wp + 4) do
        sum +:= term;
        n +:= 1;
        term *:= s/n;
    end while;
    b := RBRound(<sum, 2*Abs(term)>, wp);
    for i in [1..k] do b := RBMul(b, b, wp); end for;
    return b[1] - b[2], b[1] + b[2];
end function;

// Balls for cos(x) and sin(x), x a ball with |mid| <= 4. Taylor at the
// midpoint with the Lagrange remainder |m|^n/n!, plus the radius because both
// functions are 1-Lipschitz.
function CosSinBalls(x, p)
    m := x[1];
    error if Abs(m) gt 4, "CosSinBalls: argument out of range";
    c := 0/1; s := 0/1; term := 1/1; n := 0;
    while n le 4 or Abs(term) ge 1/2^(p + 4) do
        case n mod 4:
            when 0: c +:= term;
            when 1: s +:= term;
            when 2: c -:= term;
            when 3: s -:= term;
        end case;
        n +:= 1;
        term *:= m/n;
    end while;
    rad := Abs(term) + x[2];
    return RBRound(<c, rad>, p), RBRound(<s, rad>, p);
end function;

// ---------------------------------------------------------------------------
// Fourier coefficient bound (notes, Proposition 4.2)
// ---------------------------------------------------------------------------

function HeckeMatrixOnStarForms(fs, ell, ncoef)
    g := #fs;
    A := Matrix(Rationals(), g, ncoef, [[Coefficient(f, n) : n in [1..ncoef]] : f in fs]);
    error if Rank(A) ne g, "HeckeMatrixOnStarForms: forms are dependent on the first coefficients";
    rows := [];
    for f in fs do
        v := Vector(Rationals(), [Coefficient(f, ell*n)
                + ((n mod ell eq 0) select ell*Coefficient(f, n div ell) else 0) : n in [1..ncoef]]);
        ok, x := IsConsistent(A, v);
        error if not ok, Sprintf("HeckeMatrixOnStarForms: T_%o does not preserve the span", ell);
        Append(~rows, Eltseq(x));
    end for;
    return Matrix(Rationals(), g, g, rows);
end function;

// Rational C_i with |a_n(f_i)| <= C_i * sigma_0(n) * sqrt(n) for all n >= 1.
function DeligneConstants(fs, N)
    g := #fs;
    ncoef := 40;
    while Rank(Matrix(Rationals(), g, ncoef, [[Coefficient(f, n) : n in [1..ncoef]] : f in fs])) lt g do
        ncoef *:= 2;
    end while;
    a1 := Vector(Rationals(), [Coefficient(f, 1) : f in fs]);
    T := ZeroMatrix(Rationals(), g, g);
    nused := 0; found := false;
    for ell in PrimesUpTo(100) do
        if N mod ell eq 0 then continue; end if;
        error if ell*ncoef ge Minimum([AbsolutePrecision(f) : f in fs]),
            "DeligneConstants: not enough q-expansion terms for the Hecke operators";
        nused +:= 1;
        T +:= nused*HeckeMatrixOnStarForms(fs, ell, ncoef);
        if IsSquarefree(CharacteristicPolynomial(T)) then found := true; break; end if;
    end for;
    error if not found, Sprintf("DeligneConstants: no Hecke combination separates the eigenforms at level %o", N);
    pows := [T^j : j in [0..2*g - 2]];
    M := Matrix(Rationals(), g, g, [[Trace(pows[j + l + 1]) : l in [0..g - 1]] : j in [0..g - 1]]);
    Minv := M^-1;
    kappa := 1/1;
    for q in PrimeDivisors(N) do
        _, up := SqrtBounds(q, 20);
        kappa *:= 1 + up;
    end for;
    Cs := [];
    for i in [1..g] do
        u := Vector(Rationals(), [(pows[j + 1][i], a1) : j in [0..g - 1]]);
        tr := (u*Minv, u);
        _, up := SqrtBounds(g*tr, 20);
        Append(~Cs, kappa*up);
    end for;
    return Cs;
end function;

// ---------------------------------------------------------------------------
// The CM point and the two sides of the inequality
// ---------------------------------------------------------------------------

// Exact forms [A,B,C] of the Gamma_0(N)*-orbit representatives of discriminant
// D, in CMTauReps order: tau is the root of A*tau^2 + B*tau + C in the upper
// half plane.
function CMOrbitForms(D, N)
    orbits := CMTauOrbits(D, N, ComplexField(100));
    return [FixedPointForm(orb[1][2]) : orb in orbits];
end function;

function EllipticOrderOfDisc(D, ell_pts)
    for ell in [2, 3, 4, 6] do
        if D in Keys(ell_pts[ell]) then return ell; end if;
    end for;
    return 1;
end function;

// Rational lower bound for prod_{d | N} ||eta||(d*tau)^4, with
// ||eta||(z) = |eta(z)| Im(z)^(1/4), which is SL_2(Z)-invariant. So each
// factor is evaluated at the root z of the reduced form equivalent to that of
// d*tau, where |e^(2 pi i z)| <= e^(-pi sqrt 3).
function EtaNormProductLower(form, N, p)
    A := form[1]; B := form[2]; C := form[3];
    pib := PiBall(p);
    pilo := pib[1] - pib[2]; piup := pib[1] + pib[2];
    prod := 1/1;
    for d in Divisors(N) do
        c := GCD([A, B*d, C*d^2]);
        a0 := A div c; b0 := (B*d) div c; c0 := (C*d^2) div c;
        Dp := b0^2 - 4*a0*c0;
        f := Reduction(QuadraticForms(Dp)![a0, b0, c0]);
        a := f[1];
        slo, sup := SqrtBounds(-Dp, p);
        // |q| <= rho, and |prod (1 - q^n)| >= 1 - rho/(1 - rho)
        _, rho := ExpBounds(-pilo*slo/a, p);
        error if rho ge 1/100, "EtaNormProductLower: form not reduced";
        elo := ExpBounds(-piup*sup/(6*a), p);
        prod *:= (slo/(2*a))*elo*(1 - rho/(1 - rho))^4;
    end for;
    return prod;
end function;

// Balls for the truncated sums 12^(e-1) * sum_{n <= m} n^(e-1) a_n(f_i) q^n at
// the root of `form`, and a rational tail factor t such that the omitted part
// of the series for a form with constant C has absolute value at most C*t.
function CMBasisValues(fs, form, e, m, p)
    A := form[1]; B := form[2]; C := form[3];
    Delta := 4*A*C - B^2;
    error if Delta le 0, "CMBasisValues: form is not positive definite";
    pib := PiBall(p);
    slo, sup := SqrtBounds(Delta, p);
    // |q| = exp(-pi sqrt(Delta)/A)
    rlo := ExpBounds(-(pib[1] + pib[2])*sup/A, p);
    _, rup := ExpBounds(-(pib[1] - pib[2])*slo/A, p);
    rb := <(rlo + rup)/2, (rup - rlo)/2>;
    // arg q = -pi*B/A, reduced to (-pi, pi]
    Br := B mod (2*A);
    if Br gt A then Br -:= 2*A; end if;
    cb, sb := CosSinBalls(RBScale(Br/A, pib), p);
    qre := RBMul(rb, cb, p); qim := RBMul(rb, sb, p);
    q := <qre[1], -qim[1], qre[2] + qim[2]>;
    sums := [<0/1, 0/1, 0/1> : f in fs];
    qn := <1/1, 0/1, 0/1>;
    for n in [1..m] do
        qn := CBMul(qn, q, p);
        w := n^(e - 1);
        for i in [1..#fs] do
            a := Integers()!Coefficient(fs[i], n);
            if a ne 0 then sums[i] := CBAdd(sums[i], CBScale(w*a, qn)); end if;
        end for;
    end for;
    sums := [CBScale(12^(e - 1), s) : s in sums];
    // |a_n| n^(e-1) <= 2 C n^e, and n^e r^n decays at least geometrically with
    // ratio r*((m+2)/(m+1))^e from n = m+1 on.
    ratio := rup*((m + 2)/(m + 1))^e;
    if ratio ge 1 then return sums, -1; end if;
    tail := 12^(e - 1)*2*(m + 1)^e*rup^(m + 1)/(1 - ratio);
    return sums, tail;
end function;

// Rational upper bound for nu^sigma_0(N), where U bounds |F^[e](tau)| above
// and L bounds prod ||eta||(d tau)^4 below. Uses that sigma_0(N) is even.
function NuPowerUpper(N, form, e, U, L)
    s0 := NumberOfDivisors(N);
    error if IsOdd(s0), "NuPowerUpper: level 1 is not supported";
    Delta := 4*form[1]*form[3] - form[2]^2;
    return N^((e*s0) div 2)*(Delta/(4*form[1]^2))^((e*s0) div 2)*U^s0/L^e;
end function;

// One evaluation at one CM point: value balls, tail factor and eta bound.
// Returns ok = false when the series has too few terms for the tail bound.
//
// The number of terms is chosen in floating point so that the tail is around
// 2^-TailBits. That choice is only a cost estimate: the tail bound actually
// used is the rational one CMBasisValues returns for whatever m was chosen.
function CMEvaluationData(N, fs, form, e, p : TailBits := 48)
    m := Minimum([AbsolutePrecision(f) : f in fs]) - 1;
    RRf := RealField(20);
    logr := -Pi(RRf)*Sqrt(RRf!(4*form[1]*form[3] - form[2]^2))/form[1];
    m := Minimum(m, Ceiling((TailBits*Log(RRf!2) + 30 + 8*e)/(-logr)));
    sums, tail := CMBasisValues(fs, form, e, m, p);
    if tail lt 0 then return false, 0, 0, 0; end if;
    return true, sums, tail, EtaNormProductLower(form, N, p);
end function;

// Upper bound for |F^[e](tau)| with F = sum mvec[i]*fs[i].
function LinearFormUpper(mvec, sums, tail, Cs, p)
    z := <0/1, 0/1, 0/1>;
    CF := 0/1;
    for i in [1..#mvec] do
        if mvec[i] eq 0 then continue; end if;
        z := CBAdd(z, CBScale(mvec[i], sums[i]));
        CF +:= Abs(mvec[i])*Cs[i];
    end for;
    return CBAbsUpper(z, p) + CF*tail;
end function;

// ---------------------------------------------------------------------------
// Certificates
// ---------------------------------------------------------------------------

// Proves that F = sum mvec[i]*fs[i] vanishes at every CM point in `forms`, in
// the sense that the hyperplane mvec contains the canonical image. `forms`
// must be a full set of Galois conjugates (one form for a rational point), all
// of elliptic order e. True means proved; false means not proved, which is
// not a proof of the opposite.
function CertifyVanishingAtCM(N, fs, Cs, mvec, forms, e : Prec := 128)
    prod := 1/1;
    for form in forms do
        ok, sums, tail, L := CMEvaluationData(N, fs, form, e, Prec);
        if not ok then return false; end if;
        prod *:= NuPowerUpper(N, form, e, LinearFormUpper(mvec, sums, tail, Cs, Prec), L);
    end for;
    return prod lt 1;
end function;

// Proved bounds b_i with |a_i| <= b_i for the primitive integer coordinates
// (a_1 : ... : a_g) of a rational CM point. Returns ok = false if the series
// is too short.
function CMHeightBounds(N, fs, Cs, form, e : Prec := 128)
    ok, sums, tail, L := CMEvaluationData(N, fs, form, e, Prec);
    if not ok then return false, []; end if;
    s0 := NumberOfDivisors(N);
    unit := [Integers() | 0 : i in [1..#fs]];
    bounds := [];
    for i in [1..#fs] do
        mvec := unit; mvec[i] := 1;
        nu := NuPowerUpper(N, form, e, LinearFormUpper(mvec, sums, tail, Cs, Prec), L);
        fl := Floor(nu);
        Append(~bounds, fl eq 0 select 0 else Iroot(fl, s0));
    end for;
    return true, bounds;
end function;

// Proves that the rational point P (a sequence of g rationals, not all zero)
// is the canonical image of the rational CM point given by `form`. Checks
// that g-1 independent integral hyperplanes through P contain the image, and
// that some coordinate form is provably nonzero there, which rules out an
// elliptic order e that is too small.
function CertifyRationalCMPoint(N, fs, Cs, P, form, e : Prec := 128)
    g := #fs;
    den := LCM([Denominator(c) : c in P]);
    a := [Integers() | den*c : c in P];
    a := [c div GCD(a) : c in a];
    ok, sums, tail, L := CMEvaluationData(N, fs, form, e, Prec);
    if not ok then return false; end if;
    K := LLL(KernelMatrix(Transpose(Matrix(Integers(), 1, g, a))));
    error if Nrows(K) ne g - 1, "CertifyRationalCMPoint: kernel has the wrong rank";
    for r in [1..g - 1] do
        mvec := Eltseq(K[r]);
        if NuPowerUpper(N, form, e, LinearFormUpper(mvec, sums, tail, Cs, Prec), L) ge 1 then
            return false;
        end if;
    end for;
    nonzero := false;
    for i in [1..g] do
        if a[i] eq 0 then continue; end if;
        if CBAbsLower(sums[i], Prec) gt Cs[i]*tail then nonzero := true; break; end if;
    end for;
    return nonzero;
end function;
