// tests/test_cm_certify.m
// Tests for the exact CM certificates in src/cm_certify.m.
// Run: tests/run.sh test_cm_certify
//
// The mathematics is in notes/cm_integrality.tex. Expected values come from
// Magma's own real arithmetic (for the ball functions) and from the point
// search and the existing floating-point labeling (for the CM points), never
// from this module.

load "src/AtkinLehner.m";
load "tests/assertions.m";
SetSeed(1);

results := NewResults();
RR := RealField(80);

printf "\n=== Ball functions enclose the true value ===\n";
pb := PiBall(150);
AssertEqual(~results, Abs(pb[1] - Pi(RR)) le pb[2] + 10^-70 and pb[2] lt 10^-40, true, "PiBall(150) encloses pi");
for t in [-37/5, -1/1000, 0, 3/7, 12] do
    lo, up := ExpBounds(t, 150);
    v := Exp(RR!t);
    AssertEqual(~results, lo le v*(1 + 10^-70) and up ge v*(1 - 10^-70) and (up - lo) lt 10^-40*v, true,
        Sprintf("ExpBounds(%o) encloses exp", t));
end for;
for m in [-3, -17/7, 0, 1/3, 22/7] do
    c, s := CosSinBalls(<m, 1/10^50>, 150);
    AssertEqual(~results, Abs(c[1] - Cos(RR!m)) le c[2] + 10^-70 and Abs(s[1] - Sin(RR!m)) le s[2] + 10^-70 and c[2] lt 10^-40, true,
        Sprintf("CosSinBalls(%o) encloses cos and sin", m));
end for;
lo, up := SqrtBounds(163, 100);
AssertEqual(~results, lo^2 le 163 and up^2 ge 163 and up - lo eq 1/2^100, true, "SqrtBounds(163)");

// A disc product must contain the product of any two points of the factors.
z := <3/5, -4/7, 1/1000>; w := <-2/3, 1/9, 1/500>;
zw := CBMul(z, w, 100);
CCt := ComplexField(40); I := CCt.1;
zp := (3/5 + 1/1000) + I*(-4/7); wp := (-2/3) + I*(1/9 - 1/500);
AssertEqual(~results, Abs(zp*wp - (zw[1] + I*zw[2])) le zw[3], true, "CBMul encloses a boundary product");

printf "\n=== Coefficient bound holds on the available coefficients ===\n";
for N in [137, 311, 178] do
    ok, prec, fs := LoadStarForms(N);
    Cs := DeligneConstants(fs, N);
    worst := Maximum([Abs(Coefficient(fs[i], n))/(Cs[i]*NumberOfDivisors(n)*Sqrt(RR!n)) : n in [1..prec - 1], i in [1..#fs]]);
    AssertEqual(~results, worst le 1, true, Sprintf("N=%o: |a_n| <= C*d(n)*sqrt(n) for n < %o", N, prec));
end for;

printf "\n=== Rational CM points are proved, level by level ===\n";
for N in [137, 311, 178] do
    rats, X, fs := point_search_X0Nstar(N, 1000);
    discs := Keys(RationalCMDiscs(N));
    d2i, unproved := CertifyRationalCMPoints(N, fs, rats, discs);
    AssertEqual(~results, #unproved, 0, Sprintf("N=%o: nothing left unproved", N));
    AssertEqual(~results, Keys(d2i), discs, Sprintf("N=%o: every rational CM disc proved", N));

    // The proved labels agree with the floating-point labeling.
    CC := ComplexField(100);
    ell_pts, disc_ell_pts := EllipticDiscsByOrder(N);
    rats_cc := [[CC!c : c in Eltseq(P)] : P in rats];
    _, nfail, float_d2i := MatchRationalCMPoints(N, fs, rats_cc, rats, CC, 10^-10, discs, ell_pts, disc_ell_pts);
    AssertEqual(~results, nfail, 0, Sprintf("N=%o: float labeling finds every disc", N));
    for d in discs do
        AssertEqual(~results, Set(d2i[d]), Set(float_d2i[d]), Sprintf("N=%o D=%o: proved index equals float index", N, d));
    end for;

    // Height bounds hold for the proved points.
    Cs := DeligneConstants(fs, N);
    for d in discs do
        forms := CMOrbitForms(d, N);
        e := EllipticOrderOfDisc(d, ell_pts);
        for k in [1..#forms] do
            ok, hb := CMHeightBounds(N, fs, Cs, forms[k], e);
            P := Eltseq(rats[d2i[d][k]]);
            den := LCM([Denominator(c) : c in P]);
            a := [Integers()!(den*c) : c in P]; a := [c div GCD(a) : c in a];
            AssertEqual(~results, ok and forall{i : i in [1..#a] | Abs(a[i]) le hb[i]}, true,
                Sprintf("N=%o D=%o orbit %o: coordinates %o within proved bounds %o", N, d, k, a, hb));
        end for;
    end for;

    // Negative controls: no other rational point is certified as this CM point.
    proved := &join[Set(d2i[d]) : d in discs];
    for d in discs do
        form := CMOrbitForms(d, N)[1];
        e := EllipticOrderOfDisc(d, ell_pts);
        wrong := [j : j in [1..#rats] | j ne d2i[d][1] and CertifyRationalCMPoint(N, fs, Cs, Eltseq(rats[j]), form, e)];
        AssertEqual(~results, wrong, [Integers()|], Sprintf("N=%o D=%o: no other point certified", N, d));
    end for;
    printf "N=%o: %o of %o rational points are proved CM; the rest are %o\n", N, #proved, #rats,
        [j : j in [1..#rats] | j notin proved];
end for;

printf "\n=== A plane through a conjugate pair (N=311, D=-123) ===\n";
N := 311;
rats, X, fs := point_search_X0Nstar(N, 1000);
discs := Keys(RationalCMDiscs(N));
d2i := CertifyRationalCMPoints(N, fs, rats, discs);
ell_pts, disc_ell_pts := EllipticDiscsByOrder(N);
Cs := DeligneConstants(fs, N);
// Hyperplanes through the D=-19 rational CM point and the D=-123 pair,
// proposed by the floating-point plane fit.
P19 := Eltseq(rats[d2i[-19][1]]);
planes := CertifiedPlaneFromCMPair(P19, -123, N, fs, ell_pts, disc_ell_pts);
AssertEqual(~results, #planes ge 1, true, "N=311: float fit proposes a plane through D=-19 and the D=-123 pair");
forms := CMOrbitForms(-123, N);
AssertEqual(~results, #forms, 2, "N=311 D=-123: two conjugate points");
for pl in planes do
    vi := pl[3];
    AssertEqual(~results, CertifyVanishingAtCM(N, fs, Cs, vi, forms, 1), true,
        Sprintf("N=311: plane %o proved to contain the D=-123 pair", vi));
    bad := vi; bad[1] +:= 1;
    AssertEqual(~results, CertifyVanishingAtCM(N, fs, Cs, bad, forms, 1), false,
        Sprintf("N=311: perturbed plane %o is not certified", bad));
end for;

Report(~results, "test_cm_certify");
