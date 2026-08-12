// tests/test_sturm_certification.m
// Regression tests for the Sturm-bound certification added to the model
// builders (ModularSturmBound/CertifyModularIdentity/CertifyCanonicalEquations
// in src/modelsX0Nstar.m; CertifyEquationsAgainstCache and the hyperelliptic
// cleared-identity check in src/triple_covers.m; the degree-aware bound in
// src/hnf_canonical.m).
//
// Before this fix, a candidate model was accepted once the resulting scheme
// had the right dimension and genus, evidence the equations are correct,
// not proof: a relation can agree with a genuine modular-form identity to
// any finite q-expansion truncation without being one. These tests confirm
// the certification actually distinguishes a true identity from a false one
// at the same precision, not just that a working pipeline still works.
//
// Uses small real levels (N=137 genus 4 non-hyperelliptic, N=136 genus 3
// hyperelliptic) so the identities under test are genuine modular-form
// relations, not synthetic data; both build in well under a second.
//
// Run with: tests/run.sh test_sturm_certification

load "src/triple_covers.m";   // LoadStarForms, CanonicalModelFromForms; also loads src/AtkinLehner.m
load "tests/assertions.m";

results := NewResults();

// -------------------------------------------------------------------------
// 1-3: non-hyperelliptic canonical case (N=137, genus 4).
// -------------------------------------------------------------------------

N137 := 137;
X137, fs137, Sstar137 := XZeroNstarWithForms(N137, 30);
g137 := Genus(X137);
AssertEqual(~results, g137, 4,
    "N=137: XZeroNstarWithForms succeeds and returns genus 4");

eqns137 := DefiningPolynomials(X137);
e1 := eqns137[1];
d1 := Degree(e1);
w1 := 2*d1;
B1 := ModularSturmBound(N137, w1);

// (1) A genuine defining equation certifies past its own Sturm bound.
bas137 := [qExpansion(f, B1 + 25) : f in Sstar137];
val_true := Evaluate(e1, bas137);
ok_true, B_check := CertifyModularIdentity(val_true, N137, w1);
AssertEqual(~results, ok_true and B_check eq B1, true,
    Sprintf("N=137: genuine defining equation (deg %o) certifies past Sturm bound %o", d1, B1));

// (2) The same equation with one coefficient perturbed must not certify at
// the same precision, otherwise the check is a no-op.
mons1 := Monomials(e1);
cffs1 := Coefficients(e1);
cffs1[1] +:= 1;   // perturb the leading coefficient
e1_bad := &+[cffs1[i]*mons1[i] : i in [1..#mons1]];
val_bad := Evaluate(e1_bad, bas137);
ok_bad, _ := CertifyModularIdentity(val_bad, N137, w1);
AssertEqual(~results, not ok_bad, true,
    "N=137: a perturbed (false) equation is correctly REJECTED at the same precision that certifies the true one");

// (3) Insufficient precision must error, not silently under-certify.
short_val := val_true + O(Parent(val_true).1 ^ (B1 - 1));
caught := false;
try
    _ := CertifyModularIdentity(short_val, N137, w1);
catch e
    caught := true;
end try;
AssertEqual(~results, caught, true,
    "N=137: CertifyModularIdentity errors (does not silently pass) when given insufficient precision");

// -------------------------------------------------------------------------
// 4: hyperelliptic cleared identity (N=136, genus 3).
// -------------------------------------------------------------------------

N136 := 136;
assert IsHyperellipticX0Nstar(N136);
C136, fs136, Sstar136 := XZeroNstarWithForms_hyperelliptic(N136, 30);
g136 := GenusStarQuotient(N136);
AssertEqual(~results, Genus(C136) eq g136 and Degree(HyperellipticPolynomials(C136)) eq 2*g136 + 2, true,
    Sprintf("N=136: XZeroNstarWithForms_hyperelliptic succeeds, genus=%o, deg(P)=2g+2", g136));

// Independently rebuild the cleared identity from the returned model and
// confirm it certifies, then confirm a perturbed P does not.
weight136 := 4*g136 + 4;
B136 := ModularSturmBound(N136, weight136);
cert_prec136 := B136 + 25;

M_hyp := Matrix([AbsEltseq(qExpansion(f, cert_prec136) : FixedLength) : f in Sstar136]);
_, T_hyp := EchelonForm(M_hyp);
diag_sstar136 := [&+[T_hyp[i][j]*Sstar136[j] : j in [1..g136]] : i in [1..g136]];
fg1c := qExpansion(diag_sstar136[g136 - 1], cert_prec136);
fgc  := qExpansion(diag_sstar136[g136],     cert_prec136);
Rc := Parent(fg1c); qc := Rc.1;
Wc := qc*Derivative(fg1c)*fgc - fg1c*qc*Derivative(fgc);

P := HyperellipticPolynomials(C136);
Pcoeffs := Coefficients(P);   // low-to-high degree, length deg(P)+1
deg136 := 2*g136 + 2;
Pcoeffs_full := Pcoeffs cat [0 : i in [#Pcoeffs+1..deg136+1]];

LHS136 := Wc^2 * fgc^(2*g136 - 4);
RHS136 := &+[Pcoeffs_full[k+1] * fg1c^k * fgc^(deg136-k) : k in [0..deg136]];
ok136, _ := CertifyModularIdentity(LHS136 - RHS136, N136, weight136);
AssertEqual(~results, ok136, true,
    "N=136: cleared hyperelliptic identity (from the actual returned model) certifies past its Sturm bound");

Pcoeffs_bad := Pcoeffs_full;
Pcoeffs_bad[1] +:= 1;   // perturb the constant term of P
RHS136_bad := &+[Pcoeffs_bad[k+1] * fg1c^k * fgc^(deg136-k) : k in [0..deg136]];
ok136_bad, _ := CertifyModularIdentity(LHS136 - RHS136_bad, N136, weight136);
AssertEqual(~results, not ok136_bad, true,
    "N=136: a perturbed P is correctly REJECTED by the cleared-identity check");

// -------------------------------------------------------------------------
// 5: cached-forms builder path (N=237, genus 5, has a starforms_237.m cache
// entry, exercises CanonicalModelFromForms/CertifyEquationsAgainstCache
// without any all_diag_basis call).
// -------------------------------------------------------------------------

ok_cache, prec_cache, fs_full_237 := LoadStarForms(237);
if ok_cache then
    X237 := CanonicalModelFromForms(fs_full_237, 237);
    AssertEqual(~results, Genus(X237), 5,
        "N=237: CanonicalModelFromForms (cache-only, no all_diag_basis) certifies and returns genus 5");

    // Truncate the cache to force an insufficient-precision error.
    short_prec := 50;
    fs_short := [f + O(Parent(f).1^short_prec) : f in fs_full_237];
    caught_cache := false;
    try
        _ := CanonicalModelFromForms(fs_short, 237);
    catch e
        caught_cache := true;
    end try;
    AssertEqual(~results, caught_cache, true,
        "N=237: CanonicalModelFromForms errors (does not silently under-certify) when the cache is truncated to 50 terms");
else
    printf "SKIP: N=237 has no starforms_237.m cache entry in this checkout, skipping cached-builder tests\n";
end if;

// -------------------------------------------------------------------------
// 6: PointsOriginalModel no longer requires a square coefficient
// denominator (src/point_search.m). LCM(1/2, 1/3) = 6 is not a square, so
// the pre-fix `assert ok where ok,s := IsSquare(den)` would abort here.
// -------------------------------------------------------------------------

Qx<xind> := PolynomialRing(Rationals());
f_nonsquare := xind^6 + 1/2*xind^3 + 1/3;
C_nonsquare := HyperellipticCurve(f_nonsquare);
pts_nonsquare := PointsOriginalModel(C_nonsquare, 20);
AssertEqual(~results, forall{P : P in pts_nonsquare | P in C_nonsquare}, true,
    Sprintf("PointsOriginalModel: non-square-denominator model (den=6) no longer aborts, and all %o returned points verify on the curve", #pts_nonsquare));

Report(~results, "test_sturm_certification");
