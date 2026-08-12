// tests/test_projective_residual.m
// Direct unit test for ProjectiveResidual (src/labelling.m): fast, no
// model-building or CM machinery, pure arithmetic on hand-built vectors.
//
// Regression test for the catastrophic-cancellation fix: the old formula
// (Sqrt(1-cos_theta^2)) needs cos_theta computed to roughly twice as many
// digits as the true residual, so at 200-digit working precision it silently
// rounds residuals smaller than ~10^-100 to 0. The exterior-product formula
// resolves residuals down to the working precision itself.
//
// Run with: tests/run.sh test_projective_residual

load "src/AtkinLehner.m";
load "tests/assertions.m";

results := NewResults();

CC := ComplexField(200);

// The old formula, kept only here as a comparison baseline to demonstrate
// the precision loss the fix addresses, not used anywhere in src/.
function OldProjectiveResidual(p, q)
    g := #p;
    inner := &+[p[l]*Conjugate(q[l]) : l in [1..g]];
    np := Sqrt(&+[Abs(p[l])^2 : l in [1..g]]);
    nq := Sqrt(&+[Abs(q[l])^2 : l in [1..g]]);
    if np eq 0 or nq eq 0 then return 1; end if;
    cos_theta := Abs(inner) / (np*nq);
    if cos_theta gt 1 then cos_theta := Parent(cos_theta)!1; end if;
    return Sqrt(Maximum(0, 1 - cos_theta^2));
end function;

// -------------------------------------------------------------------------
// p=(1,0), q=(1,delta): the true residual sin(theta) = delta/Sqrt(1+delta^2)
// is computable exactly (no near-1 cancellation in this formula, since it
// never subtracts two nearly-equal quantities), so it's a clean reference
// value across a wide range of delta.
// -------------------------------------------------------------------------
deltas := [10^-20, 10^-50, 10^-80, 10^-100, 10^-150, 10^-190];

for delta in deltas do
    d := CC!delta;
    p := [CC!1, CC!0];
    q := [CC!1, d];
    expected := d / Sqrt(1 + d^2);

    r_new := ProjectiveResidual(p, q);
    AssertEqual(~results, Abs(r_new - expected) lt Abs(expected)*10^-30, true,
        Sprintf("ProjectiveResidual resolves delta=%o (got %o, expected ~%o)", delta, r_new, expected));
end for;

// Characterization check on the old formula (not on current code): it
// should visibly fail to resolve a residual this small at 200-digit
// precision, which is exactly why the fix was needed.
delta_small := CC!(10^-150);
p_old := [CC!1, CC!0];
q_old := [CC!1, delta_small];
r_old := OldProjectiveResidual(p_old, q_old);
AssertEqual(~results, Abs(r_old) lt 10^-190 or Abs(r_old - delta_small) gt Abs(delta_small)*0.5, true,
    Sprintf("(characterization) old Sqrt(1-cos^2) formula loses delta=10^-150 at 200-digit precision (got %o)", r_old));

// -------------------------------------------------------------------------
// Known-value and scale-invariance checks, in the style of
// tests/test_scale_invariant_residual.m.
// -------------------------------------------------------------------------
p0 := [CC!1, CC!0];
q0 := [CC!0, CC!1];
r0 := ProjectiveResidual(p0, q0);
AssertEqual(~results, Abs(r0 - 1) lt 10^-40, true,
    Sprintf("orthogonal unit vectors give residual 1 (got %o)", r0));

p1 := [CC!1, CC!1];
r1 := ProjectiveResidual(p1, p1);
AssertEqual(~results, Abs(r1) lt 10^-40, true,
    Sprintf("a vector against itself gives near-zero residual (got %o)", r1));

p2 := [CC!3, CC!(-2), CC!1];
scale := CC!5 * Exp(CC.1 * Pi(CC)/7);   // nonzero complex scalar, nontrivial phase
p2_scaled := [scale*x : x in p2];
q2 := [CC!1, CC!2, CC!(-1)];
r2a := ProjectiveResidual(p2, q2);
r2b := ProjectiveResidual(p2_scaled, q2);
AssertEqual(~results, Abs(r2a - r2b) lt 10^-40, true,
    Sprintf("residual is scale-invariant under rescaling p  (got %o vs %o)", r2a, r2b));

Report(~results, "test_projective_residual");
