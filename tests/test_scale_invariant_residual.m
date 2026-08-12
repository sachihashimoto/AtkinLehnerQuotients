// tests/test_scale_invariant_residual.m
// Direct unit test for ScaleInvariantResidual (src/labelling.m): fast, no
// model-building or CM machinery, pure arithmetic on hand-built vectors.
// Run with: tests/run.sh test_scale_invariant_residual

load "src/AtkinLehner.m";
load "tests/assertions.m";

results := NewResults();

// --- Arrange ---
CC := ComplexField(50);

// --- Act / Assert: exactly orthogonal vectors give a near-zero residual ---
vi1 := [1, 1];
ev1 := [CC!1, CC!(-1)];
r1  := ScaleInvariantResidual(vi1, ev1);
AssertEqual(~results, Abs(r1) lt 10^-40, true,
    Sprintf("orthogonal vi=[1,1] ev=[1,-1]: |residual| < 1e-40 (got %o)", r1));

// --- Act / Assert: known value, vi=[1,0], ev=[1,1] -> |1|/(1*sqrt(2)) ---
vi2 := [1, 0];
ev2 := [CC!1, CC!1];
r2  := ScaleInvariantResidual(vi2, ev2);
expected2 := 1/Sqrt(RealField(CC)!2);
AssertEqual(~results, Abs(r2 - expected2) lt 10^-10, true,
    Sprintf("vi=[1,0] ev=[1,1]: residual = 1/sqrt(2) (got %o, expected %o)",
        r2, expected2));

// --- Act / Assert: rescaling ev by a nonzero complex scalar changes nothing.
// This is the whole point of the scale-invariant check over a bare
// |vi . ev| tolerance. ---
vi3        := [3, -2, 1];
ev3        := [CC!1, CC!2, CC!(-1)];
scale      := CC!5 * Exp(CC.1 * Pi(CC)/7);  // nonzero, nontrivial phase
ev3_scaled := [scale*e : e in ev3];
r3a := ScaleInvariantResidual(vi3, ev3);
r3b := ScaleInvariantResidual(vi3, ev3_scaled);
AssertEqual(~results, Abs(r3a - r3b) lt 10^-10, true,
    Sprintf("vi=[3,-2,1]: residual invariant under rescaling ev (got %o vs %o)",
        r3a, r3b));

Report(~results, "test_scale_invariant_residual");
