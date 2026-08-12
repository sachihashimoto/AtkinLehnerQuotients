// tests/test_cm_points.m
// Unit tests for the exact CM point construction in src/cm_points.m.
// Run: /Applications/Magma/tests/run.sh test_cm_points
//
// Expected counts are derived from NumberOfOptimalEmbeddings, never
// hand-written: the previous test file hand-wrote them and 3 of 8 were wrong.

load "src/cm_points.m";
load "tests/assertions.m";

results := NewResults();

CC := ComplexField(200);

// Levels and discriminants spanning both regimes.  The last four have
// gcd(N, conductor) > 1, which is the regime v2 got wrong.
cases := [
    <178, -388>, <154, -1848>, <154, -1540>, <137, -32>,
    <310, -55>,  <329, -52>,   <455, -819>,
    <399, -147>, <399, -27>,   <178, -16>,   <510, -36>
];

printf "\n=== Count matches NumberOfOptimalEmbeddings ===\n";
for c in cases do
    N := c[1]; D := c[2];
    R := QuadraticOrder(BinaryQuadraticForms(D));
    embs := OptimalEmbeddingMatrices(D, N);
    expected := NumberOfOptimalEmbeddings(R, N);
    AssertEqual(~results, #embs, expected,
        Sprintf("N=%o D=%o: #embs matches Ogg count", N, D));
end for;

// Note: every check in this block is already asserted internally inside
// OptimalEmbeddingMatrices (trace/det match, N | M[2,1]) or inside
// IsOptimalEmbeddingMatrix itself before returning, so this block can only
// ever observe true, it is a duplicate of those internal asserts, not an
// independent check. Kept for readability / documentation of the invariant;
// see "Imprimitive fixed-point form does not imply non-optimal" below for
// the actual independent tests of optimality.
printf "\n=== Every matrix is an optimal embedding ===\n";
for c in cases do
    N := c[1]; D := c[2];
    R := QuadraticOrder(BinaryQuadraticForms(D));
    tr := Integers()!Trace(R.2); nm := Integers()!Norm(R.2);
    ok := true;
    for M in OptimalEmbeddingMatrices(D, N) do
        if not IsOptimalEmbeddingMatrix(M, N) then ok := false; end if;
        if Trace(M) ne tr or Determinant(M) ne nm then ok := false; end if;
        if M[2,1] mod N ne 0 then ok := false; end if;
    end for;
    AssertEqual(~results, ok, true,
        Sprintf("N=%o D=%o: all matrices optimal, right trace/det, N | M[2,1]", N, D));
end for;

printf "\n=== Imprimitive fixed-point form does not imply non-optimal ===\n";
// This is the headline claim the whole rework rests on. Optimality in
// O_0(N) is gcd(b, c, a-d) = 1 for M = [a b; N*c d] (IsOptimalEmbeddingMatrix,
// src/cm_points.m). The CM-fixed-point form is <A,B,C> = <-M[2,1], M[1,1]-M[2,2],
// M[1,2]> (sign-normalised so A > 0); its content is gcd(N*c, d-a, b). These
// two contents differ by exactly the factor of N pulled out of A, so a
// form with content > 1 need not correspond to a non-optimal embedding.
//
// N=399, D=-147: End(E) = O_{-3}, End(E') = O_{-147} (conductor 7), and
// N=399=3*7*19 shares the prime 7 with that conductor. The embedding below
// has fixed-point form content 7 (imprimitive) but is still optimal.
N399 := 399; D147 := -147;
found_imprimitive_optimal := false;
for M in OptimalEmbeddingMatrices(D147, N399) do
    A := -M[2,1]; B := M[1,1]-M[2,2]; C := M[1,2];
    if A lt 0 then A := -A; B := -B; C := -C; end if;
    if GCD([A,B,C]) eq 7 and IsOptimalEmbeddingMatrix(M, N399) then
        found_imprimitive_optimal := true;
    end if;
end for;
AssertEqual(~results, found_imprimitive_optimal, true,
    "N=399 D=-147: an embedding with imprimitive (content-7) fixed-point form is still optimal");

// Negative case: a matrix genuinely violating gcd(b,c,a-d) = 1, verified by
// hand. N=399, M = [4 2; 798 0]: M[2,1]=798=2*399 so N | M[2,1] and
// c = M[2,1] div N = 2; b = M[1,2] = 2; a-d = 4-0 = 4. gcd(b,c,a-d) =
// gcd(2,2,4) = 2 =/= 1, so this is not an optimal embedding (it need not
// correspond to any actual CM order, this only exercises the gcd-content
// logic of IsOptimalEmbeddingMatrix directly).
M_nonopt := Matrix(Integers(), 2, 2, [4, 2, 798, 0]);
AssertEqual(~results, not IsOptimalEmbeddingMatrix(M_nonopt, N399), true,
    "N=399: M=[4 2; 798 0] has gcd(b,c,a-d)=2, correctly flagged non-optimal");

printf "\n=== taus: upper half plane, descending Im (NON-strict) ===\n";
for c in cases do
    N := c[1]; D := c[2];
    taus := CMTaus(D, N, CC);
    AssertEqual(~results, #taus gt 0 and &and[Imaginary(t) gt 0 : t in taus], true,
        Sprintf("N=%o D=%o: %o taus, all in the upper half plane", N, D, #taus));
    // Non-strict: ties are normal (N=399 D=-147 has two embeddings at A=399).
    AssertEqual(~results,
        &and[Imaginary(taus[i]) ge Imaginary(taus[i+1]) : i in [1..#taus-1]], true,
        Sprintf("N=%o D=%o: taus ordered by descending Im (non-strict)", N, D));
    AssertEqual(~results, #taus, #OptimalEmbeddingMatrices(D, N),
        Sprintf("N=%o D=%o: one tau per embedding, none dropped", N, D));
end for;

printf "\n=== Local obstruction returns [], does not error ===\n";
// 2 is inert in Q(sqrt(-3)), so there is no embedding at N=178.
AssertEqual(~results, #OptimalEmbeddingMatrices(-3, 178), 0,
    "N=178 D=-3: OptimalEmbeddingMatrices returns empty");
AssertEqual(~results, #CMTaus(-3, 178, CC), 0,
    "N=178 D=-3: CMTaus returns empty");

printf "\n=== Non-squarefree level raises a clear error ===\n";
raised := false;
try
    _ := CMTaus(-4, 12, CC);
catch e
    raised := true;
end try;
AssertEqual(~results, raised, true,
    "N=12 (not squarefree): CMTaus raises rather than returning []");

printf "\n=== Regression: the null-universe bug (7 of 16 conductor cases) ===\n";
// extra_p := {} is a null-universe set; appending it fixes local_extra_roots'
// universe to null and a later {3} cannot coerce in.  Fires only when one prime
// of N has an extra AL branch and another does not.
for c in [<246,-72>, <246,-36>, <290,-100>, <318,-36>, <510,-36>, <370,-100>, <399,-147>] do
    N := c[1]; D := c[2];
    ok := true;
    try
        _ := CMTaus(D, N, CC);
    catch e
        ok := false;
    end try;
    AssertEqual(~results, ok, true,
        Sprintf("N=%o D=%o: no null-universe Append failure", N, D));
end for;

Report(~results, "test_cm_points");
