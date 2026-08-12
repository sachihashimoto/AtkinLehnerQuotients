// tests/test_cm_containment.m
// Containment check: every form HeegnerForms returns is Gamma_0(N)-equivalent
// to the fixed-point form of some new embedding, restricted to the primitive subset.
//
// SL2(Z)-equivalence is not acceptable here.  SL2(Z) is strictly larger than
// Gamma_0(N) and identifies distinct points of X_0(N).  Concretely,
// <178,18,1> and <178,-18,1> are SL2(Z)-equivalent via [1,0;-18,1], whose
// lower-left entry -18 is not divisible by 178.
//
// Measured 2026-08-01: 243 of 243 forms contained, 0 misses.
// Run: /Applications/Magma/tests/run.sh test_cm_containment
//
// Note: this test's output is not pristine by design. RationalCMDiscs (in
// src/fields_of_definition.m) prints one unconditional "found CM point at discriminant
// ..." line per discriminant it finds, with no verbosity gate. This test
// calls RationalCMDiscs once per level across 14 levels, so the real
// transcript carries roughly 99 interleaved "found CM point at discriminant"
// lines ahead of the PASS/FAIL lines. That noise is pre-existing production
// behaviour in src/fields_of_definition.m, not a symptom of anything in this test;
// do not "fix" it by silencing the production print, and do not read its
// presence as a regression.

load "src/AtkinLehner.m";
load "tests/assertions.m";

results := NewResults();

levels := [178,183,246,290,310,318,329,430,455,510,137,311,370,399];

printf "\n=== Gamma_0(N)-containment of HeegnerForms in the new set ===\n";
total := 0; missed := 0;
for N in levels do
    for D in Sort(Setseq(Keys(RationalCMDiscs(N)))) do
        QF := BinaryQuadraticForms(D);
        // Primitive subset only: HeegnerForms returns only primitive forms, and
        // the imprimitive members of the new set are additional points, not
        // replacements.
        ours := [];
        for M in OptimalEmbeddingMatrices(D, N) do
            t := FixedPointForm(M);
            if GCD(t) eq 1 then Append(~ours, t); end if;
        end for;
        for t in HeegnerForms(N, D) do
            total +:= 1;
            f := [Integers() | t[1], t[2], t[3]];
            if not exists{g : g in ours | IsGamma0Equivalent(f, g, N)} then
                missed +:= 1;
                printf "  NOT CONTAINED: N=%o D=%o form=%o\n", N, D, t;
            end if;
        end for;
    end for;
end for;

AssertEqual(~results, missed, 0,
    Sprintf("all %o HeegnerForms forms Gamma_0(N)-contained", total));
AssertEqual(~results, total, 243,
    "checked 243 forms across the 99 production pairs");

printf "\n=== The SL2(Z) proxy really is too permissive ===\n";
// Guard against anyone "simplifying" IsGamma0Equivalent into IsEquivalent.
Q388 := BinaryQuadraticForms(-388);
eqv, Mbad := IsEquivalent(Q388![178,18,1], Q388![178,-18,1]);
AssertEqual(~results, eqv and Mbad[2,1] mod 178 ne 0, true,
    "SL2(Z) identifies <178,18,1> ~ <178,-18,1> via a matrix outside Gamma_0(178)");

Report(~results, "test_cm_containment");
