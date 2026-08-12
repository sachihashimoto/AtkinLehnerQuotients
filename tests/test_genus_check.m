// tests/test_genus_check.m
// GenusStarQuotient and IsHyperellipticX0Nstar on the higher-genus
// hyperelliptic special cases, plus three levels from the genus-2 list.
// Run with: tests/run.sh test_genus_check

load "src/AtkinLehner.m";
load "tests/assertions.m";

results := NewResults();

// --- Arrange ---
// <N, expected genus, expected IsHyperelliptic>. The first seven are the
// higher-genus hyperelliptic special cases; the last three come from the
// genus-2 list.
cases := [
    <136, 3, true>,
    <171, 3, true>,
    <176, 4, true>,
    <207, 3, true>,
    <252, 3, true>,
    <279, 5, true>,
    <315, 3, true>,
    < 67, 2, true>,
    < 73, 2, true>,
    < 85, 2, true>
];

for c in cases do
    N := c[1];

    // --- Act / Assert ---
    AssertEqual(~results, GenusStarQuotient(N), c[2],
        Sprintf("N=%o: GenusStarQuotient", N));
    AssertEqual(~results, IsHyperellipticX0Nstar(N), c[3],
        Sprintf("N=%o: IsHyperellipticX0Nstar", N));
end for;

Report(~results, "test_genus_check");
