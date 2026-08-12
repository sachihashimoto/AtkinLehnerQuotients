// test_286_class8_coverage.m
// Checks that RationalCMDiscs(286) does not miss any class-8 fundamental
// discriminant with N_R_primes={} that has a degree-1 field of definition.
// This guards against the f_cond=1 filter regression fixed in src/fields_of_definition.m.
//
// Run with: tests/run.sh test_286_class8_coverage

load "src/AtkinLehner.m";
load "tests/assertions.m";

results := NewResults();

printf "\n=== RationalCMDiscs class-8 coverage test for N=286 (2*11*13) ===\n";

N286 := 2*11*13;
cm286 := RationalCMDiscs(N286);
printf "RationalCMDiscs(286) returned %o disc(s): %o\n", #cm286, Sort([d : d in Keys(cm286)]);

CNs286 := CMClassLists();
missed286 := [];
rc_cache286 := AssociativeArray();
ncandidates := 0;
n_nonfund := 0;   // dropped: conductor != 1
n_fund    := 0;   // survived the conductor filter
n_split   := 0;   // dropped: some p | N is split
n_noemb   := 0;   // dropped: no optimal embedding into the level-N Eichler order
for d in CNs286[8] do
    disc := -d;
    R := QuadraticOrder(BinaryQuadraticForms(disc));
    if Conductor(R) ne 1 then n_nonfund +:= 1; continue; end if;
    n_fund +:= 1;
    N_R := {p : p in PrimeDivisors(N286) | KroneckerCharacter(disc)(p) eq 1};
    if #N_R ne 0 then n_split +:= 1; continue; end if;
    if NumberOfOptimalEmbeddings(R, N286) eq 0 then n_noemb +:= 1; continue; end if;
    ncandidates +:= 1;
    flds, rc_cache286 := FieldsOfDefinitionOfCMPoint(N286, disc : rc_cache := rc_cache286);
    degs := [Degree(F) : F in flds];
    if 1 in degs then
        printf "  D=%o: degree-1 field found\n", disc;
        if disc notin Keys(cm286) then
            printf "  -> MISSED by RationalCMDiscs!\n";
            Append(~missed286, disc);
        else
            printf "  -> present in RationalCMDiscs (ok)\n";
        end if;
    end if;
end for;
printf "Candidates checked (f_cond=1, N_R_primes={}, opt_emb>0): %o\n", ncandidates;

// ---------------------------------------------------------------------------
// Characterisation of the filter pipeline.
//
// Important: ncandidates is 0 at N=286, and that is mathematically correct, not a
// breakage.  Of the 21 class-8 entries in CMClassLists(), 8 are non-fundamental,
// and of the 13 fundamental ones 2 have a split prime and the remaining 11 admit
// no optimal embedding into the level-286 Eichler order.  Nothing survives, so the
// "no disc was missed" assertion below has nothing to range over and passes
// trivially, it has done so since this test was written.
//
// That makes the headline assertion alone worthless as a regression guard: it would
// keep reporting PASS if CMClassLists() lost its class-8 entry outright, or if
// NumberOfOptimalEmbeddings began returning 0 everywhere.  The "Candidates checked"
// line above is printed for a reader, not asserted, so on its own it would not
// reveal the collapse either.
//
// So pin the stage counts instead.  These make the test earn its runtime: any drift
// in CMClassLists, the conductor filter, the split-prime filter, or the optimal
// embedding count moves one of these numbers and fails loudly.
// ---------------------------------------------------------------------------
AssertEqual(~results, #CNs286[8], 21,
    "N=286: CMClassLists() has 21 class-8 discriminants");
AssertEqual(~results, n_fund eq 13 and n_nonfund eq 8, true,
    Sprintf("N=286: 13 of the 21 class-8 discs are fundamental, 8 are not (got %o and %o)",
        n_fund, n_nonfund));
AssertEqual(~results, n_split, 2,
    "N=286: 2 fundamental class-8 discs have a split prime dividing N");
AssertEqual(~results, n_noemb, 11,
    "N=286: 11 fundamental class-8 discs with no split prime admit no optimal embedding");
AssertEqual(~results, ncandidates eq 0 and n_split + n_noemb eq n_fund, true,
    Sprintf("N=286: the class-8 filter selects %o candidates, and 2+11 accounts for all 13 fundamental discs",
        ncandidates));

AssertEqual(~results, #missed286, 0,
    Sprintf("N=286: no class-8 fundamental disc with N_R_primes={} missed by RationalCMDiscs  (missed: %o)",
        missed286));

Report(~results, "test_286_class8_coverage");
