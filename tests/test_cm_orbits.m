// tests/test_cm_orbits.m
// Gamma_0(N)*-orbits of the optimal-embedding taus.
//
// Design: docs/handoff/CM-TAU-orbits-design.md
// Run from the repo root: /Applications/Magma/tests/run.sh test_cm_orbits
//
// Note: this test's output is not pristine by design.  RationalCMDiscs prints
// one unconditional "found CM point at discriminant ..." line per discriminant,
// with no verbosity gate.  That noise is pre-existing production behaviour in
// src/fields_of_definition.m, do not silence it and do not read it as a regression.

load "src/AtkinLehner.m";
load "tests/assertions.m";

results := NewResults();

printf "\n=== FixedPointForm ===\n";

// M = [53, 7; -399, -52] at N=399, D=-147: the imprimitive-yet-optimal case.
// Fixed-point form <399,105,7> has content 7 and primitive part <57,15,1>.
M399 := Matrix(Integers(),2,2,[53,7,-399,-52]);
f399 := FixedPointForm(M399);
AssertEqual(~results, f399, [399,105,7],
    "FixedPointForm([53,7;-399,-52]) = [399,105,7]");
AssertEqual(~results, f399[2]^2 - 4*f399[1]*f399[3], -147,
    "FixedPointForm preserves the discriminant");

printf "\n=== AutForm orders ===\n";

AssertEqual(~results, #AutForm([1,1,1], -3), 6,
    "Aut of a D=-3 form has order 6");
AssertEqual(~results, #AutForm([1,0,1], -4), 4,
    "Aut of a D=-4 form has order 4");
AssertEqual(~results, #AutForm([1,1,2], -7), 2,
    "Aut of a D=-7 form has order 2");

printf "\n=== IsGamma0Equivalent is Gamma_0(N), not SL2(Z) ===\n";

// The canonical counterexample.  SL2(Z) identifies <178,18,1> with <178,-18,1>
// via [1,0;-18,1], whose lower-left entry -18 is not divisible by 178, so they
// are distinct points of X_0(178).
Q388 := BinaryQuadraticForms(-388);
sl2_says, Mbad := IsEquivalent(Q388![178,18,1], Q388![178,-18,1]);
AssertEqual(~results, sl2_says and Mbad[2,1] mod 178 ne 0, true,
    "SL2(Z) does identify <178,18,1> ~ <178,-18,1>, outside Gamma_0(178)");
AssertEqual(~results, not IsGamma0Equivalent([178,18,1], [178,-18,1], 178), true,
    "IsGamma0Equivalent separates <178,18,1> from <178,-18,1> at N=178");

AssertEqual(~results, IsGamma0Equivalent([178,18,1], [178,18,1], 178), true,
    "IsGamma0Equivalent is reflexive");

// Content is a Gamma_0(N)-invariant, so an imprimitive form is never
// equivalent to a primitive one.
AssertEqual(~results, not IsGamma0Equivalent([399,105,7], [57,15,1], 399), true,
    "content 7 form is not Gamma_0(399)-equivalent to its primitive part");

// ... and the imprimitive case is handled rather than erroring.
AssertEqual(~results, IsGamma0Equivalent([399,105,7], [399,105,7], 399), true,
    "IsGamma0Equivalent accepts imprimitive forms (content 7 at N=399)");

printf "\n=== CMTauOrbits: structure ===\n";

CC := ComplexField(200);   // TauFromEmbedding's fixed-point assert needs ~50 digits

// N=399, D=-147: eight embeddings, one orbit, and the orbit contains the
// imprimitive-fixed-point-form members that HeegnerForms cannot reach.
orbs399 := CMTauOrbits(-147, 399, CC);
AssertEqual(~results, #orbs399, 1,
    "N=399 D=-147: 1 orbit");
AssertEqual(~results, &+[#o : o in orbs399], #OptimalEmbeddingMatrices(-147, 399),
    "N=399 D=-147: orbits partition the embedding set");
AssertEqual(~results,
    &and[&and[orbs399[k][i][1] le orbs399[k][i+1][1] : i in [1..#orbs399[k]-1]]
         : k in [1..#orbs399]],
    true,
    "N=399 D=-147: each orbit is sorted by ascending A");

// N=178, D=-4: exercises the order-4 AutForm branch.
orbs178 := CMTauOrbits(-4, 178, CC);
AssertEqual(~results, #orbs178, 1,
    "N=178 D=-4: 1 orbit");

printf "\n=== CMTauOrbits: no optimal embedding ===\n";

// Find a discriminant with a local obstruction at N=178 rather than hard-coding
// one, so the test cannot rot against a changed convention.
Dnone := 0;
for D in [-3..-200 by -1] do
    if not IsDiscriminant(D) then continue; end if;
    if #OptimalEmbeddingMatrices(D, 178) eq 0 then Dnone := D; break; end if;
end for;
AssertEqual(~results, Dnone ne 0, true,
    Sprintf("found a discriminant with no optimal embedding at N=178  (got %o)", Dnone));
if Dnone ne 0 then
    AssertEqual(~results, CMTauOrbits(Dnone, 178, CC), [],
        Sprintf("N=178 D=%o: CMTauOrbits returns [] rather than erroring", Dnone));
    AssertEqual(~results, CMTauReps(Dnone, 178, CC), [],
        Sprintf("N=178 D=%o: CMTauReps returns []", Dnone));
end if;

printf "\n=== CMTauReps: one min-A representative per orbit ===\n";

reps399 := CMTauReps(-147, 399, CC);
AssertEqual(~results, #reps399, #orbs399,
    "N=399 D=-147: #reps = #orbits");

// Each representative is its own orbit's minimum A.  Nothing here compares A
// across orbits, a disc-wide minimum would return a tau for a different point.
AssertEqual(~results,
    &and[orbs399[k][1][1] eq Min([t[1] : t in orbs399[k]]) : k in [1..#orbs399]],
    true,
    "N=399 D=-147: orbit[1] attains the minimum A within its own orbit");

// Representatives are a subset of the raw CMTaus list.
taus399 := CMTaus(-147, 399, CC);
AssertEqual(~results,
    &and[exists{t : t in taus399 | Abs(t - r) lt 10^-40} : r in reps399],
    true,
    "N=399 D=-147: every representative appears in CMTaus");

printf "\n=== #orbits == DegreeOfFieldOfDefinitionOfCMPoint ===\n";

// Part A: the 14 production levels, over their rational CM discriminants.
levels := [178,183,246,290,310,318,329,430,455,510,137,311,370,399];

CCq := ComplexField(200);
npairs := 0; nbad := 0;

for N in levels do
    for D in Sort(Setseq(Keys(RationalCMDiscs(N)))) do
        orbs := CMTauOrbits(D, N, CCq);
        if #orbs eq 0 then continue; end if;
        npairs +:= 1;

        // Note the argument order: the level comes first here.
        deg   := DegreeOfFieldOfDefinitionOfCMPoint(N, D);
        sizes := {#o : o in orbs};

        // deg = 0 is the function's "no such point" sentinel.  #orbs >= 1 here,
        // so a 0 fails this check loudly, which is the intent.
        ok := (#orbs eq deg) and (#sizes eq 1);
        if not ok then
            nbad +:= 1;
            printf "  MISMATCH N=%o D=%o: #orbits=%o deg=%o sizes=%o\n",
                   N, D, #orbs, deg, sizes;
        end if;
    end for;
end for;

AssertEqual(~results, nbad, 0,
    Sprintf("part A: %o production pairs, no mismatches", npairs));
AssertEqual(~results, npairs, 99,
    "part A covered the 99 production pairs");

// Part B: a sweep including degree > 1 discriminants, which part A's rational
// discs do not reach.  Bounded at 48 embeddings: the singleton check below is
// O(n^2) and DegreeOfFieldOfDefinitionOfCMPoint builds a PicardGroup, so an
// unbounded sweep over high class numbers would not terminate in test time.
printf "\n=== sweep including degree > 1 discriminants ===\n";

sweep_levels := [137,178,329,399];
nsweep := 0; nsweep_bad := 0; nskip := 0;

for N in sweep_levels do
    for D in [-3..-400 by -1] do
        if not IsDiscriminant(D) then continue; end if;
        embs := OptimalEmbeddingMatrices(D, N);
        if #embs eq 0 then continue; end if;
        if #embs gt 48 then nskip +:= 1; continue; end if;

        orbs := CMTauOrbits(D, N, CCq);
        nsweep +:= 1;

        deg   := DegreeOfFieldOfDefinitionOfCMPoint(N, D);
        sizes := {#o : o in orbs};

        // Gamma_0(N)-classes are singletons: no two constructed matrices are
        // Gamma_0(N)-equivalent.  Every other claim in this design rests on
        // this, so assert it rather than assuming it.
        L := Setseq(embs);
        fs := [FixedPointForm(M) : M in L];
        singleton := not exists{<i,j> : i in [1..#L], j in [1..#L]
                                | i lt j and IsGamma0Equivalent(fs[i], fs[j], N)};

        ok := (#orbs eq deg) and (#sizes eq 1) and singleton;
        if not ok then
            nsweep_bad +:= 1;
            printf "  MISMATCH N=%o D=%o: #orbits=%o deg=%o sizes=%o singleton=%o\n",
                   N, D, #orbs, deg, sizes, singleton;
        end if;
    end for;
end for;

AssertEqual(~results, nsweep_bad, 0,
    Sprintf("sweep: %o pairs checked, no mismatches, %o skipped for #emb > 48",
            nsweep, nskip));
AssertEqual(~results, nsweep ge 200, true,
    Sprintf("sweep covered at least 200 pairs  (got %o)", nsweep));

// The gcd(N, conductor) > 1 cases, named explicitly so an imprimitive-form
// regression cannot pass silently.
printf "\n=== conductor cases ===\n";
for pair in [<399,-147>, <399,-12>, <399,-27>, <399,-48>, <178,-16>,
             <178,-36>, <178,-100>] do
    Nc := pair[1]; Dc := pair[2];
    orbs := CMTauOrbits(Dc, Nc, CCq);
    AssertEqual(~results,
        #orbs ge 1 and #orbs eq DegreeOfFieldOfDefinitionOfCMPoint(Nc, Dc), true,
        Sprintf("N=%o D=%o: #orbits = %o matches the degree", Nc, Dc, #orbs));
end for;

// The extra-automorphism discriminants, driving AutForm's order-6 and order-4
// branches through the full orbit computation rather than only through the
// unit tests in Task 1.
printf "\n=== extra-automorphism discriminants ===\n";
for pair in [<399,-3>, <178,-4>] do
    Nc := pair[1]; Dc := pair[2];
    orbs := CMTauOrbits(Dc, Nc, CCq);
    AssertEqual(~results,
        #orbs ge 1 and #orbs eq DegreeOfFieldOfDefinitionOfCMPoint(Nc, Dc), true,
        Sprintf("N=%o D=%o: #orbits = %o matches the degree", Nc, Dc, #orbs));
end for;

Report(~results, "test_cm_orbits");
