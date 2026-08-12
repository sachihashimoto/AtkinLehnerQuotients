// tests/test_triple_cover_table.m
//
// Pins the paper's triple-cover table against the computed classification.
//
// The claim being tested is not just "these triples are covers" but "these are
// the only ones", so the test re-derives the whole classification from scratch
//, the full sweep over the 667 branch-bound candidate levels, and asserts
// set equality in both directions.  A missing triple and a spurious extra one
// are separately reported.
//
// The expected list below is a transcription of Table "triple covers" in the
// paper.  If this test fails after a deliberate change to the mathematics, the
// table is what needs updating, not the assertion.
//
// The sweep comes from ClassifyTripleCovers (src/classify_covers.m), the same
// function scripts/classify_triple_covers.m formats.  Neither this test nor the
// script reimplements it, a test with its own copy of the sweep would only be
// testing itself.
//
// Run from the repo root with:
//   tests/run.sh test_triple_cover_table > /tmp/t.txt 2>&1; cat /tmp/t.txt
// Judge the result by counting PASS lines, not by the trailing banner;
// magma -b continues past undeclared-identifier errors, so a stale file can
// print "ALL TESTS PASSED" having executed zero assertions.
//
// Runtime: the full sweep, a few minutes.

load "src/AtkinLehner.m";
load "tests/assertions.m";
SetSeed(1);

results := NewResults();

// ---------------------------------------------------------------------------
// Table "triple covers": (N, d, E) with d the level of the associated newform
// and E = E^C_f the curve carrying the cover.  E differs from E_f exactly when
// c != 0, which happens only at N = d = 185, where E_f = 185c1.
// ---------------------------------------------------------------------------
expected := [
    <154, 77,  "77a1">,   <274, 274, "274c1">, <429, 143, "143a1">,
    <154, 154, "154a1">,  <282, 141, "141d1">, <430, 430, "430a1">,
    <163, 163, "163a1">,  <285, 57,  "57a1">,  <434, 434, "434a1">,
    <185, 185, "185c2">,  <285, 285, "285b1">, <438, 219, "219a1">,
    <201, 201, "201a1">,  <286, 143, "143a1">, <455, 91,  "91a1">,
    <202, 101, "101a1">,  <286, 286, "286c1">, <462, 77,  "77a1">,
    <214, 214, "214b1">,  <290, 58,  "58a1">,  <465, 155, "155c1">,
    <219, 219, "219a1">,  <291, 291, "291c1">, <570, 57,  "57a1">,
    <237, 79,  "79a1">,   <305, 61,  "61a1">,  <570, 190, "190b1">,
    <246, 123, "123b1">,  <310, 155, "155c1">, <574, 574, "574a1">,
    <249, 83,  "83a1">,   <318, 318, "318c1">, <590, 118, "118a1">,
    <254, 254, "254c1">,  <354, 118, "118a1">, <798, 57,  "57a1">,
    <258, 258, "258a1">,  <393, 131, "131a1">, <870, 58,  "58a1">,
    <262, 131, "131a1">,  <395, 79,  "79a1">,  <910, 91,  "91a1">,
    <262, 262, "262b1">,  <399, 57,  "57a1">,
    <267, 89,  "89a1">,   <402, 201, "201a1">,
    <269, 269, "269a1">,  <426, 142, "142b1">
];

printf "\n=== recomputing the classification (full sweep) ===\n";
t0 := Cputime();
rows := ClassifyTripleCovers(: verbose := true);
printf "sweep done (%o s)\n", Cputime(t0);

computed := {<r[2], r[3], r[4]> : r in rows};
wanted   := {t : t in expected};

// ---------------------------------------------------------------------------
printf "\n=== 1. the table is exactly the classification ===\n";
// ---------------------------------------------------------------------------
AssertEqual(~results, #expected, #wanted,
    "the table has no duplicate rows");
AssertEqual(~results, #rows, #computed,
    "the sweep produced no duplicate rows");

missing := wanted diff computed;
AssertEqual(~results, #missing, 0,
    Sprintf("every table entry is a computed cover (missing: %o)",
        #missing eq 0 select "none" else Sprint(Sort(Setseq(missing)))));

extra := computed diff wanted;
AssertEqual(~results, #extra, 0,
    Sprintf("the table omits no computed cover (extra: %o)",
        #extra eq 0 select "none" else Sprint(Sort(Setseq(extra)))));

AssertEqual(~results, computed, wanted,
    Sprintf("the table IS the complete list of triple covers (%o triples)", #wanted));

// ---------------------------------------------------------------------------
printf "\n=== 2. each row satisfies the degree formula ===\n";
// ---------------------------------------------------------------------------
// deg = delta_f * prod (l + 1 + a_l) = 3, checked row by row rather than taken
// on faith from the sweep that produced the rows.
allthree := true;
for r in rows do
    F := &*[Integers() | t[2] : t in r[8]];
    if r[7] * F ne 3 then
        allthree := false;
        printf "  row N=%o d=%o: delta=%o, factors=%o -> %o\n", r[2], r[3], r[7], r[8], r[7]*F;
    end if;
end for;
AssertEqual(~results, allthree, true,
    "every row satisfies 3 = delta_f * prod_{l | N/d} (l + 1 + a_l)");

// Every cover is of a curve of genus >= 2 star quotient (the theorem's
// hypothesis), a genus-1 X_0(N)* would make the map an isogeny, not a cover.
AssertEqual(~results, &and[r[1] ge 2 : r in rows], true,
    "every N has g(X_0(N)*) >= 2");

// ---------------------------------------------------------------------------
printf "\n=== 3. E^C_f differs from E_f only at 185 ===\n";
// ---------------------------------------------------------------------------
// The caption's claim: the label is that of E = E^C_f, which differs from E_f
// exactly when c != 0, and that happens only at N = d = 185.
twisted := {<r[2], r[3], r[4], r[5]> : r in rows | r[4] ne r[5]};
AssertEqual(~results,
    twisted, {<185, 185, "185c2", "185c1">},
    "E^C_f != E_f exactly at N = d = 185 (185c2 vs 185c1)");

AssertEqual(~results,
    &and[(r[6] eq 1) eq (r[4] eq r[5]) : r in rows], true,
    "|C| = 1 iff E^C_f = E_f, on every row");

AssertEqual(~results,
    {r[6] : r in rows | r[2] eq 185}, {2},
    "N = 185 has |C| = 2");

// ---------------------------------------------------------------------------
printf "\n=== 4. the committed output file agrees ===\n";
// ---------------------------------------------------------------------------
// Guards against data/triple_cover_classification.txt drifting from the
// code that generates it.
function IsIntegerString(s)
    if #s eq 0 then return false, 0; end if;
    for i in [1..#s] do
        if not s[i] in "0123456789" then return false, 0; end if;
    end for;
    return true, StringToInteger(s);
end function;

fromfile := {};
for line in Split(Read("data/triple_cover_classification.txt"), "\n") do
    fs := [w : w in Split(line, " ") | w ne ""];
    if #fs ne 8 then continue; end if;
    okN, N := IsIntegerString(fs[1]);
    okd, d := IsIntegerString(fs[2]);
    if not okN or not okd then continue; end if;
    Include(~fromfile, <N, d, fs[3]>);
end for;
AssertEqual(~results, fromfile, computed,
    Sprintf("data/triple_cover_classification.txt matches the sweep (%o rows read)", #fromfile));

Report(~results, "test_triple_cover_table");
