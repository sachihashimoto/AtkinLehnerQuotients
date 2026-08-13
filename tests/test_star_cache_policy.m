// tests/test_star_cache_policy.m
//
// The data/starmodels/ cache is now read by default (point_search_X0Nstar and
// the check_exceptional_* entry points take UseCache := true), so the two
// things that default made load-bearing are pinned here:
//
//   1. Read policy. A cache hit returns a materialized fixed-precision series
//      list in the Sstar slot, a fresh build returns a live form basis. Both
//      must find the same rational points, since the cached rebuild goes
//      through CanonicalModelFromForms / HyperellipticModelFromForms rather
//      than the builder that produced the entry. A cache *miss* must return
//      the live basis too (section 2): it built one, and only a live basis can
//      be asked for more q-expansion terms later.
//
//   2. Write policy. A level with no entry gets one written; an entry that
//      already exists is left alone even when the run needs more terms than it
//      holds, because data/starmodels/ is committed and rewriting
//      starforms_<M>.m silently invalidates every map_<M>_*.m built against it
//      (README, "Regenerating the cache"). Only GrowCache := true rewrites.
//
//   3. The retry path. A cache hit's Sstar cannot be re-expanded, so
//      BoostFsPrec fails soft on it by design; retry_precision_failures must
//      recover by rebuilding the level fresh rather than skipping the retry.
//      Before that recovery existed, a "needs higher eval_prec" failure on a
//      cache-built entry was unfixable in-process and callers had to rebuild
//      by hand (tests/test_exceptional_tables.m used to carry that workaround).
//
// tests/test_find_examples.m covers the other half of 3, where Sstar is live
// and BoostFsPrec extends it directly.
//
// Levels: N=154 (2*7*11, genus 2 hyperelliptic) has a committed cache entry
// and is only ever read here; N=158 (2*79, same shape) is the level whose
// entry the write tests create and destroy, stashing and restoring anything
// already there so the suite is repeatable and leaves the checkout as it found
// it. Both are small enough to keep this suite fast.
//
// Run with: tests/run.sh test_star_cache_policy

load "src/AtkinLehner.m";
load "tests/assertions.m";

results := NewResults();

N154 := 2*7*11;
N158 := 2*79;

// -------------------------------------------------------------------------
// 1: read policy. Cached and fresh builds of the same level agree on points.
// -------------------------------------------------------------------------
printf "\n=== Read policy: cached vs fresh build of N=%o ===\n", N154;

ok154, prec154 := LoadStarForms(N154);
AssertEqual(~results, ok154, true,
    "N=154: committed starforms entry loads  (this suite assumes one exists)");
printf "N=154: cache entry holds %o terms\n", prec154;

B := 100;   // small: the two runs are compared against each other, not a table
pts_cached, X_cached, fs_cached, Sstar_cached := point_search_X0Nstar(N154, B);
pts_fresh,  X_fresh,  fs_fresh,  Sstar_fresh  := point_search_X0Nstar(N154, B : UseCache := false);

// The cache hit hands back fs_full, a list of power series; the fresh build
// hands back the live forms its q-expansions came from. That difference is
// precisely what BoostFsPrec can and cannot extend, which is why the retry
// path in 3 exists.
BOOST_PREC := 200;
AssertEqual(~results, Type(Sstar_cached[1]), RngSerPowElt,
    Sprintf("N=154: UseCache (default) returns a materialized series list  (got %o)",
    Type(Sstar_cached[1])));
AssertEqual(~results, BoostFsPrec_hyperelliptic(Sstar_cached, BOOST_PREC), [],
    "N=154: a cached Sstar cannot be re-expanded (BoostFsPrec fails soft)");
AssertEqual(~results, Type(Sstar_fresh[1]) eq RngSerPowElt, false,
    Sprintf("N=154: UseCache := false returns live forms, not series  (got %o)",
    Type(Sstar_fresh[1])));
AssertEqual(~results, #BoostFsPrec_hyperelliptic(Sstar_fresh, BOOST_PREC), 2,
    Sprintf("N=154: a fresh Sstar can be re-expanded to %o terms", BOOST_PREC));

// StarModelWithForms reports which of the two it has: a hit read series off
// disk and never constructed a basis, so it hands back none.
_, _, full154, live154 := StarModelWithForms(N154, 30);
AssertEqual(~results, #live154, 0,
    "N=154: a cache hit returns no live basis (there is none to return)");
AssertEqual(~results, Type(full154[1]), RngSerPowElt,
    Sprintf("N=154: a cache hit still returns the cached series  (got %o)", Type(full154[1])));

// Same points, up to the coordinate representation of the two curve objects.
coords_cached := {Eltseq(P) : P in pts_cached};
coords_fresh  := {Eltseq(P) : P in pts_fresh};
AssertEqual(~results, coords_cached, coords_fresh,
    Sprintf("N=154: cached and fresh models give the same %o rational points at bound %o",
    #coords_fresh, B));

// -------------------------------------------------------------------------
// 2: write policy, all three branches: create, keep, grow.
// -------------------------------------------------------------------------
// The suite owns N=158's cache entry for the duration rather than reading
// whatever the checkout happens to have: it stashes any existing file first,
// so each branch starts from a known state and the section gives the same
// answer on every run, then puts the original back. N=158 is used (not the
// committed N=154 entry) so that a crash between the stash and the restore
// cannot lose committed data; the worst case is an untracked cache file
// sitting at .testbak, which nothing reads.
//
// Precisions are deliberately tiny. These branches are about which file is on
// disk afterwards, and a 200-term rebuild of a genus-2 level is nearly free.
printf "\n=== Write policy: create / keep / grow for N=%o ===\n", N158;

path158 := StarFormsCachePath(N158);
bak158  := path158 cat ".testbak";
System("mv " cat path158 cat " " cat bak158 cat " 2>/dev/null");   // no-op if absent

AssertEqual(~results, LoadStarForms(N158), false,
    "N=158: starts the write tests with no cache entry");

// Regression: a cache MISS must hand back the live basis it just built, not a
// frozen copy of it. The frozen copy is what gets written to disk, and
// returning that instead would cost a caller who later needs more terms a full
// rebuild of a basis this call already had in hand. Only a hit (section 1) has
// no live basis to give. Asserted through point_search_X0Nstar because that is
// the contract callers see: its Sstar feeds retry_precision_failures.
_, _, _, Sstar_miss := point_search_X0Nstar(N158, 100);
AssertEqual(~results, #BoostFsPrec_hyperelliptic(Sstar_miss, 3200), 2,
    "N=158: a cache miss returns a live, still-boostable Sstar");

// That call wrote an entry; drop it so the branches below start from absent.
System("rm -f " cat path158);

// (a) create: a level with no entry gets one written.
SHORT := 200;
StarModelWithForms(N158, SHORT : cache_prec := SHORT);
ok_created, prec_created := LoadStarForms(N158);
AssertEqual(~results, <ok_created, prec_created>, <true, SHORT>,
    Sprintf("N=158: absent entry is created, with %o terms", SHORT));

// (b) keep: an entry that is too short is rebuilt in memory, not on disk.
WANT := 300;
_, _, full158 := StarModelWithForms(N158, WANT : cache_prec := WANT);
ok_kept, prec_kept := LoadStarForms(N158);
AssertEqual(~results, <ok_kept, prec_kept>, <true, SHORT>,
    Sprintf("N=158: %o-term entry survives a %o-term rebuild (no silent overwrite)", SHORT, WANT));
AssertEqual(~results, AbsolutePrecision(full158[1]) ge WANT, true,
    Sprintf("N=158: that rebuild still returns the %o terms asked for  (got %o)",
    WANT, AbsolutePrecision(full158[1])));

// (c) grow: GrowCache := true is the way to rewrite it.
StarModelWithForms(N158, WANT : cache_prec := WANT, GrowCache := true);
ok_grown, prec_grown := LoadStarForms(N158);
AssertEqual(~results, <ok_grown, prec_grown>, <true, WANT>,
    Sprintf("N=158: GrowCache := true rewrites the entry to %o terms", WANT));

// Restore whatever was there before this section.
System("rm -f " cat path158);
System("mv " cat bak158 cat " " cat path158 cat " 2>/dev/null");

// -------------------------------------------------------------------------
// 3: retry policy. A materialized Sstar cannot be boosted, so
// retry_precision_failures rebuilds the level instead of skipping it.
// -------------------------------------------------------------------------
printf "\n=== Retry policy: cached Sstar triggers a fresh rebuild for N=%o ===\n", N158;

// UseCache := false both to get a live Sstar to materialize from and to leave
// N=158's cache state alone now that section 2 has restored it.
pts158, X158, fs158, Sstar158 := point_search_X0Nstar(N158, 3000 : UseCache := false);
cm158 := RationalCMDiscs(N158);

// Exactly what a cache hit puts in the Sstar slot: fixed-precision series.
materialized158 := BoostFsPrec_hyperelliptic(Sstar158, 3000);
AssertEqual(~results, Type(materialized158[1]), RngSerPowElt,
    Sprintf("N=158: materialized Sstar is a power series list  (got %o)",
    Type(materialized158[1])));
AssertEqual(~results, BoostFsPrec_hyperelliptic(materialized158, 3500), [],
    "N=158: BoostFsPrec cannot extend a materialized Sstar (fails soft, returns [])");

// Synthetic results/interesting pair whose fail_reason triggers the retry,
// same construction as the hyperelliptic dispatch test in
// tests/test_find_examples.m, but with the un-boostable Sstar.
fake_interesting158 := [* <N158, 1, pts158, X158, fs158, materialized158, cm158> *];
fake_results158 := [*
    <N158, [], [* *], false,
     "D=-7: g(q)~0 at CM point and WPS infinity match failed (needs higher eval_prec)">
*];
retry158 := retry_precision_failures(fake_results158, fake_interesting158 : new_eval_prec := 3000);
AssertEqual(~results, retry158[1][5], "",
    Sprintf("N=158: retry recovers from an un-boostable Sstar by rebuilding  (fail_reason: %o)",
    retry158[1][5]));
AssertEqual(~results, #retry158[1][2], 1,
    Sprintf("N=158: rebuilt retry returns 1 exceptional index  (got %o)", #retry158[1][2]));

Report(~results, "test_star_cache_policy");
