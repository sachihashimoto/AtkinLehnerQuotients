// tests/test_deg2_status_helpers.m
// Direct unit tests for the two pure decision-table helpers factored out of
// AlgebraicDeg2Matches (src/labelling.m): DiscStatusOnComponent and
// ComponentAggregate. Fast, no model-building or CM machinery; exercises
// the truth tables directly, including the exact scenarios the review
// flagged that real CM data would be slow/awkward to reproduce:
//   - a class-number > 2 discriminant where an irrelevant pair is
//     trustworthy but the actual candidate pair is too noisy to test
//     (must be "inconclusive", not "rejected");
//   - a discriminant with missing orbit representatives (must be
//     "inconclusive", not "rejected");
//   - a component with one confirmed disc and one still-inconclusive disc
//     (the inconclusive one must not be silently dropped).
//
// Run with: tests/run.sh test_deg2_status_helpers

load "src/AtkinLehner.m";
load "tests/assertions.m";

results := NewResults();

// -------------------------------------------------------------------------
// DiscStatusOnComponent(found, any_pair_trustworthy, all_pairs_trustworthy,
//                        all_orbits_present)
// -------------------------------------------------------------------------

AssertEqual(~results,
    DiscStatusOnComponent(true, false, false, false), "confirmed",
    "found=true is always confirmed, regardless of the accuracy flags");

AssertEqual(~results,
    DiscStatusOnComponent(false, true, true, true), "rejected",
    "not found, every pair trustworthy, every orbit present -> rejected");

// The review's core scenario: some irrelevant pair was accurate enough to
// test (and failed), but not every combinatorial pair was; the real
// candidate pair may have been the untested one. Must not be "rejected".
AssertEqual(~results,
    DiscStatusOnComponent(false, true, false, true), "inconclusive",
    "not found, only SOME pairs trustworthy -> inconclusive, not rejected");

// Second form of the same issue: an orbit representative failed to converge
// and is silently absent, so fewer pairs were even attempted than exist.
AssertEqual(~results,
    DiscStatusOnComponent(false, true, true, false), "inconclusive",
    "not found, not all orbit representatives present -> inconclusive, not rejected");

AssertEqual(~results,
    DiscStatusOnComponent(false, false, true, true), "inconclusive",
    "not found, no pair ever trustworthy -> inconclusive (unchanged gray-zone case)");

// -------------------------------------------------------------------------
// ComponentAggregate(confirmed_discs, inconclusive_discs)
//   -> (status, matches_contribution, inconclusive_contribution)
// -------------------------------------------------------------------------

Z := Integers();

status, m_add, i_add := ComponentAggregate({Z|1}, {Z|});
AssertEqual(~results, status eq "confirmed" and m_add eq {Z|1} and i_add eq {Z|}, true,
    Sprintf("single confirmed disc, nothing inconclusive -> confirmed, matches={1} (got %o, %o, %o)", status, m_add, i_add));

status, m_add, i_add := ComponentAggregate({Z|1,2}, {Z|});
AssertEqual(~results, status eq "ambiguous" and m_add eq {Z|} and i_add eq {Z|1,2}, true,
    Sprintf("two confirmed discs -> ambiguous, neither goes into matches (got %o, %o, %o)", status, m_add, i_add));

status, m_add, i_add := ComponentAggregate({Z|}, {Z|3});
AssertEqual(~results, status eq "inconclusive" and m_add eq {Z|} and i_add eq {Z|3}, true,
    Sprintf("no confirmed disc, one inconclusive -> inconclusive (got %o, %o, %o)", status, m_add, i_add));

status, m_add, i_add := ComponentAggregate({Z|}, {Z|});
AssertEqual(~results, status eq "unlabelled" and m_add eq {Z|} and i_add eq {Z|}, true,
    Sprintf("nothing confirmed or inconclusive -> unlabelled (got %o, %o, %o)", status, m_add, i_add));

// The bug fix: one confirmed disc and a different, still-inconclusive disc
// on the same component. The confirmed disc still becomes a match (it stands
// on its own numerical certification), but the inconclusive disc must not be
// silently dropped, it has to surface in the inconclusive contribution.
status, m_add, i_add := ComponentAggregate({Z|1}, {Z|2});
AssertEqual(~results, status eq "confirmed" and m_add eq {Z|1} and i_add eq {Z|2}, true,
    Sprintf("confirmed disc 1 + inconclusive disc 2 on same component: 1 confirmed, 2 NOT dropped (got %o, %o, %o)", status, m_add, i_add));

// Second review's finding: an ambiguous component (>1 confirmed disc) must
// not drop a third, still-inconclusive disc on the same component; the
// unresolved contribution has to be confirmed_discs join inconclusive_discs,
// not confirmed_discs alone, or the third disc silently vanishes from the
// caller's global inconclusive set even though it remains unresolved against
// this same component.
status, m_add, i_add := ComponentAggregate({Z|1,2}, {Z|3});
AssertEqual(~results, status eq "ambiguous" and m_add eq {Z|} and i_add eq {Z|1,2,3}, true,
    Sprintf("ambiguous discs 1,2 + inconclusive disc 3 on same component: nothing confirmed, {1,2,3} all unresolved (got %o, %o, %o)", status, m_add, i_add));

Report(~results, "test_deg2_status_helpers");
