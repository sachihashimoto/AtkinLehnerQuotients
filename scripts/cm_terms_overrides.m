// scripts/cm_terms_overrides.m
//
// Not a standalone script, do not run this file directly. It only
// defines a lookup table (`cm_terms_override`) and is pulled in via
// `load "scripts/cm_terms_overrides.m";` by:
//   - scripts/run_triple_covers.m
//   - scripts/make_exceptional_table.m
// Editing this file changes behavior for both.
//
// What it's for: CMFiberSetup (src/triple_covers.m) asks for `cm_terms`
// terms of a q-expansion when trying to pin down a CM point (default
// 3000, auto-doubled once to 6000 on a failed retry). For most levels
// that's enough. This file lets you hand-raise that starting value for
// a specific top level M, keyed by the integer M, when even the doubled
// retry isn't enough.
//
// When to add an entry: if a run fails to converge on a CM point even
// after the automatic retry, add a line here for that top level M with
// a higher term count, and reference this file in your commit/PR notes.
//
// Current overrides:
//   399 (X_0(399)*, covering X_0(57)*): its D=-3 CM point has extra
//   order-6 units and didn't converge even at the doubled 6000-term
//   retry, so it asks for 7000 terms directly.
cm_terms_override := AssociativeArray();
cm_terms_override[399] := 7000;
