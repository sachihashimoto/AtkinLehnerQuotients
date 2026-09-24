# CLAUDE.md

Magma code for the paper "Exceptional points on Atkin-Lehner quotients" (Assaf,
Hashimoto, Shnidman). It builds models of the quotient curves X_0(N)* for
squarefree N, searches them for rational points, labels each found point (cusp /
elliptic / CM of known discriminant / exceptional), and explains the exceptional
ones geometrically — via coplanar CM triples, and via degree-3 covers
X_0(M)* -> E where an exceptional point shares a fiber with CM points.

## Running things

Everything assumes **cwd = repo root**: every `load` and every cache/data path in
the repo is relative (`src/...`, `data/starmodels/...`), so a Magma session or
script started elsewhere fails to find its files. `tests/run.sh` enforces this
explicitly (checks for `src/AtkinLehner.m`, exits 2 otherwise).

```
magma                                  # then: load "src/AtkinLehner.m";
magma -b <file.m>                      # batch, no banner; how scripts and tests run
magma -b key:=value <file.m>           # script parameters arrive as STRINGS

magma -b g:=7 scripts/gen_genus_models.m              # also eval_prec:=; default gs = [5,6]
magma -b caseidx:=5 scripts/run_triple_covers.m       # also bigB:= fibersearch:= ramified:= cuspfiber:=
magma -b fast:=1 scripts/make_exceptional_table.m     # also discover:=1, only_cm:=0
magma -b B:=100000 shard:=1 nshards:=8 scripts/pointsearch_g8.m
bash scripts/run_pointsearch_g8.sh                    # 8 shards in parallel, then concatenates
```

Most scripts end in `quit;`/`exit;`, so they are batch-only; `certify_committed_models.m`,
`check_automorphisms.m`, `check_fiber_table.m` and `make_plane_multiplicity_table.m`
do not and can also be `load`ed in a session.

- `load "src/AtkinLehner.m";` pulls in `QuadraticPoints/models_and_maps.m` plus
  11 of the 13 src modules, in dependency order. Each header says whether the
  module is loadable standalone: most are not, but `cm_points.m`, `cm_orders.m`
  and `cm_numerics.m` are self-contained (`tests/test_cm_points.m` loads
  `cm_points.m` directly).
- `src/triple_covers.m` loads `AtkinLehner.m` itself — load it *instead*, not after.
- `src/hnf_canonical.m` is not in the chain: load it *after* `AtkinLehner.m`, so
  `all_diag_basis` and `modelsX0Nstar.m`'s helpers are already declared.
- Script parameters are checked with `assigned x` and are strings, so they need
  `StringToInteger`, or comparisons like `fast eq "1"`.

Tests:

```
tests/run.sh                    # fast suites only (default)
tests/run.sh --slow             # ALSO the slow suites, not only them
tests/run.sh test_cm_points     # one suite, output streamed; accepts bare name, tests/x, x.m
magma -b tests/test_cm_points.m # direct, no status accounting
```

Suites are discovered by globbing `tests/test_*.m`, so a new file is picked up
automatically. `SLOW_SUITES` at the top of `run.sh` currently excludes
`test_find_examples test_311_jmap test_degree_formula`. Each suite is a separate
Magma process. Status comes from the `@@TEST_RESULT@@` marker that
`Report` prints, combined with exit code: exactly one marker + PASS + exit 0 =>
`PASS`; one marker + FAIL + exit 1 => `FAIL`; anything else (including zero
markers) => `INCOMPLETE`. `INCOMPLETE` means the test itself did not run — crash,
broken fixture, or a suite that asserted nothing (`Report` raises when
`nassert eq 0`, deliberately emitting no marker). Do not run the full suite
casually: `--slow` is ~43 min, dominated by `test_311_jmap`.

## Layout

- `src/` — the library. `AtkinLehner.m` loader; `cm_points.m` exact CM points via
  optimal embeddings; `cm_orders.m` class-number bookkeeping (defines `omega`);
  `star_quotients.m` genera and level enumeration by genus; `modelsX0Nstar.m`
  canonical/hyperelliptic models + Sturm certification; `star_model_cache.m`
  (`StarModelWithForms`, disk cache); `cm_numerics.m` q-expansion evaluation at CM
  tau; `fields_of_definition.m` ring-class-field degrees and rational/degree-2
  discs; `labeling.m` labels points and fits planes through CM triples;
  `point_search.m` the driver entry points; `star_degree.m` (c_n, delta_f, E^C_f);
  `classify_covers.m` (`ClassifyTripleCovers`); out-of-chain `triple_covers.m` and
  `hnf_canonical.m`.
- `scripts/` — `gen_genus_models.m` (regenerates `data/genus<g>_models.m`),
  `certify_committed_models.m`, `classify_triple_covers.m` (writes
  `data/triple_cover_classification.txt`), `run_triple_covers.m`,
  `make_exceptional_table.m`, `make_plane_multiplicity_table.m`,
  `pointsearch_examples.m`, `pointsearch_g8.m` + `run_pointsearch_g8.sh`,
  `check_automorphisms.m` (verifies the paper tables' Automorphism column),
  `check_fiber_table.m` (regenerates the paper's CM-fiber table), and the
  one-off `automorphisms_<N|genus g>.m` automorphism checks.
  `cm_terms_overrides.m` is a lookup table `load`ed by two scripts, not a script.
- `tests/` — one `test_*.m` per topic, `assertions.m` (shared), `run.sh`,
  and `logs/` (transcripts, git-ignored).
- `data/` — `genus3_models.m`..`genus8_models.m` (one `models[N]` record per
  squarefree level, HNF basis, all curves in one shared `P`),
  `triple_cover_classification.txt`, and `starmodels/` (cache; all 151 files are
  git-tracked).

Paper artifacts: `scripts/make_exceptional_table.m` reproduces the paper's
exceptional-points table (~20 min; `fast:=1` for the ~1 min subset).
`scripts/make_plane_multiplicity_table.m` emits the supplementary
collinearity-plane table as LaTeX. `data/triple_cover_classification.txt`
matches the paper's triple-cover table; `tests/test_triple_cover_table.m` pins
the two against each other.

## Gotchas

- **Submodule.** `QuadraticPoints/` is a git submodule
  (`sachihashimoto/QuadraticPoints`). Without `git submodule update --init`, the
  first `load "QuadraticPoints/models_and_maps.m"` dies with `Could not open file`.
- **`outputs/` is git-ignored and created on demand**: each script that writes
  there (`gen_genus_models.m`, `pointsearch_*.m`, `run_pointsearch_g8.sh`) runs
  its own `mkdir -p outputs` first.
- **Star-forms cache read vs. write.** `StarModelWithForms` reads
  `data/starmodels/starforms_<N>.m` by default (that AL diagonalization is nearly
  all the cost of a level). It creates an absent entry, but an existing entry that
  is too short is rebuilt *in memory only* unless `GrowCache := true` — currently
  only `BuildTripleCover` asks for that. Reason: the directory is committed, and
  rewriting `starforms_<M>.m` silently invalidates every `map_<M>_*.m` built
  against it (maps store polynomial exponents but not the coordinate system).
  If you regenerate `starforms_<M>.m`, delete every `map_<M>_*.m`.
- **Cache hit vs. live basis.** On a hit, the returned `Sstar` is a frozen
  fixed-precision series list; `BoostFsPrec` cannot extend it (fails soft, returns
  `[]`). So `StarModelWithForms` returns a 4th value (the live basis, empty on a
  hit), `point_search_X0Nstar`'s returned `Sstar` prefers the live basis when one
  was built, and `retry_precision_failures` recovers by rebuilding with
  `UseCache := false`.
- **`eval_prec` / precision retries.** Default 3000 terms. Labeling failures carry a
  `fail_reason` containing `"needs higher eval_prec"`;
  `retry_precision_failures(results, interesting)` re-runs exactly those at 7000.
  Likewise `CMFiberSetup`'s `cm_terms` (default 3000) auto-doubles once to 6000,
  with per-level starting bumps in `scripts/cm_terms_overrides.m` (only
  `399 -> 7000` today). Precision changes *confidence in the CM identification*,
  not the geometry.
- **Squarefree is assumed, not incidental.** `RationalCMDiscs`,
  `DegreeOfFieldOfDefinitionOfCMPoint` and `count_special_points_X0Nstar` assert
  `IsSquarefree(N)`; genus sweeps skip non-squarefree levels; `ALTranslations`
  errors on non-squarefree conductors.
- **`gen_genus_models.m` deliberately passes `UseCache := false`** — a cached rebuild
  gives the same curve through different ideal generators, breaking the
  regenerate-and-diff check against the committed files. No resume mode either.
- **`load` needs a literal filename** in Magma (no computed paths, invalid inside a
  loop body); `certify_committed_models.m` unrolls its four genus loads for this.
- **`Nonsingular := true`** on every canonical-model `PointSearch`: the default
  singularity precheck is a Groebner computation that dominates at genus 8 and hangs
  at omega = 4 levels. Valid since canonical models of non-hyperelliptic curves are
  smooth. Hyperelliptic levels take `PointsOriginalModel` instead.
- **"Confirmed"/"certified" in `labeling.m`** means numerically checked at two
  precisions and two q-expansion lengths against a noise-scaled tolerance — strong
  evidence, not proof. Real proof is the Sturm-bound path
  (`CertifyModularIdentity`), which errors rather than under-certify.

## Conventions

- Library functions are `CamelCase` (`XZeroNstarWithForms`); the user-facing drivers
  in `point_search.m` are `snake_case` (`check_exceptional_example`). Keep the split.
- Every src file opens with a header naming its **entry points**, its dependencies,
  and whether it is loadable standalone. Preserve this; headers explain *why*.
- Comments are short, in plain language, and avoid jargon; the file-top
  headers especially should read easily for someone new to the repo. No
  em-dashes in comments.
- Comments describe the present state of the code, never its history: no
  "this used to...", no citing removed functions or prior versions. If a past
  bug matters, state the invariant it revealed, not the story of fixing it.
- Cite the theorem, don't reprove it: "quadrics cut out the canonical curve
  unless it is trigonal or a plane quintic (Petri)" is the right scale for a
  math comment.
- Inline comments state constraints the code cannot show (why
  `Nonsingular := true` is valid, why an existing cache entry is not
  rewritten), not what the next line does. The exception is a genuinely
  unclear line, where saying what it does is appropriate.
- Results are passed as tuples and `[* *]` lists in a fixed order — e.g.
  `check_exceptional_example` entries are `<N, n, rats, X, fs, Sstar, cm_pts>` and
  `analyze_exceptional` returns `<N, exc, planes, all_matched, fail_reason>`.
  `retry_precision_failures` asserts the two lists are index-aligned.
- Invariant violations use `error if <cond>, Sprintf(...)` with a message that
  names the level/discriminant and often the likely cause; `assert` is for
  internal sanity checks.
- Test suites: `load` the module under test, then `load "tests/assertions.m";`,
  `results := NewResults();`, many `AssertEqual(~results, actual, expected, label)`
  (records rather than raises, so one run reports every failure), and exactly one
  `Report(~results, "test_<name>")` at the very end. `assertions.m` sets
  `SetQuitOnError(true)` centrally so no suite can forget it. Labels must identify
  the example (level, discriminant, row); suites touching randomized Magma paths
  call `SetSeed(1)`; expected values are derived from an independent computation
  (e.g. `NumberOfOptimalEmbeddings`) rather than hand-written where possible.
