# AtkinLehner

Computational tools for constructing and analysing Atkin–Lehner quotient
curves X₀\*(N), searching for exceptional
CM points on them, and explaining these exceptional points via geometry.
Companion code to "Exceptional points on Atkin-Lehner quotients" by Eran Assaf, Sachi Hashimoto, and Ari Shnidman

## License and attribution

This repository is licensed under the MIT License; see [`LICENSE`](LICENSE).

`src/modelsX0Nstar.m` is adapted from
[`sachihashimoto/X0Nstarquotients`](https://github.com/sachihashimoto/X0Nstarquotients), by Sachi Hashimoto, Timo Keller, and Samuel Le Fourn,
licensed under [CC BY-4.0](https://creativecommons.org/licenses/by/4.0/).
It is edited from the upstream original.

Many functions from this repository are derived from [assaferan/ShimuraCurveALQuotients](https://github.com/assaferan/ShimuraCurveALQuotients) by Eran Assaf and Sachi Hashimoto.

## Hardware and timing note

Every runtime quoted in this README was measured on a MacBook Pro (Apple M4
Pro, 24 GB RAM, macOS 26.5.1) running Magma V2.29-4.

## How to install

To install, you will need to clone this repository and its submodule.

This repository uses a git submodule for `QuadraticPoints/` (a patched fork
of `TimoKellerMath/QuadraticPoints`, see "`QuadraticPoints` dependency"
below). Initialize it as part of cloning the repository:

```
git clone --recurse-submodules <this repository's URL>
```

or, if you already have a clone without it:

```
git submodule update --init --recursive
```

If you skip this, `QuadraticPoints/` is empty and the first script you run
dies at `load "QuadraticPoints/models_and_maps.m"` with `Could not open
file`, a cryptic error that just means the submodule was never fetched.
Beyond the submodule, the only further requirement is Magma itself.

## Quickstart

In order to run these commands, make sure Magma is installed and available, and open a terminal with magma in the project's main folder.

**1. Check one example.**

```
load "src/AtkinLehner.m";
result := check_exceptional_example(137);
```

Expected output ends `Special points: 8` with 9 points found overall: 8
CM-plus-cusp points, and one point left over. That leftover is the
exceptional point. Measured runtime is about ~1.7 s.

**2. Explain the exceptional point.**

```
load "src/AtkinLehner.m";
result := check_exceptional_example(137);
analyze_exceptional(result);
```

This passes the list that `check_exceptional_example` returns straight into
`analyze_exceptional`. Expected output ends `All exceptional points in a plane: true`. Measured runtime ~1.6 s.

**3. Sweep through a whole genus.**

```
load "src/AtkinLehner.m";
check_exceptional_X0Nstar(4);
```

Runs over all 36 squarefree genus 4 levels. Defaults to a point search bound of height
`B = 1000`. Expected answer: **N = 137, 311, 370, and 399** are exactly the
four genus-4 levels with an exceptional point (one each). The other 32 have
none. A larger `B` can only ever *add* points, so this is a lower bound on
what a bigger search would find. Measured ~703 s (~11.7 min).

**4. Build a triple cover and inspect a CM fiber.**

The triple-cover code (`src/triple_covers.m`) is separate from
`src/AtkinLehner.m`, and is normally run through `scripts/run_triple_covers.m`
 but it also can be used directly in a Magma session. There is one builder,
`BuildTripleCover(M, Elabel)`: `M` is the top level and `Elabel` the Cremona
label of the target curve E<sup>C</sup><sub>f</sub>. The newform level
`d = Conductor(E)` is derived, not supplied. What you choose next depends only
on whether you already know a discriminant to check.

If you already have a discriminant in mind:

```
load "src/triple_covers.m";
pi, X, E, fs, Sstar, c := BuildTripleCover(290, "58a1");
results := AnalyzeCMFiber(pi, X, E, fs, Sstar, 290, -136);
```

Builds π : X₀(290)\* → X₀(58)\* = 58a1 (~8.3 s), then analyzes the fiber over
the disc `-136` CM points (~27 s). Expected output ends by identifying the
third point of that fiber as the cusp:
`>>> THIRD POINT in the fiber over Q = (0 : 1 : 0): (1 : 0 : 0)   [cusp]`.

If you don't have a discriminant in mind you can sweep every plausible discriminant, and the cusp fiber, instead:

```
load "src/triple_covers.m";
pi, X, E, fs, Sstar, c := BuildTripleCover(258, "258a1");
rows := SweepCMFibers(pi, X, E, fs, Sstar, 258);
```

Builds π : X₀(258)\* → 258a1 (~9 s), then checks every plausible CM
discriminant for a rational fiber (~16 s). Expected output ends with a
`SWEEP SUMMARY` reporting three residual points: the single cusp fiber over
`Q = (0:1:0)` splits completely into three distinct rational points (degree
`[1, 1, 1]`, since π has degree 3), so besides the cusp itself it reports
*two* residual points (CM discs `-48` and `-12`); the CM-disc loop then finds
one more, over `D = -156` (CM disc `-8`).

**5. Count special points**

```
load "src/AtkinLehner.m";
levels := SquarefreeStarQuotientsOfGenusExactly(5);
for pair in levels do
  N := pair[1];
  special := count_special_points_X0Nstar(N);
  printf "N = %o: special = %o\n", N, special;
end for;
```

`SquarefreeStarQuotientsOfGenusExactly(g)` returns every squarefree level
with `X_0(N)*` of genus exactly `g`, as `<N, g>` pairs (39 of them for
`g = 5`). `count_special_points_X0Nstar(N)` counts N's rational CM points plus
the (rational) cusp directly from class-number data, with no point search or model
construction, so the whole sweep is fast: measured **9.26 s total** for all
39 levels. Sample of the output: `N = 157: special = 9`, `N = 227: special = 4`,
`N = 551: special = 2`, `N = 910: special = 4`.

## Running the tests

```
tests/run.sh                 # the 23 fast suites (the default), ~6.2 min
tests/run.sh --slow          # all 26 suites, including the slow ones, ~43 min
tests/run.sh <name>          # one suite, with its output streamed
```

`--slow` means *also* run the slow suites, not *only* the slow ones. Three
suites account for nearly all of the runtime — `test_311_jmap`,
`test_find_examples`, and `test_degree_formula` — and are excluded from the
default run. They are listed in `SLOW_SUITES` at the top of `tests/run.sh`.

`test_311_jmap` dominates: it alone is ~31 min of the ~43 min total, because of
the genus-26 pullbacks it does on X_0(311). Everything else put together is
about 11 minutes. Long stretches with no output during that suite are expected.

Each suite runs in its own Magma process and reports one of three statuses:

| status | meaning |
|---|---|
| `PASS` | the code behaved correctly |
| `FAIL` | the code produced an incorrect result |
| `INCOMPLETE` | the test itself did not run to completion — a crash, a broken fixture, or a suite that asserted nothing |

Every suite is expected to `PASS`. Full transcripts are written to `tests/logs/<suite>.log`,
and the runner prints the path for any suite that is not `PASS`.

To run a suite directly, without the runner:

```
magma -b tests/test_cm_points.m 
```

## Repository layout

- `src/`: the 13 core libraries, plus `AtkinLehner.m`, which loads 11 of them in the required order. The other two load separately: `triple_covers.m` (which loads `AtkinLehner.m` itself) and `hnf_canonical.m` (load it after `AtkinLehner.m`).
- `scripts/`: 9 standalone scripts for generating models, running point searches, building triple covers, and producing the paper's tables. See the table below. The tenth file, `cm_terms_overrides.m`, is a lookup table that two of the scripts load, not a script itself.
- `tests/`: the test suites, plus `tests/assertions.m` (the shared assertion procedures every suite loads) and `tests/run.sh` (the runner). See "Running the tests" below.
- `data/`: reference models of X₀(N)\* in the canonical saturated-HNF basis, one file per genus (`genus3_models.m`-`genus8_models.m`) with one entry per squarefree level of that genus; the degree-3 cover classification table (`triple_cover_classification.txt`); and cached data for triple-cover maps and forms (`data/starmodels/`).
- `QuadraticPoints/`: see submodule section below.

## Script table

| Script                             | What it does                                                                                                       | Example command                                                                                      | Typical runtime                                     | Output                                                        |
| ---------------------------------- | ------------------------------------------------------------------------------------------------------------------ | ---------------------------------------------------------------------------------------------------- | --------------------------------------------------- | ------------------------------------------------------------- |
| Generate genus 5–8 models          | Creates the reference model files for genus 5–8.                                                                   | `magma -b g:=7 scripts/gen_genus_models.m` (omit `g:=` to generate the default genus 5 and 6 models) | Not recorded                                        | `data/genus<g>_models.m`                                      |
| Classify triple covers             | Classifies triple covers and prints the results.                                                                   | `magma -b scripts/classify_triple_covers.m > out.txt`                                                | ~2–4 h                                              | Printed to the terminal (redirect to a file with `> out.txt`) |
| Build the exceptional-points table | Generates the exceptional-points table.                                                                            | `magma -b scripts/make_exceptional_table.m > out.txt` (or `fast:=1` for a ~41 s test run)            | ~20 min; ~41 s with `fast:=1`                       | Printed to the terminal (redirect to a file)                  |
| Build the plane-multiplicity table | Finds *every* confirmed special hyperplane through the exceptional point at each of the 14 genus 3–4 levels, recomputed from scratch at `eval_prec := 7000`, and emits the supplementary LaTeX table. | `magma -b scripts/make_plane_multiplicity_table.m > out.txt`                                          | ~10 min (583 s, 371 MB peak); each level takes 10–100 s and prints as it finishes | A progress line per level, then a LaTeX `tabular`, on the terminal (redirect to a file) |
| Search for a triple cover          | Runs the search for a single case. Optional flags: `bigB:=1` (higher search bound), `ramified:=1`, `cuspfiber:=1`. | `magma -b caseidx:=<n> scripts/run_triple_covers.m`                                                  | ~2–112 s per case (median ~8 s); all 48 cases ~8.4 min | Cached map files in `data/starmodels/`                        |
| Search genus-8 points              | Runs the full genus-8 point search. The script defaults to `B=10^6`; edit `B` near the top to change the bound.    | `bash scripts/run_pointsearch_g8.sh`                                                                 | ~27.7 CPU-hours at `B=10^5` (~3.1 h wall, 8 shards) | `outputs/special_vs_found_g8_sqfree_B<B>.txt`                 |
| Point-search examples              | Runs several example point searches.                                                                               | `magma -b scripts/pointsearch_examples.m`                                                            | 662–9597 s depending on the example                 | `outputs/` (private repository only)                          |


`data/starmodels/` cache note: the search scripts above check this cache
before rebuilding a star model or triple-cover map. See "`data/starmodels/`
cache" below before regenerating anything by hand.

## `data/starmodels/` cache

The `data/starmodels/` directory stores cached intermediate results used when
constructing triple covers. The search scripts check this cache before
recomputing anything, so rerunning a script is often much faster once the
required files have been generated.

The cache contains two kinds of files:

| File | Purpose |
|---|---|
| `starforms_<M>.m` | Cached Atkin Lehner invariant modular forms for level `M`. |
| `map_<M>_<label>.m` | Cached triple-cover maps, keyed by top level and target curve (see below). |

### Regenerating the cache

If you regenerate a `starforms_<M>.m` file, you **must also delete every
corresponding `map_*.m` file for level `M`** before running another search.

This is necessary because the cached map stores only polynomial exponents. It
does **not** record the coordinate system used to create the map. If the model
construction changes (for example, a different coordinate basis is chosen), an
old `map_*.m` file may still load successfully but represent the **wrong**
triple-cover map.

For level `M`, delete every `map_<M>_*.m` — one per target curve, since a level
can carry more than one triple cover (`X_0(286)*` has both `map_286_143a1.m`
and `map_286_286c1.m`).

### Cache file naming

`starforms_<M>.m`

- `<M>` is the level of the star curve.
- These files are written by `SaveStarForms` and loaded by `LoadStarForms`.
- A level with no entry gets one written the first time it is built. If an entry exists but its precision is too low, the run rebuilds in memory and leaves the file alone; only `BuildTripleCover` rewrites an existing entry.

`map_<M>_<label>.m`

- `<M>` is the **top** level: the level of the star curve X₀(M)\* being covered.
- `<label>` is the Cremona label of the target curve E<sup>C</sup><sub>f</sub>.

Every triple cover π : X₀(M)\* → E is built the same way, by
`BuildTripleCover(M, Elabel)`: as a pullback of E's cusp form,
π\*ω = c·h·dq/q once E is known. The pair `(M, label)` determines the map.

## `QuadraticPoints` dependency

`QuadraticPoints/` is a git submodule pointing at
[`sachihashimoto/QuadraticPoints`](https://github.com/sachihashimoto/QuadraticPoints),
a fork of [`TimoKellerMath/QuadraticPoints`](https://github.com/TimoKellerMath/QuadraticPoints)
(forked from commit `2673521`, its `main` at fork time). See "How to install"
above for initializing it.

The fork carries one patch to `models_and_maps.m`'s
`all_diag_basis`. In short, it avoids a combinatorial blow-up in the simultaneous-eigenspace computation.

We load `models_and_maps.m` and use four of its functions:

- `all_diag_basis(N)` — the AL-diagonal integral basis of S₂(Γ₀(N)); its +1
  eigenspace gives the coordinates for every X₀(N)\* model here.
  (`src/modelsX0Nstar.m`, `src/hnf_canonical.m`, `tests/test_311_jmap.m`)
- `eqs_quos(N, als)` — model and quotient map on the hyperelliptic/low-genus
  path, and an independent model of X₀(137)/X₀(137)\* to compare against ours.
  (`src/modelsX0Nstar.m`, `tests/test_137_jmap.m`)
- `canonic(B)` — canonical model of X₀(311)\* from the +1 eigenbasis.
  (`tests/test_311_jmap.m`)
- `jmap(X, N)`, and its worker `find_rels` directly at N = 311 — the
  j-invariant map, used to identify the exceptional points' j-invariants.
  (`tests/test_137_jmap.m`, `tests/test_311_jmap.m`)
