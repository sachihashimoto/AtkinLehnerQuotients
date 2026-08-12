// tests/test_exceptional_tables.m
//
// Rebuilds the paper's "Exceptional points for genus 3" and "genus 4" tables
// from src/point_search.m's documented entry points:
//
//   interesting := check_exceptional_X0Nstar(g);              // Level column
//   results     := analyze_exceptional(interesting :
//                      max_class_num := 8, confirm_deg2 := true);
//                                                               // Collinearity column
//
// The "Automorphism" column is not reproduced here (out of scope for this
// suite). Factorization is printed for genus 3 (as in the paper table) but
// not separately asserted, it is a deterministic function of Level.
//
// Run with: tests/run.sh test_exceptional_tables
//
// Warning, this is a slow suite, and some levels are known-risky:
//   * max_class_num := 8: every disc in both collinearity tables below has
//     PicardNumber (class number) <= 8, the worst cases are -264, -600,
//     -819, -260, -1995, all h=8; verified directly via PicardNumber(R), not
//     inferred from the CMClassListsDeg2 bucket labels. This bound is exact,
//     not padded: raising it pulls in CMClassListsDeg2's CNs[16] bucket
//     (100+ discs up to D=-20155) that build full ring class fields for
//     every one of the 13 confirm_deg2 levels below without ever being the
//     disc a "found" assertion needs, since a smaller candidate set can only
//     drop planes, never manufacture a spurious match. Do not raise this
//     without re-checking PicardNumber for every disc in both collinearity
//     tables below.
//   * N=399's D=-3 row does not converge at the default eval_prec (3000, also
//     what the genus-4 starforms cache holds), the genus-4 section below
//     retries any such failure with a fresh (UseCache := false), higher-
//     precision (7000) rebuild of that level only, which converges.
// Failures are recorded as soft FAILs (Expect pattern below, same as
// tests/test_find_examples.m) so one bad level does not block the rest of the
// suite or hide unrelated regressions.

load "src/AtkinLehner.m";
load "tests/assertions.m";

results := NewResults();

MAX_CLASS_NUM := 8;
CUSP := 0;  // sentinel used throughout src/labelling.m for the cusp

// =========================================================================
// Genus 3 (paper Table "Exceptional points for genus 3")
// =========================================================================
printf "\n=== Genus 3: check_exceptional_X0Nstar(3) level set ===\n";

expected_levels3 := [178, 183, 246, 290, 310, 318, 329, 430, 455, 510];

interesting3 := check_exceptional_X0Nstar(3 : UseCache := true);
levels3 := Sort([e[1] : e in interesting3]);
AssertEqual(~results, levels3, expected_levels3,
    "genus 3: check_exceptional_X0Nstar(3) level set");

// N -> expected Collinearity discs (subset that must appear together on one
// deg2-matched plane).
collinearity3 := AssociativeArray();
collinearity3[178] := {Integers()| -388, -40};
collinearity3[183] := {Integers()| -483, -75};
collinearity3[246] := {Integers()| -264, -168};
collinearity3[290] := {Integers()| -64, -24};
collinearity3[310] := {Integers()| -55, CUSP};
collinearity3[318] := {Integers()| -852, -372};
collinearity3[329] := {Integers()| -52, -35};
collinearity3[430] := {Integers()| -220, -120};
collinearity3[455] := {Integers()| -819, -195};
collinearity3[510] := {Integers()| -480, CUSP};

printf "\n=== Genus 3: analyze_exceptional (max_class_num:=%o, confirm_deg2:=true) ===\n",
    MAX_CLASS_NUM;
results3 := analyze_exceptional(interesting3 : max_class_num := MAX_CLASS_NUM, confirm_deg2 := true);

function DiscStr(discs)
    if #discs eq 0 then return "none"; end if;
    return Join([d eq 0 select "cusp" else Sprint(d) : d in Sort([s : s in discs])], ", ");
end function;

printf "\n--- Reconstructed Table: Exceptional points for genus 3 ---\n";
printf "%-6o %-16o %o\n", "Level", "Factorization", "Collinearity";
for r in results3 do
    N := r[1]; planes := r[3]; fail_reason := r[5];

    if fail_reason ne "" then
        printf "%-6o %-16o FAILED: %o\n", N, Factorization(N), fail_reason;
        AssertEqual(~results, fail_reason, "",
            Sprintf("N=%o: analyze_exceptional succeeded", N));
        continue;
    end if;

    expected := collinearity3[N];
    matched_planes := [p : p in planes | p[5] and expected subset p[4]];
    found := #matched_planes gt 0;
    printf "%-6o %-16o %o\n", N, Factorization(N),
        found select DiscStr(expected) else "NOT FOUND";
    AssertEqual(~results, found, true,
        Sprintf("N=%o: exists deg2-matched plane containing discs %o  (found plane disc sets: %o)",
            N, expected, [p[4] : p in planes | p[5]]));
end for;

// =========================================================================
// Genus 4 (paper Table "Exceptional points for genus 4")
// =========================================================================
printf "\n=== Genus 4: check_exceptional_X0Nstar(4) level set ===\n";

expected_levels4 := [137, 311, 370, 399];

interesting4 := check_exceptional_X0Nstar(4 : UseCache := true);
levels4 := Sort([e[1] : e in interesting4]);
AssertEqual(~results, levels4, expected_levels4,
    "genus 4: check_exceptional_X0Nstar(4) level set");

collinearity4 := AssociativeArray();
collinearity4[137] := {Integers()| -32, -11, -4, CUSP};
collinearity4[311] := {Integers()| -232, -123, -19};
collinearity4[370] := {Integers()| -340, -260, -16, CUSP};
collinearity4[399] := {Integers()| -1995, -483, -147, -84};

printf "\n=== Genus 4: analyze_exceptional (max_class_num:=%o, confirm_deg2:=true) ===\n",
    MAX_CLASS_NUM;
results4 := analyze_exceptional(interesting4 : max_class_num := MAX_CLASS_NUM, confirm_deg2 := true);

// N=399's D=-3 CM point needs more q-expansion precision than the default
// (3000, also all the genus-4 starforms cache holds) to converge. interesting4
// was built with UseCache := true, so its Sstar is a precision-capped power
// series list rather than a live CuspForms basis, BoostFsPrec (the usual
// retry_precision_failures mechanism) can't extend a materialized series, it
// can only ask a live modular form for more q-expansion terms. So instead of
// retrying via BoostFsPrec, rebuild fresh (UseCache := false) at higher
// eval_prec for exactly the entries that still need it; verified this
// converges N=399 to the expected {-1995,-483,-147,-84} plane.
RETRY_EVAL_PREC := 7000;
for i in [1..#results4] do
    if "needs higher eval_prec" notin results4[i][5] then continue; end if;
    N := results4[i][1];
    printf "\n=== Retrying N=%o fresh at eval_prec=%o (UseCache := false) ===\n", N, RETRY_EVAL_PREC;
    retry_interesting := check_exceptional_example(N : UseCache := false, eval_prec := RETRY_EVAL_PREC);
    retry_results := analyze_exceptional(retry_interesting : max_class_num := MAX_CLASS_NUM, confirm_deg2 := true);
    results4[i] := retry_results[1];
end for;

printf "\n--- Reconstructed Table: Exceptional points for genus 4 ---\n";
printf "%-6o %o\n", "Level", "Collinearity";
for r in results4 do
    N := r[1]; planes := r[3]; fail_reason := r[5];

    if fail_reason ne "" then
        printf "%-6o FAILED: %o\n", N, fail_reason;
        AssertEqual(~results, fail_reason, "",
            Sprintf("N=%o: analyze_exceptional succeeded", N));
        continue;
    end if;

    expected := collinearity4[N];
    matched_planes := [p : p in planes | p[5] and expected subset p[4]];
    found := #matched_planes gt 0;
    printf "%-6o %o\n", N, found select DiscStr(expected) else "NOT FOUND";
    AssertEqual(~results, found, true,
        Sprintf("N=%o: exists deg2-matched plane containing discs %o  (found plane disc sets: %o)",
            N, expected, [p[4] : p in planes | p[5]]));
end for;

// =========================================================================
// Summary
// =========================================================================
printf "\n";
Report(~results, "test_exceptional_tables");
