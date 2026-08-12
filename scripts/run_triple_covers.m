// scripts/run_triple_covers.m
//
// Run directly (from the repo root):
//   run one case:    magma -b caseidx:=5 scripts/run_triple_covers.m
//   run everything:  magma -b scripts/run_triple_covers.m
//   fiber point search (pull back all fibers over E(Q) up to height bound;
//   finds rational points of X_0(M)* beyond the PointSearch bound):
//                    magma -b caseidx:=1 fibersearch:=1 scripts/run_triple_covers.m
//   custom case, in a Magma session (bypassing the `cases` table below):
//       load "src/triple_covers.m";
//       pi, X, E, fs, Sstar, c := BuildStarCover(286, "143a1");
//       rows := SweepCMFibers(pi, X, E, fs, Sstar, 286);   // all valid D
//
// Driver for degree-3 maps pi : X_0(M)* -> E, and the analysis of
// the fiber through the discriminant-D CM points of X_0(M)*: the two disc-D
// CM points (a Galois-conjugate quadratic pair, or two rational points) map
// to the same rational point Q of E, and the third point of pi^{-1}(Q) is a
// rational point of X_0(M)*, identified as a CM point / the cusp / an
// exceptional (non-CM) point.
//
// Each entry of `cases` is <M, Elabel>: the top level M and the Cremona label
// of the target curve E^C_f = E_f/C.

//
// Every case sweeps all valid CM discs of X_0(M)* (SweepCMFibers), including
// the cusp fiber; see src/triple_covers.m for AnalyzeCMFiber if you want a
// single disc by hand.
//
// Each case ends with a SUMMARY block: one line per fiber giving the third
// point and its label. After all cases finish, a GRAND SUMMARY collects
// those lines from every case in one place.  Tests: magma -b tests/test_triple_covers.m

load "src/triple_covers.m";

// <top level M, Cremona label of the target E^C_f>.  The pair is exactly the
// triple-cover map cache key, and it determines the map: a degree-3 map
// X_0(M)* -> E is unique up to sign and translation.  The newform level d is
// not listed, BuildStarCover derives it as the conductor of the target's
// isogeny class, which is what keeps a factor-1 prime from being folded into it.
// Every entry appears as a row of outputs/triple_cover_classification.txt.
// "caseidx:=<i>" selects the i-th entry below.
cases := [
    <290, "58a1">,     // 1: genus 3   (d = 58)
    <154, "77a1">,     // 2: genus 2   (d = 77)
    <455, "91a1">,     // 3: genus 3   (d = 91)
    <590, "118a1">,    // 4: genus 6   (d = 118)
    <246, "123b1">,    // 5: genus 3   (d = 123)
    <286, "143a1">,    // 6: genus 2   (d = 143); examples/X0star286.m
    <570, "57a1">,     // 7: genus 4   (d = 57; the prime 2 has a_2 = -2, so
                       //    it contributes factor 1 to the degree)
    <798, "57a1">,     // 8: genus 5   (d = 57; 2 contributes factor 1)
    <870, "58a1">,     // 9: genus 7   (d = 58; 3 contributes factor 1)
    <910, "91a1">,     // 10: genus 5  (d = 91; 2 contributes factor 1)
    <570, "190b1">,    // 11: genus 4  (d = 190)
    <462, "77a1">,     // 12: genus 3  (d = 77; 3 contributes factor 1)
    <285, "57a1">,     // 13: genus 2, 2 exceptional points   (d = 57)
    <310, "155c1">,    // 14: genus 3, exceptional point      (d = 155)
    <399, "57a1">,     // 15: genus 4, 4 exceptional points   (d = 57)
    <318, "318c1">,    // 16: genus 3, own level  (d = M)
    <430, "430a1">,    // 17: genus 3, own level
    <154, "154a1">,    // 18: genus 2, own level
    <285, "285b1">,    // 19: genus 2, own level
    <286, "286c1">,    // 20: genus 2, own level
    <237, "79a1">,     // 21: genus 5  (d = 79)
    <393, "131a1">,    // 22: genus 5  (d = 131)
    <465, "155c1">,    // 23: genus 5  (d = 155)
    <574, "574a1">,    // 24: genus 5, own level
    <163, "163a1">,    // 25: genus 6, own level
    <269, "269a1">,    // 26: genus 6, own level
    <274, "274c1">,    // 27: genus 6, own level
    <291, "291c1">,    // 28: genus 6, own level
    <202, "101a1">,    // 29: genus 4  (d = 101)
    <249, "83a1">,     // 30: genus 3  (d = 83)
    <262, "131a1">,    // 31: genus 4  (d = 131; see also case 44)
    <267, "89a1">,     // 32: genus 4  (d = 89)
    <282, "141d1">,    // 33: genus 3  (d = 141)
    <305, "61a1">,     // 34: genus 4  (d = 61)
    <354, "118a1">,    // 35: genus 4  (d = 118)
    <395, "79a1">,     // 36: genus 4  (d = 79)
    <426, "142b1">,    // 37: genus 4  (d = 142)
    <429, "143a1">,    // 38: genus 3  (d = 143)
    <201, "201a1">,    // 39: genus 4, own level
    <214, "214b1">,    // 40: genus 4, own level
    <219, "219a1">,    // 41: genus 4, own level
    <254, "254c1">,    // 42: genus 4, own level
    <258, "258a1">,    // 43: genus 3, own level
    <262, "262b1">,    // 44: genus 4, own level
    <434, "434a1">,    // 45: genus 4, own level
    <402, "201a1">,    // 46: genus 5  (d = 201, the prime 2 contributes factor 1)
    <438, "219a1">,    // 47: genus 5  (d = 219, likewise)
    <185, "185c2">     // 48: genus 3, own level; |C| = 2, so the target is
                       //     E_f/C = 185c2, not the optimal curve 185c1
];

load "scripts/cm_terms_overrides.m";

// Returns the SweepCMFibers rows (empty list for the other modes) plus a
// display label for the target of pi, so the driver can print one grand
// summary across every case at the very end. The display label is the Cremona
// label, never "X_0(d)*": the two coincide only when that quotient has genus
// 1, so printing "X_0(d)*" in general would be false.
function DoCase(M, Elabel : do_fibersearch := false, do_ramified := false, do_cuspfiber := false, B := 100000)
    printf "\n#################### M = %o, target = %o ####################\n", M, Elabel;
    // cache_prec must be raised (not just cm_terms) for the same reason
    // documented at cm_terms_override above: a cache hit hands CMFiberSetup
    // an already-materialized, fixed-precision series list it cannot boost,
    // so the star-forms cache itself has to be built with enough terms.
    // cm_terms_override is keyed on the top level M.
    ct := IsDefined(cm_terms_override, M) select cm_terms_override[M] else 3000;
    pi, X, E, fs, Sstar, c := BuildStarCover(M, Elabel : cache_prec := ct);
    printf "X_0(%o)* = %o\n", M, X;
    printf "E = %o (%o)\n", aInvariants(E), CremonaReference(E);
    // The target is the named curve.  It is X_0(M)* itself only when that
    // quotient has genus 1; naming it "X_0(M)*" in general would be false.
    target_label := Elabel;
    if do_fibersearch then
        _ := FiberPointSearch(pi, X, E, fs, Sstar, M : B := B, cm_terms := ct);
        return [* *], target_label;
    end if;
    if do_ramified then
        _ := RamifiedFibers(pi, X, E, fs, Sstar, M : B := B, cm_terms := ct);
        return [* *], target_label;
    end if;
    if do_cuspfiber then
        _ := RunCuspFiber(pi, X, E, fs, Sstar, M : B := B, cm_terms := ct);
        return [* *], target_label;
    end if;
    return SweepCMFibers(pi, X, E, fs, Sstar, M : B := B, cm_terms := ct), target_label;
end function;

searchB := assigned bigB select 10^6 else 100000;
do_fibersearch := assigned fibersearch;
do_ramified := assigned ramified;
do_cuspfiber := assigned cuspfiber;
// <M, Elabel, rows, target_label> per case, gathered so a single conglomerate
// summary can be printed after every case has run, instead of hunting through
// each case's own SWEEP SUMMARY block.
all_rows := [* *];

if assigned caseidx then
    idx := StringToInteger(caseidx);
    entry := cases[idx];
    rows, target_label := DoCase(entry[1], entry[2] : do_fibersearch := do_fibersearch, do_ramified := do_ramified, do_cuspfiber := do_cuspfiber, B := searchB);
    Append(~all_rows, <entry[1], entry[2], rows, target_label>);
else
    for entry in cases do
        rows, target_label := DoCase(entry[1], entry[2] : do_fibersearch := do_fibersearch, do_ramified := do_ramified, do_cuspfiber := do_cuspfiber, B := searchB);
        Append(~all_rows, <entry[1], entry[2], rows, target_label>);
    end for;
end if;

if not (do_fibersearch or do_ramified or do_cuspfiber) then
    printf "\n\n==================== GRAND SUMMARY (all cases) ====================\n";
    for t in all_rows do
        M, Elabel, rows, target_label := Explode(t);
        if #rows eq 0 then
            printf "X_0(%o)* -> %o: no residual rational points found\n", M, target_label;
        else
            for r in rows do
                if r[1] eq 0 then
                    printf "X_0(%o)* -> %o: CUSP fiber |--> Q = %o; RESIDUAL POINT %o [%o]\n",
                        M, target_label, r[2], r[3], r[4];
                elif r[1] eq 1 then
                    printf "X_0(%o)* -> %o: RATIONAL-POINT fiber |--> Q = %o; RESIDUAL POINT %o [%o]\n",
                        M, target_label, r[2], r[3], r[4];
                else
                    printf "X_0(%o)* -> %o: D = %o: CM points |--> Q = %o; THIRD POINT %o [%o]\n",
                        M, target_label, r[1], r[2], r[3], r[4];
                end if;
            end for;
        end if;
    end for;
end if;

quit;
