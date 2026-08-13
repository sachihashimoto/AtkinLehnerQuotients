// scripts/make_exceptional_table.m
//
// Run directly (from the repo root, ~20 min):
//     magma -b scripts/make_exceptional_table.m
// Discovery mode (re-derives the discs instead of just verifying; slower):
//     magma -b discover:=1 scripts/make_exceptional_table.m
// Include exceptional points whose fiber partner is not CM:
//     magma -b only_cm:=0 scripts/make_exceptional_table.m
// Fast mode (release-gate scale, ~1 min; see note near the bottom about
// resetting data/starmodels/ before and after each run):
//     magma -b fast:=1 scripts/make_exceptional_table.m
//
// Reproduce the table of exceptional points of X_0(M)* lying in a fiber of
// the triple cover X_0(M)* -> E together with CM points.  M is the top level
// and d = Conductor(E) the newform level, so the target is X_0(d)* when
// d < M and the own-level quotient when d = M:
//
//   M    genus  d    M/d  D          exceptional point
//   154  2      77   2    -63        (-3 : -77 : 2)        quadratic CM pair
//   154  2      new (154a1)  -28     (-1 : -56 : 3)        rational CM pt, doubled
//   285  2      57   5    -219       (-3/2 : -57/16 : 1)   quadratic CM pair
//   285  2      new (285b1)  -15     (3 : -12 : 1)         rational CM pt, doubled
//   286  2      143  2    -39        (5/2 : -143/16 : 1)   quadratic CM pair
//   286  2      new (286c1)  -220    (5/2 : 143/16 : 1)    quadratic CM pair
//   246  3      123  2    -228       (1/4 : 1/2 : 1)       rational CM pt, doubled
//   310  3      155  2    -520       (6 : -2 : 1)          rational CM pt, doubled
//   318  3      new (318c1)  -15     (8 : -2 : 1)          rational CM pt, doubled
//   430  3      new (430a1)  -280    (3/4 : 1/2 : 1)       rational CM pt, doubled
//   399  4      57   7    -75, -483  (5 : -3/2 : 1 : 0)    two rational CM pts
//
// "new" rows use the triple cover to the NEW elliptic quotient E of conductor
// M (all AL eigenvalues +1, modular degree 3*2^omega), i.e. d = M and so
// M/d = 1, which is what the printing below keys the "new" marker on.  The 290
// and 455 exceptional points are in no triple-cover CM fiber (no own-level map
// exists there, and their X_0(d)* fiber partners are non-CM).
//
// For each cover: builds the map, finds and labels the small rational points
// (src/point_search.m and src/labelling.m), takes each exceptional (non-CM, non-cusp)
// point P, pulls back the fiber through P, and identifies the other points
// of the fiber.  Quadratic places are matched numerically against the CM
// points of the known discriminants listed below (fast verification); with
// discover:=1 they are additionally matched against every discriminant whose
// CM points are degree-2 points of X_0(M)* (Degree2Points, Shimura
// reciprocity), so the table can be re-derived without prior knowledge.
// Rational places carry their CM/cusp labels from the point labelling.
//
// Fast mode restricts to two cases, one from each TripleCoverMap_* branch:
// <246, "123b1"> (canonical) and <286, "143a1"> (hyperelliptic).  Both maps
// are cached, so fast mode loads rather than re-derives them; to make the
// triple-cover search genuinely run, delete those two map_*.m files first:
//     rm data/starmodels/map_246_123b1.m data/starmodels/map_286_143a1.m
// fast:=1 then rewrites them, with identical content.

load "src/triple_covers.m";
load "scripts/cm_terms_overrides.m";
SetSeed(1);

// <top level M, Cremona label of the target E^C_f, known partner discs>: all
// triple covers X_0(M)* -> E whose top curve has exceptional points (the other
// known covers, 570 x2, 590, 910, 462, 798, 870, have none among their small
// rational points).  The <M, Elabel> pair is the same key
// scripts/run_triple_covers.m's `cases` table uses, and every entry here
// appears there too.
// cm_terms_override (scripts/cm_terms_overrides.m) supplies any needed
// per-level bump to CMFiberSetup's cm_terms, shared with
// scripts/run_triple_covers.m.
covers := [
    <154, "77a1",  [-63]>,    // X_0(154)* -> X_0(77)*,  genus 2
    <154, "154a1", []>,       // X_0(154)* -> 154a1      (partner: rational CM -28)
    <285, "57a1",  [-219]>,   // X_0(285)* -> X_0(57)*,  genus 2
    <285, "285b1", []>,       // X_0(285)* -> 285b1      (partner: rational CM -15)
    <286, "143a1", [-39]>,    // X_0(286)* -> X_0(143)*, genus 2
    <286, "286c1", [-220]>,   // X_0(286)* -> 286c1
    <246, "123b1", []>,       // X_0(246)* -> X_0(123)*, genus 3 (partner: rational CM -228)
    <290, "58a1",  []>,       // X_0(290)* -> X_0(58)*,  genus 3 (partner: non-CM pair)
    <310, "155c1", []>,       // X_0(310)* -> X_0(155)*, genus 3 (partner: rational CM -520)
    <455, "91a1",  []>,       // X_0(455)* -> X_0(91)*,  genus 3 (partner: non-CM pair)
    <399, "57a1",  []>,       // X_0(399)* -> X_0(57)*,  genus 4 (partners: rational CM -75, -483)
    <318, "318c1", []>,       // X_0(318)* -> 318c1,     genus 3 (partner: rational CM -15)
    <430, "430a1", []>        // X_0(430)* -> 430a1,     genus 3 (partner: rational CM -280)
];

do_discover := assigned discover and discover eq "1";
show_all := assigned only_cm and only_cm eq "0";
do_fast := assigned fast and fast eq "1";

// fast subset: one case per TripleCoverMap_* branch: (246, "123b1")
// canonical and (286, "143a1") hyperelliptic (IsHyperellipticX0Nstar(246) =
// false, IsHyperellipticX0Nstar(286) = true).  Both have a map_*.m cache
// entry, so this exercises the load path, not the search; delete
// data/starmodels/map_246_123b1.m and map_286_143a1.m to force a real build.
if do_fast then
    covers := [c : c in covers | <c[1], c[2]> in {<246, "123b1">, <286, "143a1">}];
end if;

all_rows := [* *];
for cover in covers do
    // cache_prec = cm_terms: the star-forms cache (data/starmodels/starforms_*.m)
    // is a materialized, fixed-precision series list; CMFiberSetup's cm_terms
    // can only "boost" a live ModSym object, not a cache hit, so asking for
    // more CM-labelling terms than the cache holds silently gets nothing
    // (see src/triple_covers.m CMFiberSetup's cached branch). Raising
    // cache_prec forces BuildTripleCover to regenerate the cache with enough
    // terms up front.
    ct := IsDefined(cm_terms_override, cover[1]) select cm_terms_override[cover[1]] else 3000;
    rows := ExceptionalFiberRows(cover[1], cover[2] :
        known_discs := cover[3], discover := do_discover, cm_terms := ct, cache_prec := ct);
    for r in rows do Append(~all_rows, r); end for;
end for;

// short fiber-type tag from the partner description
function FiberType(partner_str, ndiscs)
    if Position(partner_str, "quadratic CM pair") gt 0 then
        return "degree-2 CM point";
    elif Position(partner_str, "mult 2") gt 0 then
        return "ramified rational CM";
    elif ndiscs ge 2 then
        return "split rational CM";
    else
        return "other";
    end if;
end function;

printf "\n\n================== EXCEPTIONAL POINTS IN CM FIBERS ==================\n";
printf "%-5o %-6o %-5o %-4o %-8o %-14o %-22o %-22o %o\n", "M", "genus", "d", "M/d", "E", "D", "exceptional pt", "fiber type", "CM partner in fiber";
for r in all_rows do
    if not r[8] and not show_all then continue; end if;
    printf "%-5o %-6o %-5o %-4o %-8o %-14o %-22o %-22o %o\n",
        r[1], r[2],
        r[4] eq 1 select "-" else Sprint(r[3]),
        r[4] eq 1 select "new" else Sprint(r[4]),
        r[9],
        #r[7] gt 0 select Join([Sprint(d) : d in r[7]], ",") else "-",
        r[5], FiberType(r[6], #r[7]), r[6];
end for;

printf "\n---------------------------- LaTeX rows ----------------------------\n";
for r in all_rows do
    if not r[8] and not show_all then continue; end if;
    pt := SubstituteString(r[5], " : ", ":");
    Dstr := #r[7] gt 0 select Join([Sprint(d) : d in r[7]], ",\\ ") else "---";
    printf "$%o$ & $%o$ & %o & %o & \\texttt{%o} & $%o$ & $%o$ & %o \\\\\n",
        r[1], r[2],
        r[4] eq 1 select "---" else "$" cat Sprint(r[3]) cat "$",
        r[4] eq 1 select "new" else "$" cat Sprint(r[4]) cat "$",
        r[9], Dstr, pt, FiberType(r[6], #r[7]);
end for;
printf "---------------------------------------------------------------------\n";
printf "(rows: M & genus & d & M/d & E & D & exceptional point & fiber type)\n";
quit;
