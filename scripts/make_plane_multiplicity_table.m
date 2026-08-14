// scripts/make_plane_multiplicity_table.m
//
// Builds the supplementary table of ALL confirmed collinearity planes through
// each exceptional point in genus 3 and 4, and emits it as LaTeX.
//
// Why this exists: the Collinearity column of the two exceptional-point tables
// records one witnessing plane per level.  Which one it records turned out to
// depend on eval_prec -- at the default 3000, N = 178 reported "10 planes (1
// with algebraic CM match)"; at 7000 the same 10 planes gave 5 confirmed
// matches.  The geometry never changed, only the CM identification of the
// degree-2 components.  So the published column was selecting on a numerical
// artifact.  This script re-runs every level at 7000 and reports the full set.
//
// Run from the repo root:
//     magma scripts/make_plane_multiplicity_table.m
// or inside a session:
//     load "scripts/make_plane_multiplicity_table.m";
//
// Output: a progress line per level, then a LaTeX tabular on stdout.
//
// Runtime: a fresh build at eval_prec 7000 with confirm_deg2 for all 14
// levels.  Hours, not minutes.  Each level prints as it completes, so a
// partial run is still usable.

load "src/AtkinLehner.m";

EVAL_PREC     := 7000;
MAX_CLASS_NUM := 8;   // see the warning in tests/test_exceptional_tables.m
                      // before raising this
CUSP          := 0;   // sentinel from src/labeling.m

GENUS := AssociativeArray();
for N in [178, 183, 246, 290, 310, 318, 329, 430, 455, 510] do GENUS[N] := 3; end for;
for N in [137, 311, 370, 399]                                do GENUS[N] := 4; end for;
LEVELS := [178, 183, 246, 290, 310, 318, 329, 430, 455, 510, 137, 311, 370, 399];

// The plane recorded in the paper's tables, for marking in the output.
PUBLISHED := AssociativeArray();
PUBLISHED[178] := {Integers()| -388, -40};
PUBLISHED[183] := {Integers()| -483, -75};
PUBLISHED[246] := {Integers()| -264, -168};
PUBLISHED[290] := {Integers()| -64, -24};
PUBLISHED[310] := {Integers()| -55, CUSP};
PUBLISHED[318] := {Integers()| -852, -372};
PUBLISHED[329] := {Integers()| -52, -35};
PUBLISHED[430] := {Integers()| -220, -120};
PUBLISHED[455] := {Integers()| -819, -195};
PUBLISHED[510] := {Integers()| -480, CUSP};
PUBLISHED[137] := {Integers()| -32, -11, -4, CUSP};
PUBLISHED[311] := {Integers()| -232, -123, -19};
PUBLISHED[370] := {Integers()| -340, -260, -16, CUSP};
PUBLISHED[399] := {Integers()| -1995, -483, -147, -84};

// ---------------------------------------------------------------------------
// A discriminant set as LaTeX, cusp rendered as the word.  Sorted descending
// (least negative last) so the rows read like the paper's.
// ---------------------------------------------------------------------------
function DiscsToTeX(S)
    ds := Sort([d : d in S | d ne CUSP]);
    parts := [Sprintf("$%o$", d) : d in ds];
    if CUSP in S then Append(~parts, "cusp"); end if;
    return Join(parts, ", ");
end function;

// ---------------------------------------------------------------------------
// All confirmed planes for one level.  Field 5 of a plane tuple is the
// "matched" flag printed by LabelAndAnalyze; field 4 is the confirmed
// discriminant set; field 3 the component degrees.
// ---------------------------------------------------------------------------
function ConfirmedPlanes(N)
    fresh := check_exceptional_example(N : eval_prec := EVAL_PREC, UseCache := false);
    error if #fresh eq 0, Sprintf("N = %o: no exceptional point found", N);
    res := analyze_exceptional(fresh : max_class_num := MAX_CLASS_NUM,
                                       confirm_deg2 := true);
    planes := res[1][3];
    out := [* *];
    for p in planes do
        if p[5] then
            Append(~out, <p[4], p[3], p[6]>);   // discs, comp degrees, inconclusive
        end if;
    end for;
    return out;
end function;

// ---------------------------------------------------------------------------
rows := [* *];
for N in LEVELS do
    printf "=== N = %o (genus %o) ===\n", N, GENUS[N];
    t0 := Cputime();
    cp := ConfirmedPlanes(N);
    printf "  %o confirmed plane(s)  (%o s)\n", #cp, Cputime(t0);
    for e in cp do
        tag := (e[1] eq PUBLISHED[N]) select "  <- published row" else "";
        printf "    %o   comps = %o%o\n", e[1], e[2], tag;
        if #e[3] gt 0 then
            printf "      still inconclusive at prec %o: %o\n", EVAL_PREC, e[3];
        end if;
    end for;
    Append(~rows, <N, GENUS[N], cp>);
end for;

// ---------------------------------------------------------------------------
printf "\n\n%%%% ---- LaTeX, paste into the paper ----\n\n";
printf "\\begin{table}[ht]\n\\centering\n\\small\n";
printf "\\begin{tabular}{ccl}\n\\toprule\n";
printf "\\textbf{Level} & \\textbf{Genus} & \\textbf{Special hyperplanes through the exceptional point} \\\\\n";
printf "\\midrule\n";
for r in rows do
    N, g, cp := Explode(r);
    first := true;
    for e in cp do
        star := (e[1] eq PUBLISHED[N]) select "$^{\\dagger}$" else "";
        if first then
            printf "$%o$ & $%o$ & %o%o \\\\\n", N, g, DiscsToTeX(e[1]), star;
            first := false;
        else
            printf "     &     & %o%o \\\\\n", DiscsToTeX(e[1]), star;
        end if;
    end for;
    printf "\\addlinespace\n";
end for;
printf "\\bottomrule\n\\end{tabular}\n";
printf "\\caption{Every confirmed special hyperplane through an exceptional\n";
printf "point of $X_0^*(N)$ in genus $3$ and $4$, computed at\n";
printf "$\\texttt{eval\\_prec} = %o$.  Each row lists the CM discriminants (and\n", EVAL_PREC;
printf "the cusp, where it occurs) of the special divisor cut out.  A dagger\n";
printf "marks the plane recorded in Tables~\\ref{tab:exceptional_points_genus_3}\n";
printf "and~\\ref{tab:exceptional_points_genus_4}.}\n";
printf "\\label{tab:all_planes}\n\\end{table}\n";
