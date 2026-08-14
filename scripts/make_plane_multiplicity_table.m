// scripts/make_plane_multiplicity_table.m
//
// Builds the supplementary table of ALL confirmed collinearity planes through
// each exceptional point in genus 3 and 4, and emits it as LaTeX.
//
// Why this exists: the Collinearity column of the two exceptional-point tables
// records one witnessing plane per level.  The planes that are algebraic matches depend on the eval_prec.
// At the default 3000, N = 178 reported "10 planes (4 with algebraic CM match)"; 
// at 7000 the same 10 planes gave 5 confirmed
// matches (the plane 2*z[2] - z[3]=0  containing the cusp and unconfirmed CM points
// now has a confirmed CM point at higher precision). 
// The geometry does not change, only the confidence in the CM identification of the
// degree-2 components: at lower precision we are not able to select between -32 and -64.
//  This script re-runs every level at 7000 and reports the full set.
//
// Run from the main folder of the repository:
//     magma scripts/make_plane_multiplicity_table.m
// or inside a session:
//     load "scripts/make_plane_multiplicity_table.m";
//
// Output: a progress line per level, then a LaTeX tabular on stdout.
//
// Runtime: a fresh build at eval_prec 7000 with confirm_deg2 for all 14
// levels takes about 10 minutes (measured: 583 s wall, 371 MB peak).  Each
// level takes 10-100 s and prints as it completes, so a partial run is still
// usable.

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
// Right-pad to a fixed width, so the emitted .tex source lines up by column.
// ---------------------------------------------------------------------------
function Pad(s, w)
    t := s;
    while #t lt w do t cat:= " "; end while;
    return t;
end function;

// ---------------------------------------------------------------------------
// Flatten to one printable line per plane.  A line carries the level and genus
// only when it opens that level's block; continuation lines leave both blank.
// starts records the line index opening each block, so the table can be split
// into two halves without cutting a level in two.
// ---------------------------------------------------------------------------
lines  := [];
starts := [];
for r in rows do
    N, g, cp := Explode(r);
    Append(~starts, #lines + 1);
    for i in [1..#cp] do
        e    := cp[i];
        star := (e[1] eq PUBLISHED[N]) select "$^{\\dagger}$" else "";
        cell := Sprintf("%o%o", DiscsToTeX(e[1]), star);
        if i eq 1 then
            Append(~lines, <Sprintf("$%o$", N), Sprintf("$%o$", g), cell>);
        else
            Append(~lines, <"", "", cell>);
        end if;
    end for;
end for;

// The block boundary closest to halving the table; ties go to the later one,
// filling the left half first.
half  := Ceiling(#lines / 2);
split := 1;
for s in starts do
    if Abs(s - 1 - half) le Abs(split - 1 - half) then split := s; end if;
end for;
left  := [lines[i] : i in [1 .. split - 1]];
right := [lines[i] : i in [split .. #lines]];
blank := <"", "", "">;

// Both halves print against one set of rules, so they end flush by
// construction.  That rules out \addlinespace between levels: a gap belongs to
// a whole row, and the level boundaries of the two halves do not coincide.
printf "\n\n%%%% ---- LaTeX, paste into the paper ----\n\n";
printf "\\begin{table}[ht]\n\\centering\n\\small\n";
printf "\\setlength{\\tabcolsep}{5pt}\n";
printf "\\begin{tabular}{ccl@{\\hspace{2.5em}}ccl}\n\\toprule\n";
printf "$N$ & $g$ & Collinearity & $N$ & $g$ & Collinearity \\\\\n";
printf "\\midrule\n";
for i in [1 .. Max(#left, #right)] do
    L := (i le #left)  select left[i]  else blank;
    R := (i le #right) select right[i] else blank;
    printf "%o & %o & %o & %o & %o & %o \\\\\n",
           Pad(L[1], 5), Pad(L[2], 3), Pad(L[3], 26),
           Pad(R[1], 5), Pad(R[2], 3), R[3];
end for;
printf "\\bottomrule\n\\end{tabular}\n";
printf "\\caption{Every confirmed special hyperplane through an exceptional\n";
printf "point of $X_0^*(N)$ in genus $3$ and $4$, computed at\n";
printf "$\\texttt{eval\\_prec} = %o$.  Each collinearity is listed by the CM\n", EVAL_PREC;
printf "discriminants (and the cusp, where it occurs) of the special divisor\n";
printf "cut out.  A dagger marks the plane recorded in\n";
printf "Tables~\\ref{tab:exceptional_points_genus_3}\n";
printf "and~\\ref{tab:exceptional_points_genus_4}.}\n";
printf "\\label{tab:all_planes}\n\\end{table}\n";
