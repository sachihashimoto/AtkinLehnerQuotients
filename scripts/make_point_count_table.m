// scripts/make_point_count_table.m
//
// Regenerates data/x0star_point_counts.txt: for every squarefree level N with
// X_0(N)* of genus 5 to 20, the genus, the level, the number of rational cusps
// and CM points, and the rational CM discriminants with the number of points
// at each. This is the data behind the paper's by-genus distribution figure
// (scripts/plot_point_distribution.py).
//
// Run from the repository root (about 5 minutes):
//   magma -b scripts/make_point_count_table.m | grep '^@@DATA@@' \
//       | sed 's/^@@DATA@@ //' > data/x0star_point_counts.txt
//
// Each data line is:  <genus> <N> <points> <disc>:<count> ...
// The @@DATA@@ prefix separates these lines from the library's own printing.
load "src/AtkinLehner.m";
for g in [5..20] do
    for pair in SquarefreeStarQuotientsOfGenusExactly(g) do
        N := pair[1];
        total, cm_pts := count_special_points_X0Nstar(N);
        printf "@@DATA@@ %o %o %o", g, N, total;
        for d in Reverse(Sort(Setseq(Keys(cm_pts)))) do
            printf " %o:%o", d, cm_pts[d];
        end for;
        printf "\n";
    end for;
end for;
exit;
