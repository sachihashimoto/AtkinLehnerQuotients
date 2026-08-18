// scripts/pointsearch_examples.m
//
// Run directly (from the repo root; Np is required):
//   magma -b Np:=290 B:=100000000 scripts/pointsearch_examples.m
// Writes outputs/pointsearch_example_Np<Np>_B<B>.txt
//
// Point search on the six X0(Np)* levels from the "CM points in the same fiber"
// example: Np in {290, 154, 455, 590, 246, 286}.
//
// Non-hyperelliptic levels (290,455,246 genus 3; 590 genus 6) use canonical
// (smooth) models, so PointSearch is called with Nonsingular:=true to skip the
// singularity-check Groebner preprocessing (same justification as scripts/pointsearch_g8.m).
// The two genus-2 levels (154,286) are hyperelliptic and use the fast
// Points(Cint : Bound := B) path via PointsOriginalModel.

load "src/AtkinLehner.m";

if not assigned Np then error "set Np:=<level>"; end if;
if not assigned B  then B := "100000000"; end if;
level := StringToInteger(Np);
bound := StringToInteger(B);
eval_prec := 3000;

System("mkdir -p outputs");
outfile := Sprintf("outputs/pointsearch_example_Np%o_B%o.txt", level, bound);
part := outfile cat ".part";
System("rm -f " cat part);

g := GenusStarQuotient(level);
hyp := IsHyperellipticX0Nstar(level);
printf "Np=%o genus=%o hyperelliptic=%o  B=%o\n", level, g, hyp, bound;

t0 := Cputime();
if hyp then
    C, _, _ := XZeroNstarWithForms_hyperelliptic(level, eval_prec);
    pts := PointsOriginalModel(C, bound);
else
    X, _, _ := XZeroNstarWithForms(level, eval_prec);
    pts := PointSearch(X, bound : Nonsingular := true);
end if;
pts := Setseq(Seqset(pts));
search_s := Cputime() - t0;

special, cm_pts := count_special_points_X0Nstar(level);
found := #pts;

fprintf part, "# X0(%o)* point search, genus %o, hyperelliptic %o\n", level, g, hyp;
fprintf part, "# B=%o  found=%o  special=%o  diff=%o  search_s=%o\n",
    bound, found, special, found - special, RealField(5)!search_s;
fprintf part, "# points:\n";
for P in pts do
    fprintf part, "%o\n", P;
end for;
fprintf part, "# special CM discriminants and multiplicities:\n";
for d in Sort(Setseq(Keys(cm_pts))) do
    fprintf part, "#   D=%o  mult=%o\n", d, cm_pts[d];
end for;

System("mv " cat part cat " " cat outfile);
printf "Np=%o done: found=%o special=%o diff=%o (%o s)\n",
    level, found, special, found - special, RealField(5)!search_s;
quit;
