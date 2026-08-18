// scripts/pointsearch_g8.m
//
// Run directly, one shard at a time (from the repo root; all args optional):
//   magma -b B:=100000 shard:=1 nshards:=8 scripts/pointsearch_g8.m
// Each shard writes outputs/special_vs_found_g8_sqfree_B<B>_shard<shard>.txt
// (staged as .part until the shard completes). Concatenate shards when all
// finish, or just run scripts/run_pointsearch_g8.sh, which launches all
// NSHARDS shards in parallel and does the concatenation for you.
//
// Point search on the 32 squarefree genus-8 X0(N)* models.
// Nonsingular:=true skips PointSearch's singularity-check preprocessing, which
// blows up on 15 quadrics in P^7 (308s at N=293, unbounded at the omega=4 levels).
// Legitimate here: canonical models of non-hyperelliptic curves are smooth
if not assigned B then B := "100000"; end if;
if not assigned shard then shard := "1"; end if;
if not assigned nshards then nshards := "1"; end if;
bound := StringToInteger(B);
sh := StringToInteger(shard);
ns := StringToInteger(nshards);

load "data/genus8_models.m";
Ns := Sort(Setseq(Keys(models)));

System("mkdir -p outputs");
outfile := Sprintf("outputs/special_vs_found_g8_sqfree_B%o_shard%o.txt", B, sh);
part := outfile cat ".part";
System("rm -f " cat part);
fprintf part, "# Squarefree genus-8 X0(N)*: PointSearch(B=%o, Nonsingular:=true) found vs stored special points (shard %o/%o)\n", bound, sh, ns;
fprintf part, "# N  found  special  diff  search_s\n";

for i in [1..#Ns] do
    if ((i - 1) mod ns) + 1 ne sh then continue; end if;
    N := Ns[i];
    t0 := Cputime();
    pts := PointSearch(models[N]`curve, bound : Nonsingular := true);
    pts := Setseq(Seqset(pts));
    sp := models[N]`special_points;
    fprintf part, "%o  %o  %o  %o  %o\n", N, #pts, sp, #pts - sp, RealField(4)!(Cputime() - t0);
    printf "N=%o done: found=%o special=%o (%o s)\n", N, #pts, sp, Cputime() - t0;
end for;

System("mv " cat part cat " " cat outfile);
quit;
