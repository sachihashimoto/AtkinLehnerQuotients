// scripts/classify_triple_covers.m
//
// Writes the complete classification of degree-3 covers X_0(N)* -> E
// (N squarefree) to data/triple_cover_classification.txt.
//
// The classification itself lives in src/classify_covers.m
// (ClassifyTripleCovers), which states and proves the finiteness bound and
// documents the degree formula.  This script only formats the result, so that
// tests/test_triple_cover_table.m can pin the same function's output against
// the table in the paper without either one reimplementing the sweep.
//
// Run:  magma -b scripts/classify_triple_covers.m > outputs/classify.log 2>&1

load "src/triple_covers.m";

function Pad(s, n)
    t := Sprint(s);
    while #t lt n do t cat:= " "; end while;
    return t;
end function;

rows := ClassifyTripleCovers(: verbose := true);

printf "\n== %o covers ==\n", #rows;
out := "Complete classification of degree-3 covers of X_0(N)* (N squarefree).\n";
out cat:= "Reproduce with:  magma -b scripts/classify_triple_covers.m\n";
out cat:= "Pinned against the paper's table by tests/test_triple_cover_table.m\n\n";
out cat:= "deg(pi_f) = delta_f * prod_{l | N/d} (l + 1 + a_l(f)) = 3, where f is a\n";
out cat:= "newform of level d | N with rational coefficients and all Atkin-Lehner\n";
out cat:= "eigenvalues +1, C := im(c) subset E_f(Q)[2] is the AL translation subgroup,\n";
out cat:= "and delta_f = |C| * deg(phi_d) / 2^omega(d).  The cover lands on\n";
out cat:= "E^C_f = E_f/C, which differs from E_f exactly when |C| > 1.\n";
out cat:= "'factors' lists (l, l + 1 + a_l(f)) for each l | N/d; each row satisfies\n";
out cat:= "3 = delta * product of those factors.\n\n";
header := "  " cat Pad("N", 7) cat Pad("d", 7) cat Pad("E^C_f", 9) cat Pad("E_f", 9)
          cat Pad("|C|", 5) cat Pad("delta", 7) cat Pad("factors", 24) cat "g";
out cat:= header cat "\n";
printf "%o\n", header;
for r in rows do
    fs := #r[8] eq 0 select "-"
          else &cat[Sprintf("(%o,%o)", t[1], t[2]) : t in r[8]];
    line := "  " cat Pad(r[2], 7) cat Pad(r[3], 7) cat Pad(r[4], 9) cat Pad(r[5], 9)
            cat Pad(r[6], 5) cat Pad(r[7], 7) cat Pad(fs, 24) cat Sprint(r[1]);
    out cat:= line cat "\n";
    printf "%o\n", line;
end for;

targets := {r[4] : r in rows};
summary := Sprintf("\n%o covers on %o distinct curves over %o distinct levels; maximum genus %o.\n",
    #rows, #targets, #{r[2] : r in rows}, Max([r[1] : r in rows]));
out cat:= summary;
printf "%o", summary;

// Stage to a temp file and move: never overwrite the only copy in place.
tmp := "data/triple_cover_classification.txt.tmp" cat Sprint(Random(10^9));
Write(tmp, out : Overwrite := true);
System("mv " cat tmp cat " data/triple_cover_classification.txt");
printf "wrote data/triple_cover_classification.txt (%o rows)\n", #rows;
quit;
