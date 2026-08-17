// scripts/check_automorphisms.m
//
// Verifies the "Automorphism" column of the paper's genus 3 and 4 exceptional
// point tables.  That column is the one thing tests/test_exceptional_tables.m
// explicitly does not reproduce, so it is currently unchecked.
//
// For each level, the claim being tested is: some non-identity automorphism of
// X_0^*(N) carries a special point (rational CM point or the cusp) to the
// exceptional point.  That is what "explained by an automorphism" means in the
// paper -- not merely that Aut is nontrivial.
//
// Run from the repo root:
//     magma scripts/check_automorphisms.m
// or inside a session:
//     load "scripts/check_automorphisms.m";
//
// Runtime: AutomorphismGroup on a genus 3 plane quartic over Q is usually
// seconds; genus 4 canonical curves in P^3 can be much slower.  Levels are
// processed one at a time and each prints as it finishes, so a slow level does
// not hide the earlier results.

load "src/AtkinLehner.m";

// Expected values, transcribed from the paper's tables.  Genus 4's N = 370
// row was corrected from (-136, -84, -16) after the repo's own run; see the
// collinearity column of tests/test_exceptional_tables.m.
EXPECTED := AssociativeArray();
EXPECTED[178] := true;   EXPECTED[183] := true;   EXPECTED[246] := true;
EXPECTED[290] := true;   EXPECTED[310] := false;  EXPECTED[318] := true;
EXPECTED[329] := false;  EXPECTED[430] := true;   EXPECTED[455] := true;
EXPECTED[510] := true;
EXPECTED[137] := false;  EXPECTED[311] := false;  EXPECTED[370] := true;
EXPECTED[399] := false;

GENUS3 := [178, 183, 246, 290, 310, 318, 329, 430, 455, 510];
GENUS4 := [137, 311, 370, 399];

MAX_CLASS_NUM := 8;

// ---------------------------------------------------------------------------
// For one level: build the model, label the rational points, compute Aut, and
// test whether any non-identity automorphism moves a special point onto an
// exceptional point.
//
// Returns <ok, aut_order, witnesses>, where witnesses is a list of
// <special_idx, disc, exc_idx> triples (disc = 0 for the cusp).
// ---------------------------------------------------------------------------
function AutomorphismExplains(N : B := 1000, eval_prec := 3000)
    interesting := check_exceptional_example(N : B := B, eval_prec := eval_prec);
    entry  := interesting[1];
    error if entry[2] eq 0,
        Sprintf("N = %o: no exceptional point found", N);
    rats   := entry[3];
    X      := entry[4];
    fs     := entry[5];
    cm_pts := entry[7];

    // analyze := false gives the labelling half only: idx -> disc, no plane
    // search and no Degree2Points.  That is all we need here.
    exc, _, _, fail, idx_to_disc := LabelAndAnalyze(N, X, fs, rats, Keys(cm_pts)
        : max_class_num := MAX_CLASS_NUM, analyze := false);
    error if fail ne "", Sprintf("N = %o: labelling failed: %o", N, fail);

    special := [ i : i in [1..#rats] | i notin exc ];

    // AutomorphismGroup(X) handles both the hyperelliptic and canonical
    // models uniformly; there is no separate hyperelliptic-specific path.
    A := AutomorphismGroup(X);

    witnesses := [* *];
    for a in A do
        if IsIdentity(a) then continue; end if;
        for i in special do
            im := a(rats[i]);
            for e in exc do
                if im eq rats[e] then
                    d := IsDefined(idx_to_disc, i) select idx_to_disc[i] else -1;
                    Append(~witnesses, <i, d, e>);
                end if;
            end for;
        end for;
    end for;

    return #witnesses gt 0, #A, witnesses;
end function;

// ---------------------------------------------------------------------------
procedure Report(levels, g)
    printf "\n=== genus %o ===\n", g;
    printf "%-6o %-10o %-8o %-8o %o\n",
           "Level", "#Aut", "computed", "paper", "witnesses";
    for N in levels do
        ok, nA, w := AutomorphismExplains(N);
        want := EXPECTED[N];
        flag := (ok eq want) select "" else "   <-- DISAGREES WITH PAPER";
        printf "%-6o %-10o %-8o %-8o %o%o\n",
               N, nA, ok select "yes" else "no", want select "yes" else "no",
               #w gt 0 select w else [* *], flag;
    end for;
end procedure;

Report(GENUS3, 3);
Report(GENUS4, 4);

printf "\nNote: #Aut is the order of the automorphism group over Q of the model\n";
printf "returned by XZeroNstar.  A level can have nontrivial Aut without any\n";
printf "automorphism explaining its exceptional point, which is what the\n";
printf "'computed' column tests.\n";
