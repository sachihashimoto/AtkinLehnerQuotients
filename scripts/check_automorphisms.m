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
// Method: rather than compute the full automorphism group with Magma's
// AutomorphismGroup(Crv) -- which for a canonically embedded (non-
// hyperelliptic) curve has no fast path and can run for well over 17 minutes
// without finishing even the first of the 14 levels below, since none of them
// are hyperelliptic -- this searches directly, for each candidate pair
// (special point, exceptional point), for a single linear automorphism T of
// the ambient P^{n-1} that both preserves the curve's defining ideal and
// sends that special point to that exceptional point.  That is a much
// smaller question than computing the whole group, and resolves in well
// under a second per pair for the genus-3 (single-generator) levels; the
// genus-4 levels, whose defining ideal is a several-dimensional space of
// same-degree forms rather than a complete intersection, take longer (see
// FindLinAutoMappingPoint below for why, and how that case is handled).
//
// This assumes X is canonically embedded (its DefiningPolynomials cut it out
// of a plane/space by an automorphism-equivariant linear action on the
// ambient coordinates), which holds for every non-hyperelliptic level here.
// A hyperelliptic level would need a different search, since its model does
// not carry automorphisms as linear actions on the same ambient coordinates.

load "src/AtkinLehner.m";

// ---------------------------------------------------------------------------
// Targeted linear-automorphism search (see file header for the "why").
//
// gens: SeqEnum of homogeneous polys generating the ideal of X.  These need
// not be a minimal/complete-intersection generating set: if several share a
// degree (e.g. Magma hands back a 5-dimensional space of cubics through the
// N=370 genus-4 model, not two complete-intersection generators), an
// automorphism need only preserve their common SPAN V_d in each degree d,
// not fix each one individually.  Rather than introduce a mixing matrix
// (which blows up the unknown count with the number of generators -- for
// N=370's 5 cubics that made the search over 1000x slower and it still
// didn't finish), that condition is imposed directly and cheaply:
// precompute, once per degree class, a basis of linear functionals
// annihilating V_d (the left null space of the generators' coefficient
// matrix); "phi(g_i) in V_d" is then just those functionals applied to
// phi(g_i)'s coefficient vector, equal to zero -- equations purely in the
// T-unknowns, no per-generator mixing variables needed at all.
//
// n: ambient dimension (rank of the polynomial ring)
// p_from, p_to: SeqEnum[FldRatElt] of length n, homogeneous coordinates.
//
// Returns: found (BoolElt), T (Mtrx over Q with T*p_from proportional to
// p_to and phi_T(gens) = gens as an ideal, or the zero matrix if not found).
// ---------------------------------------------------------------------------
function FindLinAutoMappingPoint(gens, p_from, p_to : verbose := false)
    R := Universe(gens);
    n := Rank(R);
    r := #gens;
    assert #p_from eq n and #p_to eq n;

    degs := [TotalDegree(g) : g in gens];
    uniq_degs := SetToSequence(SequenceToSet(degs));

    // For each degree d present among gens: a monomial basis `mons` of R_d,
    // and a sequence of covectors (SeqEnum[FldRatElt], one per mons) that
    // annihilate span{gens of degree d} inside R_d.
    ann := AssociativeArray();
    for d in uniq_degs do
        mons := [m : m in MonomialsOfDegree(R, d)];
        idxs := [i : i in [1..r] | degs[i] eq d];
        M := Matrix(Rationals(), #mons, #idxs,
                     [MonomialCoefficient(gens[idxs[j]], mons[i]) : i in [1..#mons], j in [1..#idxs]]);
        NS := NullSpace(M); // {L : L*M = 0}, L of length #mons
        ann[d] := <mons, [Eltseq(b) : b in Basis(NS)]>;
    end for;

    for k in [1..n^2] do
        // Chart: fix t_k = 1, solve for the rest. One extra variable w
        // localizes away det(T) = 0 (Rabinowitsch trick): w*det(T) = 1 forces
        // T itself to be invertible.  That alone kills the large degenerate
        // component of rank-deficient T's that map everything into X (which
        // otherwise makes the whole chart look positive-dimensional): once T
        // is genuinely invertible, pullback is a linear automorphism of each
        // degree-d graded piece, so "phi(g_i) lands back in V_d" for every i
        // forces V_d to map onto itself bijectively -- no separate
        // non-degeneracy condition on the g_i's is needed.
        Pt<[t]> := PolynomialRing(Rationals(), n^2);
        tt := [Pt | ];
        idx := 1;
        for i in [1..n^2] do
            if i eq k then
                Append(~tt, Pt!1);
            else
                Append(~tt, Pt.idx);
                idx +:= 1;
            end if;
        end for;
        w := Pt.(n^2 - 1 + 1);
        Tmat := Matrix(Pt, n, n, tt);

        RP := PolynomialRing(Pt, n);
        AssignNames(~RP, ["x" cat IntegerToString(i) : i in [1..n]]);
        Timg := [ &+[Tmat[i][j]*RP.j : j in [1..n]] : i in [1..n] ];
        phi := hom< R -> RP | Timg >;

        eqns := [Pt | ];
        for i in [1..r] do
            d := degs[i];
            mons, Ls := Explode(ann[d]);
            fg := phi(gens[i]);
            coeffvec := [MonomialCoefficient(fg, RP!m) : m in mons];
            for L in Ls do
                Append(~eqns, &+[L[j]*coeffvec[j] : j in [1..#mons]]);
            end for;
        end for;

        // point condition: T * p_from parallel to p_to
        Tp := [ &+[Tmat[i][j]*p_from[j] : j in [1..n]] : i in [1..n] ];
        for a in [1..n] do
            for b in [a+1..n] do
                Append(~eqns, Tp[a]*p_to[b] - Tp[b]*p_to[a]);
            end for;
        end for;

        Append(~eqns, w*Determinant(Tmat) - 1);

        eqns := [e : e in eqns | e ne 0];
        if #eqns eq 0 then continue; end if;

        I := ideal<Pt | eqns>;
        if verbose then
            printf "  chart t_%o=1: %o equations, %o vars\n", k, #eqns, n^2;
        end if;
        if I eq ideal<Pt | 1> then continue; end if; // inconsistent chart

        Sch := Scheme(AffineSpace(Pt), eqns);
        if Dimension(Sch) gt 0 then
            if verbose then printf "  chart t_%o=1: positive-dimensional, skipping\n", k; end if;
            continue;
        end if;
        pts := RationalPoints(Sch);
        for pt in pts do
            vals := Eltseq(pt);
            Tsol := ZeroMatrix(Rationals(), n, n);
            idx2 := 1;
            for i in [1..n] do
                for j in [1..n] do
                    lin := (i-1)*n + j;
                    if lin eq k then
                        Tsol[i][j] := 1;
                    else
                        Tsol[i][j] := vals[idx2];
                        idx2 +:= 1;
                    end if;
                end for;
            end for;
            if Determinant(Tsol) ne 0 then
                return true, Tsol;
            end if;
        end for;
    end for;

    return false, ZeroMatrix(Rationals(), n, n);
end function;

// ---------------------------------------------------------------------------
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

// N=399's D=-3 CM point does not converge at the default eval_prec=3000
// ("half-length series disagrees with full-length series"); 6000 resolves it.
EVAL_PREC := AssociativeArray();
EVAL_PREC[399] := 6000;

// ---------------------------------------------------------------------------
// For one level: build the model, label the rational points, and test
// whether some linear automorphism sends a special point onto an exceptional
// point.
//
// Returns <ok, witnesses>, where witnesses is a list of
// <special_idx, disc, exc_idx> triples (disc = 0 for the cusp).
// ---------------------------------------------------------------------------
function AutomorphismExplains(N : B := 1000, eval_prec := 3000)
    interesting := check_exceptional_example(N : B := B, eval_prec := eval_prec);
    error if #interesting eq 0,
        Sprintf("N = %o: no exceptional point found", N);
    entry  := interesting[1];
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
    gens := DefiningPolynomials(X);

    witnesses := [* *];
    for i in special do
        pi := Eltseq(rats[i]);
        for e in exc do
            pe := Eltseq(rats[e]);
            found, T := FindLinAutoMappingPoint(gens, pi, pe);
            if found then
                d := IsDefined(idx_to_disc, i) select idx_to_disc[i] else -1;
                Append(~witnesses, <i, d, e>);
            end if;
        end for;
    end for;

    return #witnesses gt 0, witnesses;
end function;

// ---------------------------------------------------------------------------
procedure Report(levels, g)
    printf "\n=== genus %o ===\n", g;
    printf "%-6o %-8o %-8o %o\n", "Level", "computed", "paper", "witnesses";
    for N in levels do
        t0 := Cputime();
        ep := IsDefined(EVAL_PREC, N) select EVAL_PREC[N] else 3000;
        ok, w := AutomorphismExplains(N : eval_prec := ep);
        want := EXPECTED[N];
        flag := (ok eq want) select "" else "   <-- DISAGREES WITH PAPER";
        printf "%-6o %-8o %-8o %o%o   (%o s)\n",
               N, ok select "yes" else "no", want select "yes" else "no",
               #w gt 0 select w else [* *], flag, Cputime(t0);
    end for;
end procedure;

Report(GENUS3, 3);
Report(GENUS4, 4);

printf "\nNote: 'computed' tests whether some special point (rational CM point\n";
printf "or the cusp) is carried to the exceptional point by a linear\n";
printf "automorphism of the canonical model, which is what 'explained by an\n";
printf "automorphism' means in the paper.\n";
