// src/star_degree.m
//
// The Atkin-Lehner translations c_n, the star degree delta_f, and the target
// curve E^C_f of the degree-3 covers X_0^*(N) -> E.  Everything here is exact:
// the c_n are read off from modular symbols, not approximated.
//
// Entry points:  TotallyPlusOptimalCurves(d)     the eligible curves of level d
//                StarDegree(E)                   delta_f
//                StarTargetCurve(E)              E^C_f
//
// Not loadable standalone: load "src/AtkinLehner.m" instead.  This module has no
// dependencies on the rest of the library.

// Basis (rows, over Q) of the image of H_1(X_0(d), Z) in the f-isotypic part of
// M, together with the projection matrix and the ambient space; the three
// objects every c_n computation at this level needs.
function StarHomologyImageBasis(M)
    A   := AmbientSpace(M);
    pmx := ProjectionMatrix(M);
    LH  := Lattice(CuspidalSubspace(A));            // H_1(X_0(d), Z)
    IM  := Matrix(Rationals(), [Eltseq(b) : b in Basis(LH)]) * pmx;
    den := LCM([Denominator(x) : x in Eltseq(IM)]);
    Lim := Lattice(Matrix(Integers(), den*IM));     // saturated, rank 2
    B   := Matrix(Rationals(), [[x/den : x in Eltseq(b)] : b in Basis(Lim)]);
    return B, pmx, A;
end function;

// Class of c_n in E_f(Q)[2] = (1/2)L / L, as a vector over GF(2)^2.
// w_n(oo) is the cusp 1/(d/n) for squarefree d.
function ALTranslationClass(A, pmx, B, d, n)
    s := A ! <1, [Cusps() | Infinity(), 1/(d div n)]>;
    v := Vector(Rationals(), Eltseq(s)) * pmx;
    ok, sol := IsConsistent(B, v);
    error if not ok,
        Sprintf("ALTranslations: the symbol {oo, 1/%o} is not in the f-isotypic span", d div n);
    w := [];
    for x in Eltseq(sol) do
        error if Denominator(x) notin {1, 2},
            Sprintf("ALTranslations: c_%o has coordinate %o, not a half-integer; the obstruction lemma predicts c_n in E_f(Q)[2]; check that the IMAGE lattice (not Lattice(M)) was used", n, x);
        Append(~w, (Integers() ! (2*x)) mod 2);
    end for;
    return VectorSpace(GF(2), 2) ! w;
end function;

// C = im(c) for the optimal curve E of squarefree conductor d.
// Returns |C| and the list of <q, class> pairs, one per prime q | d.
function ALTranslations(E)
    d := Conductor(E);
    error if not IsSquarefree(d),
        Sprintf("ALTranslations: conductor %o is not squarefree", d);
    B, pmx, A := StarHomologyImageBasis(ModularSymbols(E));
    prs := PrimeDivisors(d);
    classes := [<q, ALTranslationClass(A, pmx, B, d, q)> : q in prs];
    // c is a homomorphism: c_{q1 q2} = c_{q1} + c_{q2}.  Free redundancy that a
    // wrong lattice or a mis-indexed cusp would break.
    for i in [1..#prs] do
        for j in [i+1..#prs] do
            n := prs[i] * prs[j];
            error if ALTranslationClass(A, pmx, B, d, n) ne classes[i][2] + classes[j][2],
                Sprintf("ALTranslations: c is not additive at n = %o (conductor %o)", n, d);
        end for;
    end for;
    C := sub<VectorSpace(GF(2), 2) | [t[2] : t in classes]>;
    // C is a subgroup of E(Q)[2], so its order divides the number of rational
    // 2-torsion points.
    T := TorsionSubgroup(E);
    n2 := #[t : t in T | 2*t eq T ! 0];
    error if not IsDivisibleBy(n2, #C),
        Sprintf("ALTranslations: |C| = %o does not divide #E(Q)[2] = %o for %o",
            #C, n2, CremonaReference(E));
    return #C, classes;
end function;

// delta_f = |C| * deg(phi_d) / 2^omega(d) = deg(X_0^*(d) -> E^C_f).
// E must be the Cremona-optimal curve of its class: ModularDegree is deg(phi_d)
// only there.
function StarDegree(E)
    d  := Conductor(E);
    nC := ALTranslations(E);
    r  := nC * ModularDegree(E) / 2^#PrimeDivisors(d);
    error if Denominator(r) ne 1 or r le 0,
        Sprintf("StarDegree: delta_f = %o is not a positive integer for %o; the lemma guarantees it is",
            r, CremonaReference(E));
    return Integers() ! r;
end function;

// E^C_f = E_f/C, as a minimal model.  The degree-3 covers land here, not on E_f.
function StarTargetCurve(E)
    nC := ALTranslations(E);
    if nC eq 1 then
        return MinimalModel(E);
    end if;
    T, mp := TorsionSubgroup(E);
    two := [mp(t) : t in T | 2*t eq T ! 0 and t ne T ! 0];
    // |C| = 2 with #E(Q)[2] = 4 would need the class matched to one of three
    // order-2 subgroups.  No production input reaches that case, 185c1, the
    // only curve in the tables with C != 0, has #E(Q)[2] = 2; so error rather
    // than ship disambiguation code no test could exercise.
    error if nC ne #two + 1,
        Sprintf("StarTargetCurve: |C| = %o with %o nonzero rational 2-torsion points on %o; identifying which order-2 subgroup C is would need the class matched to a point, and no production input reaches this case",
            nC, #two, CremonaReference(E));
    // C is all of E(Q)[2]: quotient by it, one 2-isogeny at a time.
    F := E;
    for i in [1..Ilog(2, nC)] do
        TF, mpF := TorsionSubgroup(F);
        twoF := [mpF(t) : t in TF | 2*t eq TF ! 0 and t ne TF ! 0];
        error if #twoF eq 0,
            Sprintf("StarTargetCurve: ran out of rational 2-torsion quotienting %o", CremonaReference(E));
        F := MinimalModel(Codomain(TwoIsogeny(twoF[1])));
    end for;
    return F;
end function;

// The Cremona-optimal curves of the isogeny classes of conductor exactly d
// whose newform has all Atkin-Lehner eigenvalues +1 (equivalently a_q = -1 for
// every q | d).  Empty for most d, in particular for a level like 174 whose
// covers come from the newform level 58.
function TotallyPlusOptimalCurves(d)
    out := [];
    if d lt 11 then return out; end if;
    DB := CremonaDatabase();
    for i in [1..NumberOfIsogenyClasses(DB, d)] do
        E := EllipticCurve(DB, d, i, 1);
        if &and[TraceOfFrobenius(E, q) eq -1 : q in PrimeDivisors(d)] then
            Append(~out, E);
        end if;
    end for;
    return out;
end function;
