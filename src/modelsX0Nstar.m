// src/modelsX0Nstar.m
//
// Models of the quotient curve X_0(N)*, canonical or hyperelliptic according
// to the level, together with the Sturm-bound checks that prove their defining
// equations really do vanish.
//
// Entry points:  XZeroNstar(N)                          the model
//                XZeroNstarWithForms(N, eval_prec)      model and star cusp forms
//                XZeroNstarWithForms_hyperelliptic(N, eval_prec)
//                IsHyperellipticX0Nstar(N)              which of the two to use
//
// Not loadable standalone: load "src/AtkinLehner.m" instead.  Depends on
// star_quotients.m for GenusStarQuotient.

// ---------------------------------------------------------------------------
// Sturm-bound certification.
//
// A candidate equation is only proven to vanish on X_0(N)* once its
// q-expansion is checked past the Sturm bound for its own weight.  Agreement
// to some arbitrary truncation length is evidence but not proof: a wrong
// relation can match the true one to any finite precision.
// ---------------------------------------------------------------------------

// Sturm bound for weight `weight` forms on Gamma_0(N): two such forms whose
// q-expansions agree through q^B necessarily agree identically.
function ModularSturmBound(N, weight)
    assert weight ge 0;
    return Floor(weight * Index(Gamma0(N)) / 12);
end function;

// Certify that the q-expansion poly_qexp (computed to weight `weight` on
// Gamma_0(N)) is identically zero, by checking it vanishes past the Sturm
// bound. Errors (rather than silently under-certifying) if poly_qexp was not
// computed to enough precision to even ask the question.
function CertifyModularIdentity(poly_qexp, N, weight)
    B := ModularSturmBound(N, weight);
    prec := AbsolutePrecision(poly_qexp);
    error if prec le B,
        Sprintf("CertifyModularIdentity: insufficient precision, need precision > %o (Sturm bound for weight %o on Gamma_0(%o)), got %o",
                B, weight, N, prec);
    return Valuation(poly_qexp) gt B, B;
end function;

// Certify every equation in `equations` (homogeneous of possibly-mixed
// degree in the star cusp forms) by re-evaluating each on q-expansions of
// `Sstar` recomputed to comfortably exceed the Sturm bound for its own
// weight (2*Degree(e)). Sstar is the list of live CuspForms elements (not
// just cached power series), so this only asks for more terms of forms
// already in hand, it does not repeat the all_diag_basis computation.
// Returns ok, B_max (the largest Sturm bound needed, so a caller that fails
// certification knows how far to jump the next candidate search).
function CertifyCanonicalEquations(equations, Sstar, N : margin := 20)
    weights := [];
    for e in equations do
        assert IsHomogeneous(e);
        Append(~weights, 2 * Degree(e));
    end for;
    B_max := Max([ModularSturmBound(N, w) : w in weights]);
    cert_prec := B_max + 1 + margin;
    // all_diag_basis returns an integral basis, so qExpansion here can come
    // back as a series over Integers() rather than Rationals(), Evaluate
    // against a genuinely rational-coefficient equation then fails with
    // "Illegal coercion". Force the ring explicitly.
    Rq := PowerSeriesRing(Rationals());
    bas_cert := [Rq ! qExpansion(f, cert_prec) : f in Sstar];
    for i in [1..#equations] do
        val := Evaluate(equations[i], bas_cert);
        ok, _ := CertifyModularIdentity(val, N, weights[i]);
        if not ok then
            return false, B_max;
        end if;
    end for;
    return true, B_max;
end function;

function IsHyperellipticX0Nstar(N)
  if N in [1,2,3,4,5,6,7,8,9,10,12,13,16,18,25] cat  [11,14,15,17,19,20,21,24,27,32,36,49] cat [22,23,26,28,29,30,31,33,35,37,39,40,41,46,47,48,50,59,71] then
        return true;
    end if;
    // Hyperelliptic X_0(N)* are completely classified (Hasegawa): the genus >= 3
    // ones are exactly the list below, and every genus-2 (also hyperelliptic)
    // level has N < 500.  So for N >= 500 the curve is non-hyperelliptic of genus
    // >= 3 and we return false without computing the genus, GenusStarQuotient(N) for
    // large N (e.g. 870, 910) diagonalizes the full level-N Atkin-Lehner action
    // and is prohibitively slow, and there is nothing to learn from it here.
    if N in [136, 171, 176, 207, 252, 279, 315] then
        return true;
    end if;
    if N ge 500 then
        return false;
    end if;
    if GenusStarQuotient(N) le 2 then
        return true;
    end if;
  return false;
end function;

function ratfun(target, basis, degree, R)
  // target = q-series of target function (e.g., j)
  // basis = [b1,...,bn] basis of space of cusp forms
  // degree = degree of numerator and denominator polynomial

  // try to write target as poly(basis)/poly(basis) with two
  // homogeneous polynomials of degree degree
  mons := MonomialsOfDegree(R, degree);
  printf "Evaluating %o monomials of degree %o on basis of cardinality %o.\n", #mons, degree, #basis;
  evmons := [Evaluate(m, basis) : m in mons];
  evmonst := [-target*em : em in evmons];
  min := Min([Valuation(e) : e in evmons cat evmonst]);
  max := Min([AbsolutePrecision(e) : e in evmons cat evmonst]) - 1;
  mat := Matrix([[Coefficient(e, j) : j in [min..max]]
                   : e in evmons cat evmonst]);
  printf "Computing kernel matrix of matrix with %o rows and %o columns.\n", Nrows(mat), Ncols(mat);
  kermat := KernelMatrix(mat);
  printf "Kernel matrix with %o rows and %o columns.\n", Nrows(kermat), Ncols(kermat);
  result := [<&+[kermat[i,j]*mons[j] : j in [1..#mons]],
              &+[kermat[i,#mons+j]*mons[j] : j in [1..#mons]]> : i in [1..Nrows(kermat)]];
  result := [pair : pair in result | Valuation(Evaluate(pair[1], basis)) lt max];
  return result;
end function;

function XZeroNstarWithForms(N, eval_prec)
// Returns (X, fs): X is the canonical model of X_0(N)* and fs are the star cusp form
// q-expansions (to eval_prec terms) built from the same all_diag_basis call used to
// construct X.  all_diag_basis is called exactly once so fs and X share coordinates.
// Errors on hyperelliptic N; use XZeroNstar for that case.
    if IsHyperellipticX0Nstar(N) then
        error "XZeroNstarWithForms: hyperelliptic case not implemented for N =", N;
    end if;
    number_of_terms := 20;
    g := GenusStarQuotient(N);
    S, ALs := all_diag_basis(N);
    Sstar := [S[i] : i in [1..#S] | forall{w : w in ALs | w[i,i] eq +1}];
    assert #Sstar eq g;
    repeat
        number_of_terms +:= 10;
        bas := [qExpansion(f, number_of_terms) : f in Sstar];
        Pg1<[z]> := PolynomialRing(Rationals(), g);
        // For g = 3 the canonical curve is a plane quartic: a single quartic
        // is the only equation there is, no notion of quadrics applies since
        // the ambient P^2 has no codimension left to spare. For g >= 4, every
        // smooth non-hyperelliptic canonical curve has some quadrics through
        // it (Riemann-Roch: dim I_2 = g(g+1)/2 - (3g-3), which is already
        // positive at g=4) except that a single quadric alone never has
        // enough codimension to cut a g=4 curve out of P^3 by itself, so a
        // cubic is still needed there too; g=5 non-trigonal curves ARE cut
        // out by quadrics alone (a net of 3), and g >= 6 is generated by
        // quadrics unless the curve is trigonal (or a plane quintic), in
        // which case cubics are also needed (Petri). So for every g >= 4,
        // try quadrics first and only add cubics if that alone does not cut
        // dimension down to 1 -- this used to jump straight to cubics for
        // g in {4,5} and skip quadrics entirely, which silently produced a
        // non-saturated ideal (missing the quadric that Riemann-Roch
        // guarantees exists): see the AtkinLehnerQuotients issue tracker,
        // "Ideal(X)/DefiningPolynomials(X) is non-saturated for genus 4/5
        // models".
        if g eq 3 then
            d := 4;
        else
            d := 2;
        end if;
        // Relations of a given degree among the star forms.
        relsOfDeg := function(deg)
            monsd := MonomialsOfDegree(Pg1, deg);
            mat := Matrix([[Coefficient(m, j) : j in [2..number_of_terms]]
                            where m := Evaluate(mm, bas) : mm in monsd]);
            kermat := KernelMatrix(mat);
            return [&+[kermat[i,j]*monsd[j] : j in [1..#monsd]] : i in [1..Nrows(kermat)]];
        end function;
        equations := relsOfDeg(d);
        Pws<q> := Universe(bas);
        X0_N_Scheme := Scheme(ProjectiveSpace(Pg1), equations);
        if (g ge 4) and (Dimension(X0_N_Scheme) ne 1) then
            equations cat:= relsOfDeg(3);
            X0_N_Scheme := Scheme(ProjectiveSpace(Pg1), equations);
        end if;
        if Dimension(X0_N_Scheme) ne 1 then
            continue;
        end if;
        candidate := Curve(X0_N_Scheme);
        if Genus(candidate) ne g then
            continue;
        end if;
        // Dimension/genus agreeing with expectation is evidence, not proof: a
        // relation can vanish to the available truncation precision without
        // being a genuine modular-form identity. Certify past the Sturm bound
        // for each equation's own weight before accepting.
        certified, B_max := CertifyCanonicalEquations(equations, Sstar, N);
        if not certified then
            number_of_terms := Max(number_of_terms + 10, B_max + 1);
            continue;
        end if;
        X0_N := candidate;
    until assigned X0_N;
    fs := [qExpansion(f, eval_prec) : f in Sstar];
    return X0_N, fs, Sstar;
end function;

function XZeroNstarWithForms_hyperelliptic(N, eval_prec)
// Build a hyperelliptic model of X_0(N)* directly from its star cusp forms.
// Works for any genus g >= 2 where X_0(N)* is hyperelliptic.
// Returns (C, fs, Sstar) where:
//   C     = HyperellipticCurve y^2 = P(x) over Q
//           The echelon basis f_1,...,f_g has f_j with leading term q^j.
//           f_g = dx/y, f_{g-1} = x*dx/y, so x = f_{g-1}/f_g
//           and y = D(x)/f_g = (D(f_{g-1})*f_g - f_{g-1}*D(f_g)) / f_g^3  (D = q*d/dq)
//   fs    = [f_1,...,f_g] q-expansions of echelon star cusp forms to eval_prec terms
//   Sstar = list of star cusp forms (from all_diag_basis) for later precision boosting

    assert IsHyperellipticX0Nstar(N);
    g_star := GenusStarQuotient(N);
    assert g_star ge 2;

    S, ALs := all_diag_basis(N);
    Sstar := [S[i] : i in [1..#S] | forall{w : w in ALs | w[i,i] eq +1}];
    assert #Sstar eq g_star;

    // Echelonize so that diag_sstar[j] has leading term q^j
    M_hyp := Matrix([AbsEltseq(qExpansion(f, eval_prec) : FixedLength) : f in Sstar]);
    E, T_hyp := EchelonForm(M_hyp);
    diag_sstar := [&+[T_hyp[i][j]*Sstar[j] : j in [1..g_star]] : i in [1..g_star]];

    // x = f_{g-1}/f_g, y = D(x)/f_g = (D(fg1)*fg - fg1*D(fg)) / fg^3, where D
    // = q*d/dq. x, y are meromorphic modular functions, not modular forms, so
    // agreement of yq^2 and P(xq) to some truncation length is not a Sturm
    // certification. What is a genuine (weight 4*g_star+4) modular form
    // identity is the cleared-denominator form
    //   W^2 * f_g^(2g-4) = sum_k c_k f_{g-1}^k f_g^(2g+2-k),
    //   W = D(f_{g-1})*f_g - f_{g-1}*D(f_g)
    // (W is, up to normalization, the weight-6 Rankin-Cohen bracket of two
    // weight-2 forms). Solve for P at low-ish precision as before, but only
    // accept it once this cleared identity is checked past the Sturm bound
    // for its own weight.
    deg    := 2*g_star + 2;
    weight := 4*g_star + 4;
    B_hyp  := ModularSturmBound(N, weight);
    margin := 20;
    // Any solve precision below B_hyp can't possibly certify; start there.
    t := Max(Floor(Index(Gamma0(N)) * g_star / 6), B_hyp + 1);
    // all_diag_basis returns an integral basis, so qExpansion can come back
    // as a series over Integers() rather than Rationals(), multiplying by
    // the rational P_coeffs below, or Evaluate against a rational-coefficient
    // equation, then fails with "Illegal coercion". Force the ring explicitly.
    Rc := PowerSeriesRing(Rationals());
    qc := Rc.1;
    repeat
        cert_prec := t + 1 + margin;
        fg1c := Rc ! qExpansion(diag_sstar[g_star - 1], cert_prec);
        fgc  := Rc ! qExpansion(diag_sstar[g_star],     cert_prec);
        Dfg1c := qc * Derivative(fg1c);
        Dfgc  := qc * Derivative(fgc);
        Wc := Dfg1c * fgc - fg1c * Dfgc;

        L<ql> := LaurentSeriesRing(Rationals());
        fg1L := L ! fg1c;
        fgL  := L ! fgc;
        xq  := fg1L / fgL;
        y2q := (L ! Wc)^2 / fgL^6;

        mat   := Matrix([[Coefficient(xq^k, j) : j in [0..t]] : k in [0..deg]]);
        y2vec := Vector([Coefficient(y2q,   j) : j in [0..t]]);
        P_coeffs := Solution(mat, y2vec);

        LHS := Wc^2 * fgc^(2*g_star - 4);
        RHS := &+[P_coeffs[k+1] * fg1c^k * fgc^(deg-k) : k in [0..deg]];
        certified, _ := CertifyModularIdentity(LHS - RHS, N, weight);
        if not certified then
            // Use all the coefficients already computed at cert_prec, rather
            // than a small fixed increment, for the next solve attempt.
            t := cert_prec;
        end if;
    until certified;

    Px<x> := PolynomialRing(Rationals());
    P := Px ! Eltseq(P_coeffs);

    C := HyperellipticCurve(P);
    fs := [qExpansion(diag_sstar[i], eval_prec) : i in [1..g_star]];
    return C, fs, Sstar;
end function;

function XZeroNstar(N)
    if IsHyperellipticX0Nstar(N) then
      wds := [[d : d in Divisors(N) | Gcd(d, ExactQuotient(N,d)) eq 1]];
      X, ws, pairs, NB, cusp := eqs_quos(N, wds);
      X := pairs[1][1];
      return X;
    else
      // now X_0(N)^* is not hyperelliptic.
      // XZeroNstarWithForms builds the canonical model; eval_prec only controls
      // the q-expansions returned alongside it, which are computed once the
      // model is in hand, so the model is independent of the value passed here.
      // Callers who want the forms should call XZeroNstarWithForms directly.
      X := XZeroNstarWithForms(N, 20);
      return X;
    end if;
end function;
