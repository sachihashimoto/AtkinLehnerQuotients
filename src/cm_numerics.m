// src/cm_numerics.m
//
// Numerical evaluation of q-expansions at a CM point tau, giving the
// coordinates of that point on a model of X_0(N)*.
//
// Entry points:  TauFromForms(forms, CC)     the CM points themselves
//                EvaluateAtCM                canonical models
//                EvaluateAtCM_hyperelliptic
//
// Self-contained: pure complex-analytic numerics.  Called by labeling.m and
// point_search.m, but calls neither.

function TauFromForms(forms, CC)
    taus := [];
    for f in forms do
        A := f[1]; B := f[2]; C := f[3];
        P<z> := PolynomialRing(CC);
        rts := Roots(A*z^2 + B*z + C, CC);
        tau := [r[1] : r in rts | Imaginary(r[1]) gt 0][1];
        Append(~taus, tau);
    end for;
    return taus;
end function;

// This normalizes an arbitrary-length vector of forms by its largest
// evaluation, for projective coordinates in P^(g-1). 

function EvaluateAtCM(fs, tau, CC, D, ell_pts, disc_ell_pts, N : tol := 10^(-15))
    q := Exp(2*Pi(CC)*Sqrt(CC!-1)*tau);
    evals := [];

    // Determine total ramification order once, since D and tau are fixed.
    // ell_order here really means the total ramification order from H to the quotient.
    ell_order := 1;

    // Classical elliptic contribution from H -> X_0(N).
    if D in disc_ell_pts then
        for ell in [2, 3, 4, 6] do
            if D in Keys(ell_pts[ell]) then
                ell_order := ell;
                break;
            end if;
        end for;

    end if;

    deriv_order := ell_order - 1;

    for f in fs do
        max_n := AbsolutePrecision(f) - 1;
        classical_eval := Evaluate(f, q);

        if deriv_order eq 0 then
            Append(~evals, classical_eval);

        else
            // At a ramification point of total order ell_order,
            // the pulled-back differential should vanish to order ell_order - 1.
            if Abs(classical_eval) ge tol then return []; end if;

            // Use the deriv_order-th logarithmic derivative.
            deriv_val := CC!0;
            q_pow := CC!1;

            for n in [1..max_n] do
                q_pow *:= q;
                a_n := CC!Coefficient(f, n);
                deriv_val +:= n^deriv_order * a_n * q_pow;
            end for;

            Append(~evals, deriv_val);
        end if;
    end for;

    // Return [] to signal failure (e.g. insufficient eval_prec).
    if not exists{e : e in evals | Abs(e) gt tol} then
        return [];
    end if;

    _, j := Maximum([Abs(e) : e in evals]);

    return [evals[i]/evals[j] : i in [1..#evals]];
end function;

function nth_derivative(f, n)
    if n eq 0 then return f; end if;
    return nth_derivative(Derivative(f), n-1);
end function;

// Compute affine (x, y) coordinates at an elliptic CM point of order h using actual
// d/dq derivatives for proper L'Hôpital: x = (d/dq)^{h-1}[f] / (d/dq)^{h-1}[g],
// y from  q*(g*f' - f*g') / g^3 regularized by 3*(h-1) derivatives.
function coords(qexps, tau, h)
    assert #qexps eq 2;
    CC<i> := Parent(tau);
    q0 := Exp(2*Pi(CC)*i*tau);
    _<q> := Universe(qexps);
    numY := q*(qexps[2]*Derivative(qexps[1]) - qexps[1]*Derivative(qexps[2]));
    denomY := qexps[2]^3;
    numx := Evaluate(nth_derivative(qexps[1], h-1), q0);
    denomx := Evaluate(nth_derivative(qexps[2], h-1), q0);
    x := numx/denomx;
    vanish := 3*(h-1);
    numy := Evaluate(nth_derivative(numY, vanish), q0);
    denomy := Evaluate(nth_derivative(denomY, vanish), q0);
    y := numy/denomy;
    return [x, y];
end function;

// Evaluate a CM point on a hyperelliptic model in affine (x, y) coordinates.
// fs = [f_1,...,f_g]: echelon star cusp forms; x = f_{g-1}/f_g, y = D(x)/f_g  (D = q*d/dq).
// Returns [x_val, y_val] as CC elements, or [] if f_g(q) is too small (near-zero denominator).
// The caller may verify y_val^2 ≈ P(x_val).
//
// Genus: the affine branch is correct at any g, but the two WPS-infinity
// branches assume g = 2 and error otherwise (see their comments). That is not
// a restriction in practice: this project is squarefree throughout, and every
// squarefree hyperelliptic X_0(N)* has genus 2 -- the genus->=3 entries of
// IsHyperellipticX0Nstar (Hasegawa's list) are all non-squarefree.
// Optional parameters:
//   ell_order: elliptic ramification order at this CM point (default 1 = no ramification).
//              When > 1, both f_{g-1} and f_g vanish to order e-1; L'Hôpital applies.
//   P_poly:    hyperelliptic polynomial P(x) such that y^2 = P(x). Used only in debug output.
function EvaluateAtCM_hyperelliptic(fs, tau, CC :
    tol := 10^(-15), ell_order := 1, P_poly := 0, debug := false)
    // fs = [f_1,...,f_g] echelon basis; x = f_{g-1}/f_g, y = D(x)/f_g
    g   := #fs;
    f   := fs[g - 1];  gf := fs[g];
    q := Exp(2 * Pi(CC) * CC.1 * tau);

    f_val  := Evaluate(f, q);
    gf_val := Evaluate(gf, q);

    if ell_order gt 1 then
        // At an elliptic CM point of order e, cusp forms vanish to order e-1.
        if debug and (Abs(f_val) ge tol or Abs(gf_val) ge tol) then
            printf "  elliptic warning: ell_order=%o |f(tau)|=%o |g(tau)|=%o tol=%o\n",
                ell_order, Abs(f_val), Abs(gf_val), tol;
        end if;
        // Use d/dq derivatives for proper L'Hôpital at elliptic CM points.
        deriv_denom := Evaluate(nth_derivative(gf, ell_order - 1), q);
        if Abs(deriv_denom) lt tol then
            // D^{h-1}[g] near zero.  Check whether D^{h-1}[f] is nonzero: if so, the
            // basis form g vanishes to higher order than f at this CM tau, making x=f/g
            // -> infinity (WPS-infinity at an elliptic point).  Use f^(g+1) as the
            // regularization denominator to compute the WPS y-coordinate.
            deriv_numer := Evaluate(nth_derivative(f, ell_order - 1), q);
            if Abs(deriv_numer) gt tol then
                _<q_frm> := Universe([f, gf]);
                numY_inf := q_frm * (gf * Derivative(f) - f * Derivative(gf));
                vanish := (g + 1) * (ell_order - 1);
                wps_y_num := Evaluate(nth_derivative(numY_inf, vanish), q);
                wps_y_den := Evaluate(nth_derivative(f^(g+1), vanish), q);
                if Abs(wps_y_den) lt tol then return []; end if;
                if debug then
                    printf "  elliptic WPS-infinity: |D^%o[f]|=%o |D^%o[g]|=%o\n",
                        ell_order-1, Abs(deriv_numer), ell_order-1, Abs(deriv_denom);
                end if;
                // Same genus-2-only normalisation as the non-elliptic
                // WPS-infinity branch below; see its comment.
                error if g ne 2,
                    Sprintf("EvaluateAtCM_hyperelliptic: elliptic WPS-infinity is only implemented for genus 2, got genus %o", g);
                return [CC!1, wps_y_num / wps_y_den, CC!0];
            end if;
            if debug then
                printf "  elliptic failure: derivative denominator |Dgf|=%o < tol=%o\n",
                    Abs(deriv_denom), tol;
            end if;
            return [];
        end if;
        ev_ell := coords([f, gf], tau, ell_order);
        x_val := ev_ell[1];
        y_val := ev_ell[2];
        if debug then
            px_dbg := Evaluate(P_poly, x_val);
            printf "  elliptic candidate: x=%o y=%o residual=%o\n",
                x_val, y_val, Abs(y_val^2 - px_dbg);
        end if;
        return [x_val, y_val];
    end if;

    // D(f) and D(g) via n-weighted q-expansion: D(h) = sum_{n>=1} n * a_n * q^n
    max_n   := AbsolutePrecision(f) - 1;
    Df_val  := CC!0;
    Dgf_val := CC!0;
    q_pow   := CC!1;
    for n in [1..max_n] do
        q_pow  *:= q;
        Df_val  +:= CC!Coefficient(f,  n) * CC!n * q_pow;
        Dgf_val +:= CC!Coefficient(gf, n) * CC!n * q_pow;
    end for;

    wron_val := Df_val * gf_val - f_val * Dgf_val;

    // WPS infinity: gf(q)=0 but f(q)≠0, so x=f/gf -> inf; in WPS(1,g+1,1) the y-coord is (q*(g*f' - f*g') / g^3 )/f^(g+1).
    // Require f_val large before testing gf/f, so that f(tau)≈0 (affine x=0 point)
    // is not misidentified as WPS infinity.
    // Relative check is stable under the automorphy factor (cτ+d)^k picked up by
    // any Mobius transform of tau (e.g. the Atkin-Lehner/SL_2(Z) representatives
    // CMTaus returns).
    if Abs(f_val) gt tol and Abs(gf_val / f_val) lt tol then
        // Normalising X to 1 in WPS(1, g+1, 1) gives Y = W * f_g^(g-2) / f_{g-1}^(g+1);
        // the f_g^(g-2) factor below is dropped, which is only legitimate at
        // g = 2 (at g >= 3 the true limit is 0 as f_g -> 0). Squarefree levels
        // are always g = 2 here, so refuse rather than return a wrong point.
        error if g ne 2,
            Sprintf("EvaluateAtCM_hyperelliptic: WPS-infinity is only implemented for genus 2, got genus %o", g);
        return [CC!1, wron_val / f_val^(g+1), CC!0];
    end if;

    // Affine point: return [x, y] (2-element sequence).
    x_val := f_val / gf_val;
    y_val := wron_val / gf_val^3;
    return [x_val, y_val];
end function;
