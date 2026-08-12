// src/labeling.m
//
// Given a point found by point_search.m, decide what it is: a cusp, an
// elliptic point, a CM point of known discriminant, or a genuinely exceptional
// point.  Also fits planes through coplanar CM triples, which is how the
// exceptional points get explained.
//
// Entry points:  LabelAndAnalyze(N, X, fs, rats, rat_cm_discs)   (canonical)
//                LabelAndAnalyze_hyperelliptic(...)              (hyperelliptic)
//
// Depends on cm_numerics.m, cm_orders.m and fields_of_definition.m.
//
// Throughout this file, "confirmed" and "certified" mean checked numerically
// at two precisions and two q-expansion lengths against a tolerance scaled to
// the run's own measured noise. That is strong evidence, not a proof.



function NumberOfEllipticPoints(N, order)
    if order eq 2 then
        return &+[EulerPhi(GCD(d, N div d)) : d in Divisors(N)];
    end if;
    if order eq 4 then
        Q := 4;
    end if;
    if order eq 3 then
        Q := 9;
    end if;
    if (N mod Q eq 0) then
        return 0;
    end if;
    primesN := PrimeDivisors(N);
    e_N := &*[Integers() | 1 + KroneckerSymbol(-order, p) : p in primesN];
    return e_N;
end function;

function NumFixedPointsByCMOrder(N, m)
//The number of the fixed points of w_m on X_0(N) split by CM order.
    assert m ne 1;// "m should be greater than 1!";
    e := AssociativeArray();
    orders := CMOrdersForAL(m);
    for R in orders do
        nR := NumberOfOptimalEmbeddings(R,N);
        e[Discriminant(R)] := nR;
    end for;
    return e;
end function;


function NumberOfEllipticPointsByCMOrderArray(N, q)
    // Return the number of elliptic points of order q on X.
    assert (q gt 1);// "Elliptic points of order %o are not well-defined.", q;
    W := {d : d in Divisors(N) | GCD(d, N div d) eq 1};
    delta_2 := (2 in W) select 1 else 0;
    delta_3 := (3 in W) select 1 else 0;
    e := AssociativeArray();
    e2 := NumberOfEllipticPoints(N, 4);
    e3 := NumberOfEllipticPoints(N, 3);
    F_W := AssociativeArray();
    if q eq 2 then
        for w in W do
            if w eq 1 then continue; end if;
            n_w := NumFixedPointsByCMOrder(N,w);
            for d in Keys(n_w) do
                F_W[d] := 2*n_w[d];
            end for;
        end for;
        if not IsDefined(F_W,-3) then F_W[-3] := 0; end if;
        if not IsDefined(F_W,-4) then F_W[-4] := 0; end if;
        F_W[-4] +:= (1-3*delta_2)*e2;
        F_W[-3] -:= 2*delta_3*e3;
    elif q eq 3 then
        F_W[-3] := (1-delta_3)*e3;
    elif q eq 4 then
        F_W[-4] := 2*delta_2*e2;
    elif q eq 6 then
        F_W[-3] := 2*delta_3*e3;
    end if;
    for d in Keys(F_W) do
        if F_W[d] eq 0 then
            Remove(~F_W,d);
            continue;
        end if;
        assert (F_W[d] mod #W eq 0); // "Error counting elliptic points, getting non-integral result.";
        F_W[d] div:= #W;
    end for;
    return F_W;
end function;

function NumberOfEllipticPointsByCMOrder(N)
    // Return the number of elliptic points of every CM type on X.
    ell := AssociativeArray();
    for q in [2,3,4,6] do
        ell[q] := NumberOfEllipticPointsByCMOrderArray(N,q);
    end for;
    return ell;
end function;

// Discriminants of the elliptic CM points on X_0(N) (order 2, 3, 4 or 6, the only
// orders possible), plus the ell_pts table they come from. At such a point both
// cusp forms vanish to order e-1 and need L'Hopital correction; see EvaluateAtCM
// in cm_numerics.m. Also used by src/triple_covers.m's CMFiberSetup.
function EllipticDiscsByOrder(N)
    ell_pts := NumberOfEllipticPointsByCMOrder(N);
    disc_ell_pts := {};
    for ell in [2,3,4,6] do disc_ell_pts join:= Keys(ell_pts[ell]); end for;
    return ell_pts, disc_ell_pts;
end function;

// Search for exceptional rational points that are the hyperelliptic involution of another
// rational point on C. Returns a list of entries <exc_idx, partner_idx, [1,1], cm_discs, true>
// mirroring the coplanarity planes format. cm_discs is the set of CM discriminants of the
// partner (empty if the partner is itself unmatched).
// idx_to_disc: map from rat index to CM discriminant (built from disc_to_idx in the caller).
function HyperellipticInvolutionSearch(C, rats, exceptional_idxs, idx_to_disc)
    hyp_inv := HyperellipticInvolution(C);
    exc_set := {j : j in exceptional_idxs};
    pairs := [* *];
    for j in exceptional_idxs do
        inv_j := hyp_inv(rats[j]);
        for k in [1..#rats] do
            if k eq j or k in exc_set or inv_j ne rats[k] then continue; end if;
            partner_discs := IsDefined(idx_to_disc, k) select {idx_to_disc[k]} else {};
            Append(~pairs, <j, k, [1, 1], partner_discs, true>);
            break;
        end for;
    end for;
    return pairs;
end function;

// Label rational points on a hyperelliptic X_0(N)* as CM, cusp, or exceptional.
// C: HyperellipticCurve y^2 = P(x) from XZeroNstarWithForms_hyperelliptic.
// rats: rational points from Points(C : Bound := B).
// rat_cm_discs: Keys of RationalCMDiscs(N).
// Returns (exceptional_idxs, involution_pairs, all_matched, fail_reason,
// idx_to_disc).
//
// Deliberately kept separate from LabelAndAnalyze despite the parallel shape:
// CM matching here is affine (x,y) plus a WPS-infinity chart for a degree-2
// map to P^1, and exceptional points are explained by the hyperelliptic
// involution rather than by fitting hyperplanes in P^(g-1). Different
// algorithms for different model geometries; the shared part is already
// factored out into EllipticDiscsByOrder.
function LabelAndAnalyze_hyperelliptic(N, C, fs, rats, rat_cm_discs :
    cc_prec := 200, debug := false)
    CC  := ComplexField(cc_prec);
    tol := 10^-10;  // affine coordinate tolerance (looser than projective)
    g   := Genus(C);

    // Build affine (x, y) coordinates for each rational point.
    // HyperellipticCurve points: Eltseq gives [X, Y, Z] in WPS(1, g+1, 1).
    // Affine coords: x = X/Z, y = Y/Z^(g+1). Points returned with Z=1.
    rats_xy := [];
    for j in [1..#rats] do
        if rats[j][3] eq 0 then
            Append(~rats_xy, <false, CC!0, CC!0>);
        else
            seq := Eltseq(rats[j]);
            z   := seq[3];
            Append(~rats_xy, <true, CC!(seq[1]/z), CC!(seq[2]/z^(g+1))>);
        end if;
    end for;

    // Find j such that rats[j] has affine coords (x_ev, +-y_ev) within tol.
    function AffineMatch(x_ev, y_ev)
        for j in [1..#rats_xy] do
            if not rats_xy[j][1] then continue; end if;
            xr := rats_xy[j][2]; yr := rats_xy[j][3];
            if Abs(x_ev - xr) lt tol and Abs(y_ev - yr) lt tol then
                return j;
            end if;
        end for;
        return 0;
    end function;

    matched := {};
    disc_to_idx := AssociativeArray();
    nfail := 0; fail_reason := "";

    ell_pts, disc_ell_pts := EllipticDiscsByOrder(N);

    // WPS-infinity rat data, for CM points where f_g(q)=0 and so x -> inf.
    // In WPS(1,g+1,1): [X:Y:Z] ~ [lambda*X : lambda^(g+1)*Y : lambda*Z], so at
    // Z=0 with X!=0 the WPS y-coordinate is Y/X^(g+1).
    P_poly := HyperellipticPolynomials(C);
    inf_rats_info := [];
    for j in [1..#rats] do
        if rats[j][3] eq 0 then
            seq := Eltseq(rats[j]);
            if Abs(CC!seq[1]) gt tol then
                Append(~inf_rats_info, <j, CC!seq[2] / CC!seq[1]^(g+1)>);
            end if;
        end if;
    end for;

    // Returns the rat index j if the precomputed wps_y = Wron/f^3 matches an infinity rat, else 0.
    function InfinityValMatch(wps_y)
        for info in inf_rats_info do
            if Abs(Real(wps_y) - Real(info[2])) lt 10^-5 and
               Abs(Imaginary(wps_y)) lt 10^-5 then
                return info[1];
            end if;
        end for;
        return 0;
    end function;

    // Step A–C: evaluate CM points and match against rational points.
    for disc in rat_cm_discs do
        // One tau per <Gamma_0(N), AL>-orbit: distinct entries are distinct
        // points of X_0(N)*, each at its orbit's largest Im(tau).
        taus := CMTauReps(disc, N, CC);

        // If the basis has f_g vanishing to higher order than f_{g-1}, the CM
        // point maps to WPS infinity; EvaluateAtCM_hyperelliptic detects this
        // and returns a 3-element result, as on the non-elliptic path.
        ell_order := 1;
        if disc in disc_ell_pts then
            for ell in [2,3,4,6] do
                if disc in Keys(ell_pts[ell]) then ell_order := ell; break; end if;
            end for;
        end if;

        found := false;
        ever_affine_ok := false;  // true if any tau produced a valid affine evaluation
        ever_inf_ok    := false;  // true if any tau produced a WPS-infinity evaluation
        for tau in taus do
            ev := EvaluateAtCM_hyperelliptic(fs, tau, CC : tol := tol,
                      ell_order := ell_order, P_poly := P_poly, debug := debug);
            if #ev eq 2 then
                ever_affine_ok := true;
                // Step D: verify y^2 ≈ P(x); for elliptic case this is exact by construction.
                residual := Abs(ev[2]^2 - Evaluate(P_poly, ev[1]));
                if residual gt 10^-5 then
                    if not found then
                        printf "  D=%o: residual y^2-P(x)=%o (normalization issue, skipping)\n", disc, residual;
                    end if;
                    continue;
                end if;
                j := AffineMatch(ev[1], ev[2]);
                if j gt 0 then
                    if j in matched and (not IsDefined(disc_to_idx, disc) or disc_to_idx[disc] ne j) then
                        error Sprintf("N=%o: collision: disc=%o matched to rats[%o] but that index already in matched", N, disc, j);
                    end if;
                    if j notin matched then
                        if ell_order gt 1 then
                            printf "  disc = %o -> rats[%o], %o (CM hyperelliptic, elliptic order %o)\n", disc, j,rats[j], ell_order;
                        else
                            printf "  disc = %o -> rats[%o], %o, (CM hyperelliptic)\n", disc, j, rats[j];
                        end if;
                        Include(~matched, j);
                        if not IsDefined(disc_to_idx, disc) then disc_to_idx[disc] := j; end if;
                    end if;
                    found := true;
                end if;
                if not found then
                    printf "  D=%o: affine eval x~%o y~%o, no affine rat matched\n",
                        disc, Real(ev[1]), Real(ev[2]);
                end if;
            elif #ev eq 3 then
                // WPS infinity: [1 : wps_y : 0] in WPS(1,3,1). taus is ordered by
                // descending Im(tau), so the first tau to reach here already has
                // the best available precision for wps_y.
                ever_inf_ok := true;
                j := InfinityValMatch(ev[2]);
                if j gt 0 then
                    if j in matched then
                        error Sprintf("N=%o: collision: disc=%o matched to rats[%o] (WPS infinity) but that index already in matched", N, disc, j);
                    end if;
                    printf "  disc = %o -> rats[%o], %o (CM hyperelliptic, WPS infinity)\n", disc, j, rats[j];
                    Include(~matched, j);
                    disc_to_idx[disc] := j;
                    found := true; break;
                end if;
                printf "  D=%o: g(q)~0 (CM at WPS infinity), no infinity rat matched\n", disc;
            end if;
        end for;
        if not found then
            if ever_affine_ok then
                fail_reason := Sprintf("D=%o: affine eval ok but no rat matched (large-height CM point?)", disc);
            elif ever_inf_ok then
                fail_reason := Sprintf("D=%o: WPS infinity detected but no rat matched (needs higher eval_prec)", disc);
            elif ell_order gt 1 then
                fail_reason := Sprintf("D=%o: elliptic CM point (order %o) evaluation failed (needs higher eval_prec)", disc, ell_order);
            else
                fail_reason := Sprintf("D=%o: CM evaluation failed (needs higher eval_prec)", disc);
            end if;
            nfail +:= 1; break;
        end if;
    end for;

    if nfail ne 0 then
        printf "WARNING: CM matching failed for N=%o: %o\n", N, fail_reason;
        return [], [* *], false, fail_reason, AssociativeArray();
    end if;

    // The cusp (q -> 0) is a WPS-infinity point: with the echelon basis
    // f_{g-1} = c1*q^(g-1)+... and f_g = c2*q^g+..., x = f_{g-1}/f_g -> infinity.
    // Its WPS y-coordinate is the q->0 limit of Wron(f_{g-1},f_g)/f_{g-1}^(g+1),
    // which for genus 2 (the only genus where the cusp lands on this X != 0
    // chart) equals -c2/c1^2. Do not hard-code (1:-1:0): the basis here has
    // leading coefficient 2, putting the cusp at (1:-1/2:0).
    j_cusp := 0;
    cusp_wps_y := CC!0;
    if g eq 2 then
        c1 := CC!Coefficient(fs[g-1], g-1);
        c2 := CC!Coefficient(fs[g],   g);
        cusp_wps_y := -c2 / c1^2;
        j_cusp := InfinityValMatch(cusp_wps_y);
    end if;
    if j_cusp gt 0 then
        if j_cusp in matched then
            error Sprintf("N=%o: collision: cusp at rats[%o] but that index already matched to a CM point", N, j_cusp);
        end if;
        printf "  Cusp -> rats[%o] %o\n", j_cusp, rats[j_cusp];
        Include(~matched, j_cusp);
    elif g eq 2 then
        printf "  WARNING: cusp not matched to a rational point (cusp WPS-y=%o)\n", cusp_wps_y;
    else
        printf "  WARNING: cusp detection not implemented for hyperelliptic genus %o\n", g;
    end if;

    // idx -> disc map for callers (0 = cusp sentinel). Separate from the
    // involution-search map below, which excludes the cusp.
    idx_to_disc_full := AssociativeArray();
    for disc in Keys(disc_to_idx) do idx_to_disc_full[disc_to_idx[disc]] := disc; end for;
    if j_cusp gt 0 then idx_to_disc_full[j_cusp] := 0; end if;

    // Remaining unmatched points are exceptional.
    exceptional_idxs := [j : j in [1..#rats] | j notin matched];
    printf "Labelled %o CM+cusp, %o exceptional\n", #matched, #exceptional_idxs;
    for j in exceptional_idxs do printf "  exceptional: rats[%o] = %o\n", j, rats[j]; end for;
    if #exceptional_idxs eq 0 then return exceptional_idxs, [* *], true, "", idx_to_disc_full; end if;

    // Build idx -> disc map for the involution search.
    idx_to_disc := AssociativeArray();
    for disc in Keys(disc_to_idx) do idx_to_disc[disc_to_idx[disc]] := disc; end for;

    involution_pairs := HyperellipticInvolutionSearch(C, rats, exceptional_idxs, idx_to_disc);

    exc_covered := {e[1] : e in involution_pairs};
    all_matched := {j : j in exceptional_idxs} subset exc_covered;
    printf "Involution pairs found: %o\n", #involution_pairs;
    for e in involution_pairs do
        if #e[4] gt 0 then
            cm_str := "{ " * Join([Sprint(d) : d in Sort([s : s in e[4]])], ", ") * " }";
            printf "  rats[%o] = %o is hyperelliptic involution of rats[%o] (CM disc %o)\n",
                e[1], rats[e[1]], e[2], cm_str;
        else
            printf "  rats[%o] = %o and rats[%o] = %o are a hyperelliptic involution pair\n",
                e[1], rats[e[1]], e[2], rats[e[2]];
        end if;
    end for;
    printf "All exceptional points explained: %o\n", all_matched;

    return exceptional_idxs, involution_pairs, all_matched, "", idx_to_disc_full;
end function;

// Projective residual between nonzero complex vectors.
// Returns sin(theta), where theta is the angle between the lines spanned by p
// and q; hence 0 iff they represent the same projective point. Invariant under
// independent rescaling of either vector.
//
// Computed via
// ||p ∧ q||^2 = sum_{i<j} |p_i q_j - p_j q_i|^2,
// and normalized by ||p|| ||q||.
function ProjectiveResidual(p, q)
    if #p ne #q or #p eq 0 then return 1; end if;
    g := #p;
    np2 := &+[Abs(p[l])^2 : l in [1..g]];
    nq2 := &+[Abs(q[l])^2 : l in [1..g]];
    if np2 eq 0 or nq2 eq 0 then return 1; end if;
    wedge2 := Parent(np2)!0;
    for i in [1..g-1] do
        for j in [i+1..g] do
            wedge2 +:= Abs(p[i]*q[j] - p[j]*q[i])^2;
        end for;
    end for;
    // Return sin(theta), not sin^2(theta), to match the linear scale of other
    // residuals and tolerances.
    return Sqrt(wedge2) / Sqrt(np2*nq2);
end function;

function IsProjectivelyEquivalent(p, q, tol)
    return ProjectiveResidual(p, q) lt tol;
end function;


function RecognizeRational(val, CC_low)
    // Try to recognize val as a rational number via PowerRelation.
    // Returns (true, rat) or (false, 0).
    if Abs(Imaginary(CC_low!val)) gt 10^-3 then
        return false, Rationals()!0;
    end if;
    Ru<u> := PolynomialRing(Rationals());
    pr := PowerRelation(Real(CC_low!val), 1);
    cofs := [Round(c) : c in Coefficients(pr)];
    if #cofs ge 2 and cofs[2] ne 0 then
        return true, Rationals()!(-cofs[1]/cofs[2]);
    end if;
    return false, Rationals()!0;
end function;


// Compute integer hyperplane coefficients from g-1 rational points in P^{g-1}.
// Returns (true, vi) or (false, []) if degenerate.
function HyperplaneFromPoints(g, pts_coords)
    M := Matrix(Rationals(), pts_coords);
    if Rank(M) lt g - 1 then return false, []; end if;
    ker := Basis(Kernel(Transpose(M)));
    if #ker ne 1 then return false, []; end if;
    v := ker[1];
    lcm_d := LCM([Denominator(v[l]) : l in [1..g]]);
    vi := [Integers()!(v[l]*lcm_d) : l in [1..g]];
    gv := GCD(vi); if gv ne 0 then vi := [vi[l] div gv : l in [1..g]]; end if;
    return true, vi;
end function;

// Intersect X with the hyperplane vi·z = 0.
// Returns (plane_eqn, comp_degs, on_plane_indices).
function IntersectWithHyperplane(X, rats, vi)
    g := Genus(X);
    P_amb := AmbientSpace(X); R_amb := CoordinateRing(P_amb);
    plane_eqn := &+[vi[l]*R_amb.l : l in [1..g]];
    Scut := Scheme(P_amb, DefiningEquations(X) cat [plane_eqn]);
    on_plane := [l : l in [1..#rats] | &+[vi[m]*Eltseq(rats[l])[m] : m in [1..g]] eq 0];
    comp_degs := Sort([Degree(c) : c in IrreducibleComponents(Scut)]);
    return plane_eqn, comp_degs, on_plane;
end function;

// Recognize a coordinate via PowerRelation(degree 2).
// Returns <0,0> if zero, <1, rat> if rational, <2, poly> if quadratic algebraic.
function RecognizeCoord(val, tol, CC)
    Ru<u> := PolynomialRing(Rationals());
    if Abs(val) lt tol then return <0, Ru!0>; end if;
    pr := PowerRelation(val, 2);
    cofs := [Round(c) : c in Coefficients(pr)];
    f := Ru!cofs;
    // cofs[2] needs guarding the way RecognizeRational above guards it: a
    // degree-0 relation out of PowerRelation leaves a single coefficient. The
    // genuine-zero case already returned at the tol check, so reaching here
    // with no usable linear coefficient means recognition failed on a nonzero
    // value. There is no failure tag in this return convention and <0, 0> is
    // taken -- it asserts the coordinate IS zero, which would quietly corrupt
    // the point RecognizePoint builds. Say so instead of fabricating.
    if Degree(f) le 1 then
        error if #cofs lt 2 or cofs[2] eq 0,
            Sprintf("RecognizeCoord: no usable linear relation for val=%o (PowerRelation gave %o)", val, cofs);
        return <1, Rationals()!(-cofs[1]/cofs[2])>;
    end if;
    f := f / LeadingCoefficient(f);
    facts := Factorization(f);
    if exists{g : g in facts | Degree(g[1]) eq 1} then
        lin := [g[1] : g in facts | Degree(g[1]) eq 1];
        rr := [-Coefficient(g, 0)/LeadingCoefficient(g) : g in lin];
        _, idx := Minimum([Abs(CC!r - val) : r in rr]);
        return <1, rr[idx]>;
    end if;
    return <2, f>;
end function;

// Recognize a CC-projective point as a point over a number field.
// Applies RecognizeCoord to each coordinate; builds K as compositum of quadratic fields found.
function RecognizePoint(ev, CC)
    tol := 10^-3; n := #ev;
    recs := [RecognizeCoord(ev[j], tol, CC) : j in [1..n]];
    quad_polys := [];
    for j in [1..n] do
        if recs[j][1] eq 2 and not recs[j][2] in quad_polys then
            Append(~quad_polys, recs[j][2]);
        end if;
    end for;
    if #quad_polys eq 0 then
        coords := [recs[j][1] eq 0 select Rationals()!0 else recs[j][2] : j in [1..n]];
        return Rationals(), coords;
    end if;
    K := NumberField(quad_polys[1]);
    for j in [2..#quad_polys] do K := Compositum(K, NumberField(quad_polys[j])); end for;
    rts_K := Roots(PolynomialRing(CC)!Eltseq(DefiningPolynomial(K)));
    emb := hom<K -> CC | rts_K[1][1]>;
    function LiftToK(rec, val)
        if rec[1] eq 0 then return K!0; end if;
        if rec[1] eq 1 then return K!(rec[2]); end if;
        rts := Roots(PolynomialRing(K)!Eltseq(rec[2]));
        best := rts[1][1]; best_err := Abs(emb(best) - CC!val);
        for r in rts do
            err := Abs(emb(r[1]) - CC!val);
            if err lt best_err then best := r[1]; best_err := err; end if;
        end for;
        return best;
    end function;
    return K, [LiftToK(recs[j], ev[j]) : j in [1..n]];
end function;

// Compute integer hyperplane coefficients through exc_coords (rational) and
// a CM point given by ev1 (CC-valued), using exact K-coordinates from RecognizePoint.
// Returns (true, vi) with vi a list of g integers, or (false, []) if degenerate.
function PlaneFromCMPair(exc_coords, ev1, CC)
    K, coords1 := RecognizePoint(ev1, CC);
    if Type(K) eq FldRat then
        // CM point recognized as rational; cannot determine a unique plane this way.
        return false, [];
    end if;
    g := #exc_coords;
    d := Degree(K);
    // Build (d+1) x g matrix over Q.
    // Row 0: rational exceptional point.
    // Rows 1..d: i-th Q-basis coefficient of each coords1[j].
    rows := [[Rationals()!c : c in exc_coords]];
    for i in [1..d] do
        Append(~rows, [Eltseq(coords1[j])[i] : j in [1..g]]);
    end for;
    M := Matrix(Rationals(), #rows, g, &cat rows);
    ker := Kernel(M);
    if Dimension(ker) ne 1 then return false, []; end if;
    v := Basis(ker)[1];
    lcm_d := LCM([Denominator(v[l]) : l in [1..g]]);
    vi := [Integers()!(v[l]*lcm_d) : l in [1..g]];
    gv := GCD(vi); if gv ne 0 then vi := [vi[l] div gv : l in [1..g]]; end if;
    return true, vi;
end function;

// Rational reconstruction of a CC value via BestApproximation against an
// explicit denominator height bound hb_max (mirrors RationalizeImage in
// src/triple_covers.m). Zero is just the 0/1 case of the same residual check,
// not a special case triggered by being small against a fixed constant.
//
// Returns <0,0> (zero), <1,rat> (nonzero rational), or <2,0> (no uniquely
// identifiable candidate under hb_max, either because the uniqueness bound
// fails or because nothing is within tol). Callers read <2,0> as "not a
// conjugate pair"; it is not a claim that the value is irrational.
function RecognizeRationalWithHeightBound(val, tol, hb_max)
    if Abs(Imaginary(val)) gt tol*(1+Abs(val)) then return <2, Rationals()!0>; end if;
    re := Real(val);
    eps := tol*(1+Abs(re));
    // Uniqueness bound: if 2*eps*hb_max^2 < 1 then the eps-ball around re holds
    // at most one rational of denominator <= hb_max, so a BestApproximation
    // result within eps is the unique candidate under that bound.
    //
    // Check this at hb_max itself, never at a smaller intermediate bound:
    // uniqueness below hbk says nothing about denominators in (hbk, hb_max],
    // which can put a second rational in the same eps-ball.
    //
    // Uniqueness is not proof of rationality; an irrational value can land
    // within eps of the candidate. What makes acceptance safe is the rest of
    // the pipeline: a genuine Galois-conjugate pair is expected to give
    // rational cofactor ratios, and the caller still requires two independent
    // runs to agree plus the plane-residual checks to pass.
    if 2*eps*hb_max^2 ge 1 then return <2, Rationals()!0>; end if;
    r := BestApproximation(re, hb_max);
    if Abs(re - r) le eps then
        return r eq 0 select <0, Rationals()!0> else <1, r>;
    end if;
    return <2, Rationals()!0>;
end function;

// Compute integer hyperplane coefficients through exc_coords (rational) and
// a conjugate pair (ev1, ev2) of CC-valued CM points, using the cofactor method.
//
// The plane through a rational point and a Galois-conjugate pair is rational,
// so the 3 x g CC matrix [exc; ev1; ev2] has cofactors proportional to a
// rational vector. Divide by the largest cofactor to cancel the common complex
// scalar, then recognize each ratio with RecognizeRationalWithHeightBound.
//
// This avoids RecognizePoint / Compositum, which fails here: projective
// normalization mixes the rational and irrational parts across coordinates and
// yields a different-looking (though isomorphic) quadratic field per coord.
//
// tol: reconstruction tolerance, used for the zero-pivot guard and the
// residual check. Callers should pass something stricter than their final
// match tolerance (see CertifiedPlaneFromCMPair's recon_tol vs match_tol): a
// too-loose tolerance here fabricates a plausible but wrong low-height
// rational, and hence a wrong plane, whereas the later match check only has to
// confirm a plane already committed to.
// hb_max: denominator height bound for the reconstruction.
function PlaneFromCMPairCofactor(exc_coords, ev1, ev2, CC, tol, hb_max)
    g := #exc_coords;
    // Guard against failed CM evaluations (EvaluateAtCM returns []): without a full
    // g-vector for each point the 3 x g matrix build below has the wrong length.
    if #ev1 ne g or #ev2 ne g then return false, []; end if;
    pt_Q := [CC!c : c in exc_coords];
    M_pl := Matrix(CC, 3, g, pt_Q cat ev1 cat ev2);
    // Square (g-1)x(g-1) minors from 3 rows need g <= 4, and three points only
    // determine a hyperplane in P^{g-1} for g in {3,4}. Outside that range
    // there is nothing to recover.
    if g lt 3 or g gt 4 then return false, []; end if;
    // Unit-normalize each row so the pivot gate below compares a dimensionless
    // quantity against tol rather than a determinant that scales with the raw
    // coordinate sizes. Every vi_cc[l] is built from the same rows, so this
    // scales them all identically and leaves the ratios, and the plane,
    // unchanged.
    for r in [1..3] do
        rn := Sqrt(&+[Abs(M_pl[r,c])^2 : c in [1..g]]);
        if rn eq 0 then return false, []; end if;
        for c in [1..g] do
            M_pl[r,c] /:= rn;
        end for;
    end for;
    vi_cc := [];
    for col in [1..g] do
        cols := [c : c in [1..g] | c ne col];
        // Use the last g-1 rows of M_pl (row index = 4-g+ii) so the minor is square.
        // g=4: rows 1..3 (all, same as before); g=3: rows 2..3 (ev1, ev2).
        // Cofactor expansion along row 1 of M_pl: vi satisfies M_pl*vi = 0 for all g.
        minor := Matrix(CC, [[M_pl[4-g+ii, cols[j]] : j in [1..g-1]] : ii in [1..g-1]]);
        Append(~vi_cc, (-1)^(col+1) * Determinant(minor));
    end for;
    _, piv := Maximum([Abs(vi_cc[l]) : l in [1..g]]);
    if Abs(vi_cc[piv]) lt tol then return false, []; end if;
    vi_rat := [Rationals()!0 : l in [1..g]];
    vi_rat[piv] := 1;
    ok := true;
    for l in [1..g] do
        if l eq piv then continue; end if;
        ratio := vi_cc[l] / vi_cc[piv];
        rec := RecognizeRationalWithHeightBound(ratio, tol, hb_max);
        if rec[1] eq 0 then
            vi_rat[l] := 0;
        elif rec[1] eq 1 then
            vi_rat[l] := rec[2];
        else
            ok := false; break;  // non-rational ratio: evs[i],evs[j] not a conjugate pair
        end if;
    end for;
    if not ok then return false, []; end if;
    lcm_d := LCM([Denominator(vi_rat[l]) : l in [1..g]]);
    vi := [Integers()!(vi_rat[l] * lcm_d) : l in [1..g]];
    gv := GCD(vi); if gv ne 0 then vi := [vi[l] div gv : l in [1..g]]; end if;
    if &and[vi[l] eq 0 : l in [1..g]] then return false, []; end if;
    return true, vi;
end function;

// Dimensionless residual of ev against the plane vi.z = 0. Both vi and ev are
// only defined up to a nonzero scalar, so normalizing by their norms keeps a
// comparison against a fixed tolerance meaningful however large the plane's
// integer coefficients get. A raw |vi.ev| check would not be.
function ScaleInvariantResidual(vi, ev)
    if #vi ne #ev or #vi eq 0 then return 1; end if;
    g := #vi;
    num   := Abs(&+[vi[l]*ev[l] : l in [1..g]]);
    nv    := Sqrt(&+[Parent(ev[1])!(vi[l]^2) : l in [1..g]]);
    enorm := Sqrt(&+[Abs(ev[l])^2 : l in [1..g]]);
    if nv eq 0 or enorm eq 0 then return 1; end if;
    return num / (Abs(nv) * enorm);
end function;

// Projective distance between two evaluations of what should be the same
// point, e.g. the full-length and half-length truncations of a q-expansion.
// Used as a direct per-run estimate of numerical noise.
function ScaleInvariantDistance(ev1, ev2)
    return ProjectiveResidual(ev1, ev2);
end function;

// Quality gate on an evaluation, plus a match tolerance scaled to its own
// measured noise. Returns (ok, tol):
//
//   ok = false: observed_error exceeds error_max, so this evaluation cannot
//     support any match/no-match call. Report inconclusive and raise precision;
//     do not fall back to a loosened residual check, which against
//     untrustworthy data is evidence neither way.
//   ok = true: tol = Maximum(C*observed_error, floor). The ceiling lives on
//     observed_error, not on tol, so a noisier but still acceptable run is
//     judged by what its digits can support. A fixed ceiling on tol would be
//     unclearable by exactly those runs, however genuine the match.
//   floor = 10^(-0.8*prec_lo), pinned to the weaker run, so a fortuitous
//     observed_error of 0 cannot collapse tol and reject everything.
function AdaptiveTol(observed_error, C, error_max, prec_lo)
    if observed_error gt error_max then
        return false, 0;  // tol is meaningless when ok=false; caller must not use it
    end if;
    floor := 10^(-Floor(0.8*prec_lo));
    tol := Maximum(C*observed_error, floor);
    return true, tol;
end function;

// Evaluate every Gamma_0(N)*-orbit representative of CM discriminant d at
// precision `prec`, using fs truncated to `len` terms. Keyed by orbit_id,
// CMTauOrbits' position in its own precision-independent sort order, which is
// stable across (prec,len) choices unlike list position after non-convergent
// entries are dropped.
//
// An orbit_id appears only if EvaluateAtCM converges at both `len` and `len/2`
// terms and the two agree. The stored observed_error is the scale-invariant
// gap between them, i.e. this run's measured truncation noise, which
// AdaptiveTol then consumes.
function EvaluateOrbitsWithConvergence(d, N, fs, ell_pts, disc_ell_pts, prec, len)
    CC := ComplexField(prec);
    taus := CMTauReps(d, N, CC);
    fs_full := [ChangePrecision(f, Minimum(len, AbsolutePrecision(f))) : f in fs];
    fs_half := [ChangePrecision(f, Minimum(Ceiling(len/2), AbsolutePrecision(f))) : f in fs];
    out := AssociativeArray();
    for orbit_id in [1..#taus] do
        tau := taus[orbit_id];
        ev_full := EvaluateAtCM(fs_full, tau, CC, d, ell_pts, disc_ell_pts, N);
        ev_half := EvaluateAtCM(fs_half, tau, CC, d, ell_pts, disc_ell_pts, N);
        if #ev_full eq 0 or #ev_half eq 0 or #ev_full ne #ev_half then continue; end if;
        out[orbit_id] := <ev_full, ScaleInvariantDistance(ev_full, ev_half)>;
    end for;
    return CC, out;
end function;

// The definition of a trustworthy numeric CM evaluation, used by both
// CertifiedPlaneFromCMPair and AlgebraicDeg2Matches.
//
// "lo" and "hi" are independent runs: different working precision (prec_lo vs
// prec_hi) and different q-expansion length (half the available terms vs all
// of them), so they are not two precisions applied to one series. Each also
// passes its own full-vs-half-length check in EvaluateOrbitsWithConvergence.
//
// Returns CC_lo, CC_hi, and orbit_id -> <ev_lo, ev_hi, observed_error>, where
// observed_error is the worse of the two runs' noise. An orbit that converged
// in only one run is absent, so callers compare orbits present in both by
// construction rather than by list position.
function CertifiedConjugateEvaluations(d, N, fs, ell_pts, disc_ell_pts, prec_lo, prec_hi)
    len_hi := Minimum([AbsolutePrecision(f) : f in fs]);
    len_lo := Ceiling(len_hi/2);
    CC_lo, evs_lo := EvaluateOrbitsWithConvergence(d, N, fs, ell_pts, disc_ell_pts, prec_lo, len_lo);
    CC_hi, evs_hi := EvaluateOrbitsWithConvergence(d, N, fs, ell_pts, disc_ell_pts, prec_hi, len_hi);
    out := AssociativeArray();
    for orbit_id in Keys(evs_lo) do
        if not IsDefined(evs_hi, orbit_id) then continue; end if;
        // Each run's internal full-vs-half-length estimate is blind to error
        // correlated between its own two truncations. cross_err, the gap
        // between the lo and hi full-length values, is computed at a different
        // precision entirely and catches that. Fold it in with Maximum rather
        // than replacing the internal estimates: either disagreement is
        // equally good evidence that this orbit is untrustworthy past err.
        cross_err := ScaleInvariantDistance(evs_lo[orbit_id][1], evs_hi[orbit_id][1]);
        err := Maximum([evs_lo[orbit_id][2], evs_hi[orbit_id][2], cross_err]);
        out[orbit_id] := <evs_lo[orbit_id][1], evs_hi[orbit_id][1], err>;
    end for;
    return CC_lo, CC_hi, out;
end function;

// Recover the primitive integer hyperplane through the rational exceptional
// point exc_coords and each Galois-conjugate pair among discriminant d's orbit
// representatives, from the two independent runs of
// CertifiedConjugateEvaluations. A candidate is accepted only if:
//
//   1. its observed error is within error_max_recon, checked before any
//      reconstruction is attempted: recognizing a rational from data known to
//      be too noisy risks a wrong low-height answer, which is worse than
//      reporting nothing;
//   2. both runs recover the same primitive integer vector up to sign, at the
//      recon_C-scaled tolerance. A coincidental rational recognition is very
//      unlikely to survive redoing the work with different taus, series
//      length, and precision;
//   3. that vector annihilates exc_coords exactly. exc_coords is exact
//      rational data, so an exact check costs nothing and beats a numeric one;
//   4. its observed error is also within error_max_match. Separate from (1)
//      because recognizing a rational and certifying a geometric match are
//      different questions: succeeding at (1) does not make vi accurate
//      enough for (5);
//   5. both conjugates in both runs have scale-invariant residual below the
//      resid_C-scaled match tolerance from AdaptiveTol.
//
// Failures are dropped with a printf naming the check that failed.
//
// Returns <i, j, vi>: the orbit_id pair and the integer vector, per certified
// pair. Usually 0 or 1 entries per d, since PlaneFromCMPairCofactor itself
// rejects a non-conjugate cross-pair when h(D) > 2 gives several pairs.
function CertifiedPlaneFromCMPair(exc_coords, d, N, fs, ell_pts, disc_ell_pts :
    prec_lo := 200, prec_hi := 600, resid_C := 10^3, recon_C := 10,
    error_max_recon := 10^-12, error_max_match := 10^-12, cofactor_hb := 10^12)
    CC_lo, CC_hi, evs := CertifiedConjugateEvaluations(d, N, fs, ell_pts, disc_ell_pts, prec_lo, prec_hi);
    certified := [* *];
    ids := Sort(Setseq(Keys(evs)));
    if #ids lt 2 then return certified; end if;
    for ii in [1..#ids] do
        for jj in [ii+1..#ids] do
            i := ids[ii]; j := ids[jj];
            observed_error := Maximum(evs[i][3], evs[j][3]);
            ok_recon, recon_tol := AdaptiveTol(observed_error, recon_C, error_max_recon, prec_lo);
            if not ok_recon then
                printf "  CertifiedPlaneFromCMPair: D=%o orbit pair (%o,%o) INCONCLUSIVE; observed error %o exceeds error_max_recon %o (insufficient accuracy to attempt reconstruction)\n",
                    d, i, j, observed_error, error_max_recon;
                continue;
            end if;
            ok_lo, vi_lo := PlaneFromCMPairCofactor(exc_coords, evs[i][1], evs[j][1], CC_lo, recon_tol, cofactor_hb);
            ok_hi, vi_hi := PlaneFromCMPairCofactor(exc_coords, evs[i][2], evs[j][2], CC_hi, recon_tol, cofactor_hb);
            if not ok_lo or not ok_hi then continue; end if;
            if vi_lo ne vi_hi and vi_lo ne [-c : c in vi_hi] then
                printf "  CertifiedPlaneFromCMPair: D=%o orbit pair (%o,%o) INCONCLUSIVE; disagreement between independent (precision,length) runs: %o vs %o\n",
                    d, i, j, vi_lo, vi_hi;
                continue;
            end if;
            vi := vi_lo;
            if &+[vi[l]*exc_coords[l] : l in [1..#vi]] ne 0 then
                continue;  // certified numerically, but not the plane through exc_coords
            end if;
            ok_match, match_tol := AdaptiveTol(observed_error, resid_C, error_max_match, prec_lo);
            if not ok_match then
                printf "  CertifiedPlaneFromCMPair: D=%o orbit pair (%o,%o) INCONCLUSIVE; observed error %o exceeds error_max_match %o (reconstruction succeeded, but not accurate enough to certify a match)\n",
                    d, i, j, observed_error, error_max_match;
                continue;
            end if;
            resids := [ScaleInvariantResidual(vi, evs[i][1]), ScaleInvariantResidual(vi, evs[j][1]),
                       ScaleInvariantResidual(vi, evs[i][2]), ScaleInvariantResidual(vi, evs[j][2])];
            if Maximum(resids) gt match_tol then
                printf "  CertifiedPlaneFromCMPair: D=%o orbit pair (%o,%o) INCONCLUSIVE; max residual %o exceeds adaptive match tol %o (observed error %o)\n",
                    d, i, j, Maximum(resids), match_tol, observed_error;
                continue;
            end if;
            Append(~certified, <i, j, vi>);
        end for;
    end for;
    return certified;
end function;

// Which h2_data conjugate pairs numerically satisfy the hyperplane vi.z = 0.
// Returns the discriminants d whose conjugates both land on the hyperplane.
function MatchH2DataToHyperplane(vi, h2_data, CC, tol)
    matches := [* *];
    for entry in h2_data do
        d := entry[1]; evs := entry[2];
        // Require >= 2 evaluations on the plane, a full Galois pair. Counting
        // rather than requiring exactly 2 handles discriminants with more than
        // 2 Heegner forms, e.g. N=310, D=-55 has 4.
        n_on := #{l : l in [1..#evs] | ScaleInvariantResidual(vi, evs[l]) lt tol};
        if n_on ge 2 then
            Append(~matches, d);
        end if;
    end for;
    return matches;
end function;

// Change basis of (X, fs) from Magma's all_diag_basis to the target basis C_F,
// a g x g rational matrix whose rows are the target forms' q^1..q^g
// coefficients. Applying the change geometrically via Automorphism on the
// ambient P^(g-1) preserves the canonical model equations (1 quadric + 1 cubic
// for g=4); re-deriving them from series would instead give many cubics.
// Magma maps row-vectors as v_new = v_old * T, hence Transpose(M).
// Returns (M, fs_new, X_new, phi), phi mapping points of X to points of X_new.
function ChangeOfBasis(X, fs, C_F)
    g := Genus(X);
    C_G := Matrix(Rationals(), g, g, [[Coefficient(fs[i], j) : j in [1..g]] : i in [1..g]]);
    M := C_F * C_G^(-1);
    fs_new := [&+[M[i,j]*fs[j] : j in [1..g]] : i in [1..g]];
    P := AmbientSpace(X);
    phi := Automorphism(P, Transpose(M));
    X_new := phi(X);
    assert Genus(X_new) eq g;
    return M, fs_new, X_new, phi;
end function;

// Sign-normalized key for a primitive integer plane vector: vi and -vi are the
// same hyperplane, so negate to make the first nonzero entry positive. Lets
// callers drop a plane reached twice before paying for
// IntersectWithHyperplane and IrreducibleComponents on it again.
function CanonicalPlaneKey(vi)
    for c in vi do
        if c ne 0 then
            return (c gt 0) select vi else [-x : x in vi];
        end if;
    end for;
    return vi;
end function;

// Search 1: hyperplanes through the exceptional point and (g-2)-subsets of
// known rational points, for genus 3 through 6. Returns all-rational planes
// (max degree 1) and planes with a degree-2 component, both as entries
// <pt_idxs, plane_eqn, comp_degs, on_plane>.
//
// Distinct subsets hit the same plane whenever more than g-1 known rational
// points are coplanar with the exceptional point; at N=137 three of them are,
// so all 3 of its 2-element subsets rediscover one plane. seen_keys dedups
// these before the expensive intersection, so each geometry is reported and
// CM-matched once.
function CoplanaritySearch1(X, rats, exc_idx, known_rat_idxs)
    g := Genus(X);
    // g >= 3 is the only bound: below it X is not canonically embedded and
    // k = g-2 would be non-positive. There is no upper bound -- the exceptional
    // point together with k of the known points is g-1 points, which cut out a
    // hyperplane in P^{g-1} at every genus.
    assert g ge 3;
    exc_coords := Eltseq(rats[exc_idx]);
    results_deg1 := [* *];
    results_deg2 := [* *];
    k := g - 2;  // number of additional rational points needed
    seen_keys := {};
    for S in Subsets(Set(known_rat_idxs), k) do
        S_list := Sort(Setseq(S));
        ok, vi := HyperplaneFromPoints(g,
            [exc_coords] cat [Eltseq(rats[j]) : j in S_list]);
        if not ok then continue; end if;
        key := CanonicalPlaneKey(vi);
        if key in seen_keys then continue; end if;
        Include(~seen_keys, key);
        eqn, degs, on_plane := IntersectWithHyperplane(X, rats, vi);
        if #degs eq 0 then continue; end if;
        if Maximum(degs) le 1 then
            Append(~results_deg1, <S_list, eqn, degs, on_plane>);
        elif Maximum(degs) le 2 then
            Append(~results_deg2, <S_list, eqn, degs, on_plane>);
        end if;
    end for;
    return results_deg1, results_deg2;
end function;

// Search 2: hyperplanes through the exceptional point and an h=2 conjugate
// pair, certified by CertifiedPlaneFromCMPair (see its header for the checks).
// A candidate that cannot be certified is dropped, never labelled anyway.
// Returns <D, plane_eqn, comp_degs, on_plane> with max component degree 2.
//
// Genus: g in {3,4} only. Three points span a hyperplane just in P^2 and P^3,
// and PlaneFromCMPairCofactor refuses the rest. Covering g >= 5 would need
// g-3 further known rational points to pin the plane down; that is out of
// scope, and the caller skips this search with a warning at those genera
// rather than pretending it ran.
function CoplanaritySearch2(X, rats, exc_idx, d, N, fs, ell_pts, disc_ell_pts :
    prec_lo := 200, prec_hi := 600, resid_C := 10^3, recon_C := 10,
    error_max_recon := 10^-12, error_max_match := 10^-12)
    exc_coords := [Rationals()!c : c in Eltseq(rats[exc_idx])];
    results := [* *];
    seen_eqns := [];
    certs := CertifiedPlaneFromCMPair(exc_coords, d, N, fs, ell_pts, disc_ell_pts :
        prec_lo := prec_lo, prec_hi := prec_hi, resid_C := resid_C, recon_C := recon_C,
        error_max_recon := error_max_recon, error_max_match := error_max_match);
    for c in certs do
        vi := c[3];
        if &and[vi[l] eq 0 : l in [1..#vi]] then continue; end if;
        eqn, degs, on_plane := IntersectWithHyperplane(X, rats, vi);
        if #degs eq 0 or Maximum(degs) gt 2 then continue; end if;
        // CertifiedPlaneFromCMPair's exact-containment check already guarantees
        // this. It is an invariant, not a filter: a failure means something
        // upstream is inconsistent and should not be silently dropped.
        error if exc_idx notin on_plane,
            Sprintf("CoplanaritySearch2: certified vi %o does not contain exc_idx %o, invariant violated", vi, exc_idx);
        if exists{e : e in seen_eqns | e eq eqn or e eq -eqn} then continue; end if;
        Append(~seen_eqns, eqn);
        Append(~results, <d, eqn, degs, on_plane>);
    end for;
    return results;
end function;

// Match required rational CM discriminants to rats; return set of matched indices
// and a disc -> rat_idx map.
function MatchRationalCMPoints(N, fs, rats_cc, rats, CC, tol, rat_cm_discs, ell_pts, disc_ell_pts)
    matched := {};
    disc_to_idx := AssociativeArray();
    fail_reason := "";
    nfail := 0;
    for disc in rat_cm_discs do
        // One tau per <Gamma_0(N), AL>-orbit, so distinct entries are distinct
        // points of X_0(N)* and a repeat hit is impossible rather than merely
        // tolerated. It falls through to the collision error below.
        taus := CMTauReps(disc, N, CC);
        expected := DegreeOfFieldOfDefinitionOfCMPoint(N,disc);
        error if #taus ne expected,
            Sprintf("N=%o: disc %o has %o Gamma_0(N)*-orbits but the field of definition has degree %o",
                    N, disc, #taus, expected);
        nfound := 0;
        eval_failed := false;
        for tau in taus do
            ev := EvaluateAtCM(fs, tau, CC, disc, ell_pts, disc_ell_pts, N);
            if #ev eq 0 then eval_failed := true; continue; end if;
            idx := [j : j in [1..#rats_cc] | IsProjectivelyEquivalent(ev, rats_cc[j], tol)];
            if #idx gt 0 then
                if idx[1] in matched then
                    // Both ways idx[1] can already be matched are fatal; only
                    // the message differs, so nobody goes hunting for a
                    // colliding other discriminant that isn't there.
                    if IsDefined(disc_to_idx, disc) and idx[1] in disc_to_idx[disc] then
                        error Sprintf("N=%o: disc=%o matched rats[%o] twice: two Gamma_0(N)*-orbit representatives of the same discriminant landed on one rational point (numerically coincident within tol?)", N, disc, idx[1]);
                    end if;
                    error Sprintf("N=%o: collision: disc=%o matched to rats[%o] but that index already in matched", N, disc, idx[1]);
                end if;
                printf "  disc = %o -> rats[%o] -> %o (CM)\n", disc, idx[1], rats[idx[1]];
                Include(~matched, idx[1]);
                // The indices this disc's images matched, in the order found. A
                // disc whose field of definition has degree > 1 contributes
                // several, one per tau.
                if not IsDefined(disc_to_idx, disc) then
                    disc_to_idx[disc] := [Integers()|];
                end if;
                Append(~disc_to_idx[disc], idx[1]);
                nfound +:= 1;
                if nfound ge expected then break; end if;
            end if;
        end for;
        if nfound lt expected then
            if eval_failed then
                fail_reason := Sprintf("D=%o: EvaluateAtCM returned zero (needs higher eval_prec)", disc);
            else
                // The value looked nonzero but matched no rats[j]. That does not
                // mean the point is absent: at an elliptic point the
                // n^deriv_order-weighted value from EvaluateAtCM can be
                // under-converged while the classical zero-gate still looks
                // small. Test convergence directly with a half-length series
                // rather than trusting the zero-gate as a proxy for it.
                best_ev := [];
                best_tau := CC!0;
                for tau_diag in taus do
                    ev_diag := EvaluateAtCM(fs, tau_diag, CC, disc, ell_pts, disc_ell_pts, N);
                    if #ev_diag gt 0 then best_ev := ev_diag; best_tau := tau_diag; break; end if;
                end for;
                converged := false;
                if #best_ev gt 0 then
                    fs_half := [ChangePrecision(f, Ceiling(AbsolutePrecision(f)/2)) : f in fs];
                    ev_half := EvaluateAtCM(fs_half, best_tau, CC, disc, ell_pts, disc_ell_pts, N);
                    converged := #ev_half gt 0 and IsProjectivelyEquivalent(best_ev, ev_half, tol);
                end if;
                if converged then
                    // Converged and still unmatched: dump the evaluated point
                    // and all rats so the caller can tell whether the CM point
                    // simply has large height or EvaluateAtCM is wrong.
                    printf "  D=%o: evaluated to approx %o\n", disc, [Real(e) : e in best_ev];
                    printf "  Rats (%o points):\n", #rats;
                    for j in [1..#rats] do printf "    rats[%o] = %o\n", j, rats[j]; end for;
                    fail_reason := Sprintf("D=%o: evaluation ok but point not found in PointSearch results", disc);
                else
                    printf "  D=%o: half-length series disagrees with full-length series, not converged at this eval_prec\n", disc;
                    fail_reason := Sprintf("D=%o: evaluation not converged at this eval_prec (half-length series disagrees; needs higher eval_prec)", disc);
                end if;
            end if;
            nfail +:= 1;
            break;
        end if;
    end for;
    return matched, nfail, disc_to_idx, fail_reason;
end function;

// Status vocabulary for the three helpers below and for AlgebraicDeg2Matches.
// Two levels of outcome, easy to confuse.
//
// Per (component, disc), in `records`:
//   "confirmed"     a bijection at both precisions, from an orbit pair within
//                   error_max_match.
//   "rejected"      every orbit pair was accurate enough to judge and none
//                   gave a bijection. A confident negative.
//   "inconclusive"  no orbit pair was accurate enough to judge either way.
//                   The gray zone; never treat it as either verdict.
//
// Per component, in `comp_status`, once every field-compatible disc is tried:
//   "confirmed"     exactly one disc confirmed.
//   "ambiguous"     several discs independently confirmed on one component.
//                   Generically at most one disc's field matches a fixed
//                   quadratic field, but coincidences happen. Surfaced rather
//                   than resolved: nothing here picks a best candidate by
//                   residual or by test order.
//   "inconclusive"  nothing confirmed, something still inconclusive. The gray
//                   zone outranks a negative: while a candidate might yet
//                   resolve at higher precision, the component is not
//                   confidently unlabelled.
//   "unlabelled"    nothing confirmed, everything rejected. A confident
//                   negative about the component.

// Pure decision table, split out so it is unit-testable without real CM data.
// "rejected" demands that every orbit pair was trustworthy and every orbit
// representative present. Otherwise an untested or too-noisy pair, possibly
// the actual Galois-conjugate one for a class number > 2 disc, could be masked
// by an accurate but irrelevant pair failing the bijection test.
function DiscStatusOnComponent(found, any_pair_trustworthy, all_pairs_trustworthy, all_orbits_present)
    if found then return "confirmed"; end if;
    if all_orbits_present and any_pair_trustworthy and all_pairs_trustworthy then
        return "rejected";
    end if;
    return "inconclusive";
end function;

// Per-component aggregate, another pure decision table. Returns the status
// plus this component's contributions to the caller's global matches and
// inconclusive sets. See AlgebraicDeg2Matches's header for the four statuses.
//
// Both the confirmed and ambiguous cases pass inconclusive_discs through: a
// disc that stayed inconclusive here is unresolved regardless of what happened
// to the other candidates on the same component, so it must keep surfacing
// rather than be dropped because a neighbour was confirmed.
function ComponentAggregate(confirmed_discs, inconclusive_discs)
    if #confirmed_discs gt 1 then
        return "ambiguous", {Integers()|}, confirmed_discs join inconclusive_discs;
    end if;
    if #confirmed_discs eq 1 then
        return "confirmed", confirmed_discs, inconclusive_discs;
    end if;
    if #inconclusive_discs gt 0 then
        return "inconclusive", {Integers()|}, inconclusive_discs;
    end if;
    return "unlabelled", {Integers()|}, {Integers()|};
end function;

// Flatten comp_status into <comp_idx, disc> pairs for every disc in every
// component whose status is in wanted_statuses. LabelAndAnalyze builds its
// component-match lists from this, rather than filtering records against a
// plane-wide disc set; see its call sites for why that alternative is unsafe.
function ComponentStatusPairs(comp_status, wanted_statuses)
    out := [* *];
    for c in comp_status do
        if c[2] in wanted_statuses then
            for d in c[3] do
                Append(~out, <c[1], d>);
            end for;
        end if;
    end for;
    return out;
end function;

// For a plane with degree-2 intersection components, decide which discriminant
// in deg2pts lies on each component. Two stages per (component, disc) pair,
// neither using numeric coordinate recognition of the CM evaluation:
//
//   (1) field isomorphism, a cheap exact prefilter. A mismatch drops the pair
//       entirely and is never recorded: the disc was never a candidate here,
//       which is not the same as being rejected.
//   (2) the component's own exact points, from RationalPoints over its
//       splitting field, embedded into CC at both precisions and matched
//       projectively against the disc's CertifiedConjugateEvaluations.
//       AdaptiveTol gates each orbit pair, so a pair noisier than
//       error_max_match is never compared at all.
//
// Tracking is per (component, disc), not per disc: one plane can have two
// conjugate-pair components for different discs, and failing on one must not
// stop that disc being confirmed on the other.
//
// Returns (matches, inconclusive, records, comp_status) in the statuses above.
// matches holds the sole confirmed disc of each confirmed component, so an
// ambiguous component contributes none. inconclusive holds discs sitting on an
// inconclusive or ambiguous component, both meaning "not a usable negative". A
// disc whose records are all "rejected" is in neither.
function AlgebraicDeg2Matches(X, plane_eqn, deg2pts, N, fs, ell_pts, disc_ell_pts :
    prec_lo := 200, prec_hi := 600, resid_C := 10^3, error_max_match := 10^-12)
    records := [* *];
    comp_status := [* *];
    matches := {Integers()|};
    inconclusive := {Integers()|};
    if #Keys(deg2pts) eq 0 then return matches, inconclusive, records, comp_status; end if;
    P_amb := AmbientSpace(X);
    Scut := Scheme(P_amb, DefiningEquations(X) cat [plane_eqn]);
    comp_idx := 0;
    for comp in IrreducibleComponents(Scut) do
        if Degree(comp) ne 2 then continue; end if;
        comp_idx +:= 1;
        _, split_fld := PointsOverSplittingField(comp);
        comp_nf := NumberField(AbsolutePolynomial(split_fld));
        pts_K   := RationalPoints(BaseChange(comp, comp_nf));
        if #pts_K ne 2 then
            // Non-reduced or tangential intersection, so the component is not a
            // genuine conjugate pair and no bijection check is possible. Every
            // field-matching disc is inconclusive, and so is the component.
            printf "  AlgebraicDeg2Matches: component %o has %o exact points (expected 2), marking field-matching discs inconclusive\n", comp_idx, #pts_K;
            field_matching := {Integers()| d : d in Keys(deg2pts) | exists{F : F in deg2pts[d][2] | IsIsomorphic(comp_nf, F)}};
            for d in field_matching do
                Append(~records, <comp_idx, d, "inconclusive">);
            end for;
            Append(~comp_status, <comp_idx, "inconclusive", field_matching>);
            inconclusive join:= field_matching;
            continue;
        end if;
        coords_K := [Eltseq(p) : p in pts_K];
        def_poly := Eltseq(DefiningPolynomial(comp_nf));
        rt_lo := Roots(PolynomialRing(ComplexField(prec_lo))!def_poly)[1][1];
        rt_hi := Roots(PolynomialRing(ComplexField(prec_hi))!def_poly)[1][1];
        emb_lo := hom<comp_nf -> ComplexField(prec_lo) | rt_lo>;
        emb_hi := hom<comp_nf -> ComplexField(prec_hi) | rt_hi>;
        alg_lo := [[emb_lo(c) : c in cs] : cs in coords_K];
        alg_hi := [[emb_hi(c) : c in cs] : cs in coords_K];
        // alg_lo/alg_hi come from numerical root-finding, so they carry their
        // own error, which every bijection check below depends on but nothing
        // else measures. A poorly-conditioned embedding at prec_lo could fail a
        // genuine match while the CM-side observed_error still looks small,
        // giving a false "rejected" instead of "inconclusive". alg_cross_error
        // is the algebraic side's own lo/hi disagreement, computed once per
        // component. The two embeddings may order the conjugate pair either
        // way, so try both pairings and keep the better.
        CC_lo_component := ComplexField(prec_lo);
        alg_hi_in_lo := [[CC_lo_component!z : z in cs] : cs in alg_hi];
        alg_cross_error := Minimum([
            Maximum([ProjectiveResidual(alg_lo[1], alg_hi_in_lo[1]), ProjectiveResidual(alg_lo[2], alg_hi_in_lo[2])]),
            Maximum([ProjectiveResidual(alg_lo[1], alg_hi_in_lo[2]), ProjectiveResidual(alg_lo[2], alg_hi_in_lo[1])])
        ]);
        confirmed_discs    := {Integers()|};
        rejected_discs     := {Integers()|};
        inconclusive_discs := {Integers()|};
        for d in Keys(deg2pts) do
            // The field of definition is multi-valued, so the component need
            // only match one candidate. A mismatch means d was never a
            // candidate here, so nothing is appended to records.
            if not exists{F : F in deg2pts[d][2] | IsIsomorphic(comp_nf, F)} then
                continue;
            end if;
            _, _, evs := CertifiedConjugateEvaluations(d, N, fs, ell_pts, disc_ell_pts, prec_lo, prec_hi);
            ids := Sort(Setseq(Keys(evs)));
            if #ids lt 2 then
                Append(~records, <comp_idx, d, "inconclusive">);
                Include(~inconclusive_discs, d);
                continue;
            end if;
            // Orbits that fail to converge are simply absent from evs, so guard
            // against reaching "rejected" having tested fewer of d's
            // representatives than exist. The expected count comes from
            // DegreeOfFieldOfDefinitionOfCMPoint, not #CMTauReps: CMTauReps is
            // itself numerical, so a precision-dependent shortfall there would
            // redefine the expected count downward and let a missing orbit pass
            // as "all present".
            all_orbits_present := (#ids eq DegreeOfFieldOfDefinitionOfCMPoint(N, d));
            found := false;
            any_pair_trustworthy := false;   // at least one (i,j) pair had accuracy within error_max_match
            all_pairs_trustworthy := true;   // every (i,j) pair among the present orbit ids was trustworthy
            for ii in [1..#ids] do
                for jj in [ii+1..#ids] do
                    i := ids[ii]; j := ids[jj];
                    // Folding alg_cross_error in here, rather than gating on it
                    // separately, makes a poorly-conditioned embedding degrade
                    // this pair exactly as a poorly-converged CM evaluation
                    // would, routing to "inconclusive" and never "rejected".
                    observed_error := Maximum([evs[i][3], evs[j][3], alg_cross_error]);
                    ok_tol, tol := AdaptiveTol(observed_error, resid_C, error_max_match, prec_lo);
                    if not ok_tol then
                        all_pairs_trustworthy := false;
                        continue;  // this pair can't judge; try others
                    end if;
                    any_pair_trustworthy := true;
                    numeric_lo := [evs[i][1], evs[j][1]];
                    numeric_hi := [evs[i][2], evs[j][2]];
                    bij_lo := exists{perm : perm in [[1,2],[2,1]] |
                        IsProjectivelyEquivalent(alg_lo[1], numeric_lo[perm[1]], tol) and
                        IsProjectivelyEquivalent(alg_lo[2], numeric_lo[perm[2]], tol)};
                    bij_hi := exists{perm : perm in [[1,2],[2,1]] |
                        IsProjectivelyEquivalent(alg_hi[1], numeric_hi[perm[1]], tol) and
                        IsProjectivelyEquivalent(alg_hi[2], numeric_hi[perm[2]], tol)};
                    if bij_lo and bij_hi then found := true; break; end if;
                end for;
                if found then break; end if;
            end for;
            status := DiscStatusOnComponent(found, any_pair_trustworthy, all_pairs_trustworthy, all_orbits_present);
            Append(~records, <comp_idx, d, status>);
            if status eq "confirmed" then
                Include(~confirmed_discs, d);
            elif status eq "rejected" then
                Include(~rejected_discs, d);
            else
                Include(~inconclusive_discs, d);
            end if;
        end for;
        // Aggregate only now that every field-compatible disc has been tried.
        comp_stat, matches_add, inconclusive_add := ComponentAggregate(confirmed_discs, inconclusive_discs);
        matches join:= matches_add;
        inconclusive join:= inconclusive_add;
        if comp_stat eq "confirmed" then
            Append(~comp_status, <comp_idx, "confirmed", confirmed_discs>);
            // Discs left inconclusive on a component that also confirmed one
            // get their own entry, so ComponentStatusPairs still reports them.
            if #inconclusive_discs gt 0 then
                Append(~comp_status, <comp_idx, "inconclusive", inconclusive_discs>);
            end if;
        elif comp_stat eq "ambiguous" then
            printf "  AlgebraicDeg2Matches: component %o AMBIGUOUS, discs %o all independently confirmed against the same component\n",
                comp_idx, Sort(Setseq(confirmed_discs));
            // Store inconclusive_add, which ComponentAggregate made
            // confirmed_discs join inconclusive_discs, not confirmed_discs
            // alone: a disc left inconclusive on an ambiguous component is
            // exactly as unresolved as the confirmed ones and must not drop
            // out of ComponentStatusPairs.
            Append(~comp_status, <comp_idx, "ambiguous", inconclusive_add>);
        elif comp_stat eq "inconclusive" then
            Append(~comp_status, <comp_idx, "inconclusive", inconclusive_discs>);
        else
            // Every candidate was tested accurately enough and rejected.
            // Rejected discs stay out of `inconclusive`: a confident negative
            // is not an unresolved one.
            Append(~comp_status, <comp_idx, "unlabelled", rejected_discs>);
        end if;
    end for;
    inconclusive := inconclusive diff matches;
    return matches, inconclusive, records, comp_status;
end function;

// Label rational points on a canonical X_0(N)* and run the coplanarity
// searches. See LabelAndAnalyze_hyperelliptic above for why the hyperelliptic
// case is a separate function.
//
// Returns (exceptional_idxs, planes, all_geometrically_covered, fail_reason,
// idx_to_disc, rc_cache, all_cm_confirmed).
//
// analyze: with `analyze := false` this is the label half only -- match the
// rational points against CM points and the cusp, build idx_to_disc, stop.
// No coplanarity search, and no Degree2Points, which is the expensive step.
// Callers that want only idx_to_disc (CMFiberSetup) should pass it: besides
// the saved work it keeps them off the genus restrictions of the searches,
// which apply to the analysis and not to the labeling.
//
// Each entry of `planes` is a 12-tuple:
//    1 exc_idx        the exceptional point this plane explains
//    2 plane_eqn      \
//    3 comp_degs      / geometry of X cap plane_eqn, independent of CM labeling
//    4 cm_discs       confirmed discriminants on the plane: rational CM and
//                     cusp points from MatchRationalCMPoints (0 = cusp) plus
//                     algebraic degree-2 matches
//    5 deg2_matched   some degree-2 component matched some disc
//    6 cm_inconclusive  discs never confirmed against any field-compatible
//                     component here. Means "raise precision", and is never
//                     promoted into cm_discs
//    7 source_discs   for Search 2 planes, the discs that built this plane.
//                     Rediscovering the same plane_eqn via another d merges
//                     that d in. Empty for Search 1
//    8 confirmed_source_discs  the subset of (7) also in cm_discs
//    9 confirmed_component_matches   \ <component_idx, disc> records behind
//   10 inconclusive_component_matches/ (4) and (6); empty if confirm_deg2 off
//   11 exact_rational_points_on_plane  rats[j] for each j on the plane
//   12 plane_stable   always true: Search 2 planes passed
//                     CertifiedPlaneFromCMPair's dual-run agreement and
//                     Search 1 planes use only exact rational data
//
// Fields 5 and 8 answer different questions, and the distinction matters for
// what you can claim. deg2_matched can be true because some unrelated disc
// matched some other degree-2 component of the plane while every disc that
// actually built it stays unconfirmed. So for a target disc D the claim to
// make is "D in confirmed_source_discs".
//
// The same split appears in the two summary flags:
//   all_geometrically_covered: every exceptional point lies on some plane.
//     Purely geometric, and not evidence of CM certification.
//   all_cm_confirmed: every exceptional point lies on a CM-certified plane,
//     meaning confirmed_source_discs nonempty for a Search 2 plane, or
//     deg2_matched for a Search 1 plane. This is the one for paper claims.
//
// confirm_deg2: default true. False skips AlgebraicDeg2Matches and the ring
//   class field computation it needs (the slow part of Degree2Points). The
//   coplanarity search still runs, but degree-2 components stay unlabelled and
//   all_cm_confirmed is false unless there are no exceptional points.
// rc_cache: passed to Degree2Points and returned updated, so a caller looping
//   over several N can share one cache rather than rebuilding a shared
//   discriminant's fields per level.
function LabelAndAnalyze(N, X, fs, rats, rat_cm_discs : max_class_num := 0, analyze := true, confirm_deg2 := true, rc_cache := AssociativeArray(), prec_lo := 200, prec_hi := 600, resid_C := 10^3, recon_C := 10, error_max_recon := 10^-12, error_max_match := 10^-12)
    g := Genus(X);
    CC := ComplexField(200); tol := 10^-15;
    rats_cc := [[CC!c : c in Eltseq(r)] : r in rats];
    ell_pts, disc_ell_pts := EllipticDiscsByOrder(N);

    // Label; build idx->disc map (0 = cusp sentinel)
    matched, nfail, disc_to_idx, fail_reason := MatchRationalCMPoints(N, fs, rats_cc, rats, CC, tol, rat_cm_discs, ell_pts, disc_ell_pts);
    if nfail ne 0 then
        printf "WARNING: CM matching failed for N=%o: %o\n", N, fail_reason;
        return [], [* *], false, fail_reason, AssociativeArray(), rc_cache, false;
    end if;
    idx_to_disc := AssociativeArray();
    for disc in Keys(disc_to_idx) do
        for j in disc_to_idx[disc] do idx_to_disc[j] := disc; end for;
    end for;
    cusp_cc := [CC!Coefficient(fs[i], 1) : i in [1..g]];
    cusp_list := [j : j in [1..#rats_cc] | IsProjectivelyEquivalent(rats_cc[j], cusp_cc, tol)];
    if #cusp_list gt 0 then
        if cusp_list[1] in matched then
            error Sprintf("N=%o: collision: cusp at rats[%o] but that index already matched to a CM point", N, cusp_list[1]);
        end if;
        printf "  Cusp -> rats[%o]\n", cusp_list[1];
        Include(~matched, cusp_list[1]);
        idx_to_disc[cusp_list[1]] := 0;
    end if;
    exceptional_idxs := [j : j in [1..#rats] | j notin matched];
    printf "Labelled %o CM+cusp, %o exceptional\n", #matched, #exceptional_idxs;
    for j in exceptional_idxs do printf "  exceptional: rats[%o] = %o\n", j, rats[j]; end for;
    if #exceptional_idxs eq 0 then return exceptional_idxs, [* *], true, "", idx_to_disc, rc_cache, true; end if;
    if not analyze then
        // No search ran, so the two coverage booleans have nothing behind them.
        // Return false, not true: false reads as "not established", which is
        // recoverable, where a true would assert coverage never checked for.
        // (The #exceptional_idxs eq 0 case returned true just above, and that
        // one is honest -- there is nothing left to cover.)
        printf "analyze := false: skipping the coplanarity search\n";
        return exceptional_idxs, [* *], false, "", idx_to_disc, rc_cache, false;
    end if;

    known_rat_idxs := Sort([j : j in matched]);
    print "Computing degree 2 CM points";
    deg2pts, rc_cache := Degree2Points(N : max_class_num := max_class_num, compute_fields := confirm_deg2, rc_cache := rc_cache);
    print "Done.";

    // Build the planes list (schema in the header above). Fields 7 and 8 are
    // sets because one plane geometry can legitimately be built from several
    // discriminants; merging keeps both provenances, where discarding either
    // the later or the earlier occurrence would lose one.
    planes := [* *];
    for exc_idx in exceptional_idxs do
        r1_deg1, r1_deg2 := CoplanaritySearch1(X, rats, exc_idx, known_rat_idxs);
        for e in r1_deg1 do
            on_cm := {idx_to_disc[j] : j in e[4] | IsDefined(idx_to_disc, j)};
            Append(~planes, <exc_idx, e[2], e[3], on_cm, false, {Integers()|},
                             {Integers()|}, {Integers()|}, [* *], [* *], [rats[j] : j in e[4]], true>);
        end for;
        for e in r1_deg2 do
            on_cm := {idx_to_disc[j] : j in e[4] | IsDefined(idx_to_disc, j)};
            if confirm_deg2 then
                alg_discs, inconclusive_discs, _, comp_status := AlgebraicDeg2Matches(X, e[2], deg2pts, N, fs, ell_pts, disc_ell_pts : prec_lo := prec_lo, prec_hi := prec_hi, resid_C := resid_C, error_max_match := error_max_match);
            else
                alg_discs := {Integers()|}; inconclusive_discs := {Integers()|}; comp_status := [* *];
            end if;
            // Take the (component_idx, disc) pairs from comp_status, whose
            // discs are already the right set per status, rather than testing
            // records against the plane-wide alg_discs. That test is unsafe:
            // if one disc is confirmed on two components of this plane and one
            // of those is ambiguous, its membership in alg_discs, earned on the
            // other component, would wrongly mark the ambiguous one confirmed.
            Append(~planes, <exc_idx, e[2], e[3], on_cm join alg_discs, #alg_discs gt 0, inconclusive_discs,
                             {Integers()|}, {Integers()|},
                             ComponentStatusPairs(comp_status, {"confirmed"}),
                             ComponentStatusPairs(comp_status, {"inconclusive", "ambiguous"}),
                             [rats[j] : j in e[4]], true>);
        end for;
    end for;

    // Whether this exceptional point already sits on a certified enough plane,
    // which stops the Search 2 loop below. A Search 1 plane (p[7] empty) needs
    // deg2_matched; a Search 2 plane needs one of its own constructing discs
    // confirmed, for the reason given in the header. With confirm_deg2 off
    // there is no algebraic labeling at all, so fall back to the geometric
    // test: any plane with a degree-2 component. That keeps the early exit, and
    // so the set of planes found, the same as a confirm_deg2 run without the
    // disc labels.
    //
    // plns is a parameter because Magma function expressions capture free
    // variables by value at definition time, and planes keeps growing below.
    covered := function(exc, plns)
        if confirm_deg2 then
            return exists{p : p in plns | p[1] eq exc and (
                (#p[7] eq 0 and p[5]) or (#p[7] gt 0 and #p[8] gt 0)
            )};
        else
            return exists{p : p in plns | p[1] eq exc and 2 in p[3]};
        end if;
    end function;

    // Search 2 exists only at g in {3,4} (see its header); g >= 5 is out of
    // scope. Announce that rather than letting it return nothing -- otherwise a
    // g >= 5 level whose exceptional point Search 1 misses reports exactly the
    // all_geometrically_covered = false of a level where the search did run and
    // ruled the plane out. No squarefree level in the 379-level sweep needs it:
    // every level with an exceptional point there is genus <= 4.
    search2_ok := g in {3, 4};
    if not search2_ok and exists{e : e in exceptional_idxs | not covered(e, planes)} then
        printf "WARNING: coplanarity Search 2 is not implemented at genus %o (needs g in {3,4}); " cat
               "exceptional points Search 1 did not cover are unresolved, not excluded\n", g;
    end if;
    for exc_idx in exceptional_idxs do
        if covered(exc_idx, planes) then continue; end if;
        if not search2_ok then continue; end if;
        for d in Keys(deg2pts) do
            r2 := CoplanaritySearch2(X, rats, exc_idx, d, N, fs, ell_pts, disc_ell_pts :
                prec_lo := prec_lo, prec_hi := prec_hi, resid_C := resid_C, recon_C := recon_C,
                error_max_recon := error_max_recon, error_max_match := error_max_match);
            for e in r2 do
                on_cm := {idx_to_disc[j] : j in e[4] | IsDefined(idx_to_disc, j)};
                if confirm_deg2 then
                    alg_discs, inconclusive_discs, _, comp_status := AlgebraicDeg2Matches(X, e[2], deg2pts, N, fs, ell_pts, disc_ell_pts : prec_lo := prec_lo, prec_hi := prec_hi, resid_C := resid_C, error_max_match := error_max_match);
                else
                    alg_discs := {Integers()|}; inconclusive_discs := {Integers()|}; comp_status := [* *];
                end if;
                // CoplanaritySearch2 returns the constructing disc first.
                source_disc := e[1];
                existing_idx := [i : i in [1..#planes] | planes[i][1] eq exc_idx and
                    (planes[i][2] eq e[2] or planes[i][2] eq -e[2])];
                if #existing_idx eq 0 then
                    src := {source_disc};
                    conf := source_disc in alg_discs select {source_disc} else {Integers()|};
                    // Built from comp_status, not by filtering records against
                    // alg_discs; see the Search 1 branch above for why.
                    Append(~planes, <exc_idx, e[2], e[3], on_cm join alg_discs, #alg_discs gt 0, inconclusive_discs,
                                     src, conf,
                                     ComponentStatusPairs(comp_status, {"confirmed"}),
                                     ComponentStatusPairs(comp_status, {"inconclusive", "ambiguous"}),
                                     [rats[j] : j in e[4]], true>);
                else
                    // Same geometry found again via a different discriminant:
                    // merge it into the existing record rather than discard it.
                    pi := existing_idx[1];
                    p := planes[pi];
                    new_src := p[7] join {source_disc};
                    new_conf := p[8];
                    if source_disc in alg_discs then Include(~new_conf, source_disc); end if;
                    planes[pi] := <p[1], p[2], p[3], p[4], p[5], p[6], new_src, new_conf, p[9], p[10], p[11], p[12]>;
                end if;
            end for;
            if covered(exc_idx, planes) then break; end if;
        end for;
    end for;

    exc_covered := {e[1] : e in planes};
    all_geometrically_covered := {j : j in exceptional_idxs} subset exc_covered;

    // Same criterion as `covered` above, applied to the finished plane list.
    cm_certified := function(p)
        if #p[7] eq 0 then return p[5]; else return #p[8] gt 0; end if;
    end function;
    exc_cm_covered := {p[1] : p in planes | cm_certified(p)};
    all_cm_confirmed := {j : j in exceptional_idxs} subset exc_cm_covered;

    // Geometric coplanarity (comps) and CM labeling (CM=, matched=) print as
    // separate statuses, and cm_inconclusive is never folded into CM=.
    // source_discs is Search-2-only and plane_stable is always true, so both
    // print only when they carry information.
    n_matched := #{i : i in [1..#planes] | planes[i][5]};
    printf "Planes found: %o (%o with algebraic CM match)\n", #planes, n_matched;
    for e in planes do
        cm_str := "{ " * Join([d eq 0 select "cusp" else Sprint(d) : d in Sort([s : s in e[4]])], ", ") * " }";
        printf "  exc=rats[%o]: %o=0  comps=%o  CM=%o  matched=%o\n",
            e[1], e[2], e[3], cm_str, e[5];
        if #e[7] gt 0 then
            printf "    source_discs=%o  confirmed_source_discs=%o\n", e[7], e[8];
        end if;
        printf "    exact rational points on plane: %o\n", e[11];
        if #e[9] gt 0 then
            printf "    confirmed component matches (component_idx, disc): %o\n", e[9];
        end if;
        if #e[10] gt 0 then
            printf "    inconclusive component matches (component_idx, disc): %o\n", e[10];
        end if;
        if #e[6] gt 0 then
            printf "    CM-inconclusive (raise precision): %o\n", Sort([s : s in e[6]]);
        end if;
    end for;
    printf "All exceptional points geometrically covered: %o\n", all_geometrically_covered;
    printf "All exceptional points CM-confirmed: %o\n", all_cm_confirmed;

    return exceptional_idxs, planes, all_geometrically_covered, "", idx_to_disc, rc_cache, all_cm_confirmed;
end function;
