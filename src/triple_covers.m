// src/triple_covers.m
//
// Build the triple covers X_0(M)* -> E of elliptic curves, and identify the
// points sitting in their CM fibers.  M is the top level throughout: the level
// of the star curve being covered.  The newform level d = Conductor(E) divides
// M and is derived from the curve, never supplied.
//
// Entry points:  BuildTripleCover(M, Elabel)    returns pi, X, E, fs, Sstar, c
//                AnalyzeCMFiber(pi, X, E, fs, Sstar, M, D)     the fiber over
//                    the disc-D CM points, each point labelled CM disc, cusp,
//                    or exceptional
//                SweepCMFibers(pi, X, E, fs, Sstar, M)     the same, over every
//                    plausible discriminant at once
//
// Load this file directly; it loads src/AtkinLehner.m itself.

load "src/AtkinLehner.m";

// Formal group data of E: w(t) with x = t/w, y = -1/w (t = -x/y), and the
// formal logarithm lambda(t) = t + ... , both to t-precision prec.
function FormalWLog(E, prec)
    printf "[FormalWLog] computing formal group of %o to t-precision %o... ", CremonaReference(E), prec;
    t0 := Cputime();
    a1, a2, a3, a4, a6 := Explode(aInvariants(E));
    Qt<t> := PowerSeriesRing(Rationals(), prec);
    w := t^3;
    repeat
        wnew := t^3 + a1*t*w + a2*t^2*w + a3*w^2 + a4*t*w^2 + a6*w^3;
        done := wnew eq w;
        w := wnew;
    until done;
    x := t/w;                         // Laurent, valuation -2
    y := -1/w;                        // Laurent, valuation -3
    F := Derivative(x)/(2*y + a1*x + a3);   // omega = F(t) dt, F = 1 + ...
    lambda := Integral(F);
    printf "done (%o s)\n", Cputime(t0);
    return w, Qt!lambda;
end function;

// q-expansions of x(pi(z)), y(pi(z)) for the candidate normalization c.
// The pullback differential is c * sum_{e | M/d} e f(q^e) dq/q where
// d = Conductor(E) (d = M when the star form is new; the extra divisors are
// the oldform combinations for q | M/d).  zeta is its formal integral.
// w, lambda can be passed in to avoid recomputation across different c.
function TripleCoverXYSeries(E, M, prec, c : w := 0, lambda := 0)
    if w cmpeq 0 then
        w, lambda := FormalWLog(E, prec);
    end if;
    fE := qExpansion(ModularForm(E), prec + 1);
    L<q> := LaurentSeriesRing(Rationals());
    d := Conductor(E);
    // ExactQuotient, not `div`: d | M is a precondition, and `div` would round
    // a violation down to a plausible-looking level instead of raising.
    // d = M (so the quotient is 1) for an own-level cover.
    zeta := &+[L | &+[L | (Coefficient(fE, n)/n) * q^(e*n) : n in [1..Floor((prec - 1)/e)]]
                 : e in Divisors(ExactQuotient(M, d))]
          + O(q^prec);
    zeta := c * zeta;
    tau := Reversion(lambda);         // formal exponential: t as series in z
    tq := Evaluate(tau, zeta);        // t(q) = c q + ...
    wq := Evaluate(w, tq);
    xq := tq / wq;
    yq := -1 / wq;
    return xq, yq;
end function;

// Linear algebra: find coefficient vectors a, b with
//   sum_j a_j monseries[j] = target * sum_j b_j monseries[j],  sum b_j mon_j != 0,
// as an identity of q-series through the available precision.
// Requires at least min_extra more equations than unknowns.
function SolveRatFun(target, monseries : min_extra := 25)
    L := Universe(monseries);
    tgt := L ! target;
    evt := [-tgt * e : e in monseries];
    all := monseries cat evt;
    minv := Min([Valuation(e) : e in all]);
    maxv := Min([AbsolutePrecision(e) : e in all]) - 1;
    if maxv - minv + 1 lt #all + min_extra then
        printf "    [SolveRatFun] not enough precision (%o coefficients for %o unknowns)\n",
            maxv - minv + 1, #all;
        return false, _, _;
    end if;
    mat := Matrix(Rationals(), [[Coefficient(e, j) : j in [minv..maxv]] : e in all]);
    ker := KernelMatrix(mat);
    printf "    [SolveRatFun] %o x %o matrix, kernel dimension %o\n", Nrows(mat), Ncols(mat), Nrows(ker);
    n := #monseries;
    for i in [1..Nrows(ker)] do
        b := [ker[i, n + j] : j in [1..n]];
        Bs := &+[b[j] * monseries[j] : j in [1..n]];
        if Bs ne 0 then
            a := [ker[i, j] : j in [1..n]];
            return true, a, b;
        end if;
    end for;
    return false, _, _;
end function;

// ---------------------------------------------------------------------------
// Triple-cover map cache.  The degree-3 map pi is found by q-expansion linear
// algebra (TripleCoverMap_*), by far the most expensive step.  Cache its
// defining polynomials (as ring-independent coeff/exponent data), the target
// curve's a-invariants and the normalization c.  On a later run we rebuild the
// model from cached forms and reconstruct pi directly, skipping the search.
// ---------------------------------------------------------------------------
// Key: the top level M and the Cremona label of the target curve.  A degree-3
// map X_0(M)* -> E is unique up to sign and translation, so this pair
// determines the map.  There is no fallback read path.
function MapCachePath(M, lab)
    return STAR_CACHE_DIR cat "/map_" cat Sprint(M) cat "_" cat lab cat ".m";
end function;

function StrJoin(strs, sep)
    if #strs eq 0 then return ""; end if;
    r := strs[1];
    for i in [2..#strs] do r cat:= sep cat strs[i]; end for;
    return r;
end function;

// serialize a multivariate polynomial as ring-independent <coeff, exponents> data
function PolyCoeffData(f)
    mons := Monomials(f); cfs := Coefficients(f);
    parts := [Sprintf("<%o, %o>", cfs[i], Exponents(mons[i])) : i in [1..#mons]];
    return "[* " cat StrJoin(parts, ", ") cat " *]";
end function;

function PolyFromCoeffData(R, data)
    g := Rank(R);
    f := R ! 0;
    for t in data do
        f +:= (R ! t[1]) * &*[R.i ^ t[2][i] : i in [1..g]];
    end for;
    return f;
end function;

// Read the cache file at `path`, returning ok, contents. Shared by every
// eval-a-cached-object cache reader in this file (LoadTripleCoverMap,
// LoadExtendedMap) so a fix to the read path only has to be made once.
function ReadCacheFile(path)
    try
        return true, Read(path);
    catch e
        return false, _;
    end try;
end function;

// Atomically write `body` to `path` via a tmp-file + mv, then printf `msg`.
// Shared by every Save*Map procedure in this file so a fix to the write path
// (e.g. checking mv's exit status) only has to be made once.
procedure WriteCacheFileAtomic(path, body, msg)
    tmp := path cat ".tmp" cat Sprint(Random(10^9));
    Write(tmp, body : Overwrite := true);
    System(Sprintf("mv %o %o", tmp, path));
    printf "%o", msg;
end procedure;

// returns ok, pi, E, c  (E reconstructed from cached a-invariants)
function LoadTripleCoverMap(M, lab, X)
    ok, s := ReadCacheFile(MapCachePath(M, lab));
    if not ok then return false, _, _, _; end if;
    dat := eval s;                       // <ainvs, c, [* polydata_1, ... *]>
    E := EllipticCurve([Rationals() | a : a in dat[1]]);
    // Integrity check: the stored curve must be the one the filename claims.
    // Cheap, and it catches a hand-edited or mis-keyed cache file rather than
    // letting it through as the wrong cover.
    if CremonaReference(MinimalModel(E)) ne lab then return false, _, _, _; end if;
    R := CoordinateRing(AmbientSpace(X));
    polys := [PolyFromCoeffData(R, pd) : pd in dat[3]];
    pi := map<X -> E | polys>;
    return true, pi, E, dat[2];
end function;

procedure SaveTripleCoverMap(M, lab, E, c, pi)
    polys := DefiningPolynomials(pi);
    body := Sprintf("<%o, %o, [* %o *]>", aInvariants(E), c,
        StrJoin([PolyCoeffData(f) : f in polys], ", "));
    WriteCacheFileAtomic(MapCachePath(M, lab), body,
        Sprintf("[cache] saved triple-cover map for (M=%o, %o)\n", M, lab));
end procedure;

// ---------------------------------------------------------------------------
// Extend(pi) cache.  Extend resolves pi's base locus so it can be evaluated
// at every point, for a canonical model in P^(g-1) with g >= 5 this is by
// far the most expensive step in CMFiberSetup (elimination/saturation whose
// cost blows up with genus and embedding dimension). Since a rational map
// between smooth curves is automatically a morphism, Extend's result is representable
// the same way pi is: one polynomial sequence with no common zeros, so the
// same PolyCoeffData round-trip used for the base map cache above applies
// unchanged. Keyed on (M, aInvariants(E)) rather than on M alone; two
// different constructions at the same top level (e.g. the AL-quotient cover
// X_0(M)* -> X_0(d)* and the own-level cover X_0(M)* -> E of conductor M) can
// share M while targeting different curves, so the target's invariants have to
// be part of the key.
// ---------------------------------------------------------------------------
function ExtMapCachePath(M, E)
    tag := StrJoin([Sprint(a) : a in aInvariants(E)], "_");
    return STAR_CACHE_DIR cat "/mapext_" cat Sprint(M) cat "_" cat tag cat ".m";
end function;

function LoadExtendedMap(M, X, E)
    ok, s := ReadCacheFile(ExtMapCachePath(M, E));
    if not ok then return false, _; end if;
    dat := eval s;                       // [* polydata_1, ... *]
    R := CoordinateRing(AmbientSpace(X));
    polys := [PolyFromCoeffData(R, pd) : pd in dat];
    piE := map<X -> E | polys>;
    return true, piE;
end function;

procedure SaveExtendedMap(M, E, piE)
    polys := DefiningPolynomials(piE);
    body := "[* " cat StrJoin([PolyCoeffData(f) : f in polys], ", ") cat " *]";
    WriteCacheFileAtomic(ExtMapCachePath(M, E), body,
        Sprintf("[cache] saved extended map for X_0(%o)*\n", M));
end procedure;

// Evaluate piE at P, escalating to a full Extend(pi) (persisted via the same
// LoadExtendedMap/SaveExtendedMap cache CMFiberSetup uses) if the current piE
// fails, CMFiberSetup only extends pi when a point in `rats` demanded it, so
// callers walking fibers over points outside `rats` (ramification points,
// already-unlabelled/exceptional points) can still hit an unextended piE.
// Returns ok, Q, piE; piE is returned so callers reuse the (possibly newly
// extended) map on every later call in the same loop instead of re-extending
// each time.
function EvalPiE(pi, piE, X, E, M, P)
    try
        return true, piE(P), piE;
    catch e
        okE, piE2 := LoadExtendedMap(M, X, E);
        if not okE then
            try
                piE2 := Extend(pi);
                SaveExtendedMap(M, E, piE2);
                okE := true;
            catch e2
                okE := false;
            end try;
        end if;
        if not okE then return false, _, piE; end if;
        try
            return true, piE2(P), piE2;
        catch e3
            return false, _, piE;
        end try;
    end try;
end function;

// CertifyEquationsAgainstCache, CanonicalModelFromForms,
// HyperellipticModelFromForms, and StarModelWithForms live in
// src/star_model_cache.m, so point_search.m (loaded earlier in
// src/AtkinLehner.m than this file) can also use them for
// point_search_X0Nstar's UseCache option, without a circular
// src/point_search.m <-> src/triple_covers.m dependency. This file still
// gets them via the `load "src/AtkinLehner.m"` above.

// Attempt to build a candidate triple-cover map and check its degree.
// build_pi: 0-argument function returning map<X -> E | [...]>, construction
// can itself throw (e.g. the three coordinate functions have a common zero),
// which is why this takes a thunk rather than an already-built map.
// Shared by TripleCoverMap_canonical and TripleCoverMap_hyperelliptic: the
// two differ in how A/B (resp. C/D) are built from the solved coefficients
//, explicit numerator/denominator polynomials over the coordinate ring vs.
// function-field fractions, not in this build-and-check step.
function TryMapDegree(build_pi, expdeg)
    try
        pi := build_pi();
        deg := Degree(pi);
    catch e
        printf "  map construction failed: %o\n", e`Object;
        return false, _, _;
    end try;
    printf "  degree of map = %o (expected %o)\n", deg, expdeg;
    return deg eq expdeg, pi, deg;
end function;

// ---------------------------------------------------------------------------
// Non-hyperelliptic case: X canonically embedded in P^{g-1}, coordinates = fs.
// Express x*pi, y*pi as ratios of degree-d monomials in the coordinates.
// ---------------------------------------------------------------------------
function TripleCoverMap_canonical(X, fs, E, M, prec : cs := [1,-1,2,-2,1/2,-1/2,3,-3,1/3,-1/3,4,-4,1/4,-1/4], maxdeg := 5, expected_deg := 3)
    g := #fs;
    L<q> := LaurentSeriesRing(Rationals());
    fsL := [L ! f : f in fs];
    R := CoordinateRing(AmbientSpace(X));
    w, lambda := FormalWLog(E, prec);
    expdeg := expected_deg;
    // Monomial evaluations per degree, cached on demand.
    monscache := AssociativeArray();

    for c in cs do
        printf "[canonical] trying normalization c = %o\n", c;
        xq, yq := TripleCoverXYSeries(E, M, prec, c : w := w, lambda := lambda);
        for dx in [1..maxdeg] do
            printf "  solving for x∘pi in degree-%o monomials\n", dx;
            if not IsDefined(monscache, dx) then
                mons := Setseq(MonomialsOfDegree(R, dx));
                monscache[dx] := <mons, [&*[fsL[j]^Degree(m, R.j) : j in [1..g]] : m in mons]>;
            end if;
            md := monscache[dx];
            okx, ax, bx := SolveRatFun(xq, md[2]);
            if not okx then continue; end if;
            monsx := md[1];
            A := &+[ax[j] * monsx[j] : j in [1..#monsx]];
            B := &+[bx[j] * monsx[j] : j in [1..#monsx]];
            // now y
            for dy in [dx..maxdeg] do
                printf "  solving for y∘pi in degree-%o monomials\n", dy;
                if not IsDefined(monscache, dy) then
                    mons := Setseq(MonomialsOfDegree(R, dy));
                    monscache[dy] := <mons, [&*[fsL[j]^Degree(m, R.j) : j in [1..g]] : m in mons]>;
                end if;
                mdy := monscache[dy];
                oky, ay, bv := SolveRatFun(yq, mdy[2]);
                if not oky then continue; end if;
                monsy := mdy[1];
                C := &+[ay[j] * monsy[j] : j in [1..#monsy]];
                D := &+[bv[j] * monsy[j] : j in [1..#monsy]];
                printf "TripleCoverMap: candidate found with c = %o, deg(x) = %o, deg(y) = %o\n", c, dx, dy;
                // pi = [x : y : 1] = [A*D : C*B : B*D]
                found, pi := TryMapDegree(function() return map<X -> E | [A*D, C*B, B*D]>; end function, expdeg);
                if found then
                    return true, pi, c;
                end if;
            end for;
        end for;
    end for;
    return false, _, _;
end function;

// ---------------------------------------------------------------------------
// Hyperelliptic case: X : y^2 = P(x) from XZeroNstarWithForms_hyperelliptic,
// x = f_{g-1}/f_g, y = (D(f_{g-1}) f_g - f_{g-1} D(f_g))/f_g^3, D = q d/dq.
// Function "monomials" of level d: x^i (i <= d) and x^j*y (j <= d - 3).
// ---------------------------------------------------------------------------
function TripleCoverMap_hyperelliptic(X, fs, E, M, prec : cs := [1,-1,2,-2,1/2,-1/2,3,-3,1/3,-1/3,4,-4,1/4,-1/4], maxdeg := 8, expected_deg := 3)
    g := #fs;
    L<q> := LaurentSeriesRing(Rationals());
    fg1 := L ! fs[g - 1];
    fg := L ! fs[g];
    xC := fg1 / fg;
    yC := (q*Derivative(fg1)*fg - fg1*q*Derivative(fg)) / fg^3;
    FX := FunctionField(X);
    xF := FX.1;
    yF := FX.2;
    w, lambda := FormalWLog(E, prec);
    expdeg := expected_deg;

    // monomial list at level d: pairs <function field elt, q-series>
    function monsOfDeg(d)
        fns := [<xF^i, xC^i> : i in [0..d]];
        if d ge 3 then
            fns cat:= [<xF^j * yF, xC^j * yC> : j in [0..d - 3]];
        end if;
        return fns;
    end function;

    for c in cs do
        printf "[hyperelliptic] trying normalization c = %o\n", c;
        xq, yq := TripleCoverXYSeries(E, M, prec, c : w := w, lambda := lambda);
        for dx in [2..maxdeg] do
            printf "  solving for x∘pi at level %o\n", dx;
            md := monsOfDeg(dx);
            okx, ax, bx := SolveRatFun(xq, [m[2] : m in md]);
            if not okx then continue; end if;
            xpi := &+[ax[j] * md[j][1] : j in [1..#md]] / &+[bx[j] * md[j][1] : j in [1..#md]];
            for dy in [dx..maxdeg] do
                printf "  solving for y∘pi at level %o\n", dy;
                mdy := monsOfDeg(dy);
                oky, ay, bv := SolveRatFun(yq, [m[2] : m in mdy]);
                if not oky then continue; end if;
                ypi := &+[ay[j] * mdy[j][1] : j in [1..#mdy]] / &+[bv[j] * mdy[j][1] : j in [1..#mdy]];
                printf "TripleCoverMap: candidate found with c = %o, level(x) = %o, level(y) = %o\n", c, dx, dy;
                found, pi := TryMapDegree(function() return map<X -> E | [xpi, ypi, 1]>; end function, expdeg);
                if found then
                    return true, pi, c;
                end if;
            end for;
        end for;
    end for;
    return false, _, _;
end function;

// ---------------------------------------------------------------------------
// Main constructor.
// ---------------------------------------------------------------------------

// The Cremona-optimal curve of the isogeny class containing E.  ModularDegree
// and StarDegree are only meaningful there, while the label handed to
// BuildTripleCover names E^C_f, which need not be optimal (185c2).
function OptimalCurveOfClass(E)
    d := Conductor(E);
    DB := CremonaDatabase();
    for i in [1..NumberOfIsogenyClasses(DB, d)] do
        Ei := EllipticCurve(DB, d, i, 1);
        if IsIsogenous(Ei, E) then return Ei; end if;
    end for;
    error Sprintf("OptimalCurveOfClass: no class of conductor %o contains %o",
        d, CremonaReference(E));
end function;

// The triple-cover builder.  M is the top level, the level of the star curve
// X_0(M)* being covered; Elabel names the target E^C_f = E_f/C.  Checks the
// degree formula before doing any work, so a case that cannot give degree 3
// fails immediately rather than after the model build:
//     deg(pi_f) = delta_f * prod_{l | M/d} (l + 1 + a_l(f)) = 3.
//
// The target is named explicitly rather than derived from M, because deriving
// it is not always possible: conductor 201 carries two all-plus classes, so no
// rule picks the right one for X_0(402)*, and X_0(185)*'s target is 185c2, not
// the Cremona-optimal 185c1 of its class.
//
// use_cache := false skips the map-cache READ, so a caller that wants to time
// or re-derive a genuine build gets one.  It is deliberately not a delete:
// forcing a miss by removing files would destroy maps that cost hours to
// produce and that are independent evidence a cover exists.
function BuildTripleCover(M, Elabel : eval_prec := 400, cache_prec := 3000, use_cache := true)
    E := MinimalModel(EllipticCurve(Elabel));
    Eopt := OptimalCurveOfClass(E);
    d := Conductor(Eopt);
    error if not IsDivisibleBy(M, d),
        Sprintf("BuildTripleCover: conductor %o does not divide M = %o", d, M);
    tgt := CremonaReference(StarTargetCurve(Eopt));
    error if tgt ne CremonaReference(E),
        Sprintf("BuildTripleCover: %o is not E^C_f for the class of conductor %o; that is %o",
            Elabel, d, tgt);
    delta := StarDegree(Eopt);
    cofactor := ExactQuotient(M, d);
    factors := [<l, l + 1 + TraceOfFrobenius(Eopt, l)> : l in PrimeDivisors(cofactor)];
    expdeg := delta * &*[Integers() | t[2] : t in factors];
    printf "M = %o, d = %o: E^C_f = %o (E_f = %o), delta_f = %o, factors %o, expected degree %o\n",
        M, d, Elabel, CremonaReference(Eopt), delta, factors, expdeg;
    error if expdeg ne 3,
        Sprintf("BuildTripleCover: expected a degree-3 map, the formula gives %o", expdeg);

    lab := CremonaReference(E);
    t0 := Cputime();
    printf "[BuildTripleCover] building model of X_0(%o)* (eval_prec = %o, cached if available)... ", M, eval_prec;
    // GrowCache: this is the caller that owns the map_<M>_*.m files a rewritten
    // starforms_<M>.m would invalidate, so raising cache_prec here is meant to
    // regenerate the on-disk entry (scripts/make_exceptional_table.m relies on
    // that to get enough CM-labelling terms up front).
    X, fs, Sstar := StarModelWithForms(M, eval_prec : cache_prec := cache_prec, GrowCache := true);
    printf "done (%o s)\n", Cputime(t0);

    if use_cache then
        okc, pic, Ec, cc := LoadTripleCoverMap(M, lab, X);
        if okc then
            printf "[cache] loaded triple-cover map for (M=%o, %o)\n", M, lab;
            return pic, X, Ec, fs, Sstar, cc;
        end if;
    end if;

    if IsHyperellipticX0Nstar(M) then
        ok, pi, c := TripleCoverMap_hyperelliptic(X, fs, E, M, eval_prec);
    else
        ok, pi, c := TripleCoverMap_canonical(X, fs, E, M, eval_prec);
    end if;
    error if not ok,
        "BuildTripleCover: no map found, try higher eval_prec or more c candidates";
    SaveTripleCoverMap(M, lab, E, c, pi);
    printf "success: pi : X_0(%o)* -> %o (degree 3) with pi^*omega = %o * h dq/q, h = sum_(e | %o) e f(q^e)\n",
        M, Elabel, c, cofactor;
    return pi, X, E, fs, Sstar, c;
end function;

// ===========================================================================
// CM fiber analysis
//
// The disc-D CM points of X_0(M)* (there are two: either both rational or a
// Galois-conjugate quadratic pair) lie in a single fiber of the degree-3 map
// pi, over a rational point Q of E.  The remaining point of pi^{-1}(Q) is
// then forced to be a rational point of X_0(M)*: the point we identify.
//
// Point labeling (CM disc / cusp / exceptional) 
// LabelAndAnalyze and LabelAndAnalyze_hyperelliptic now also return their
// index -> disc map (cusp = 0).
// ===========================================================================

// Recognize a numeric image [v1, v2, v3] (projective, complex) as a rational
// point of E.
function RationalizeImage(E, vals : tol := 10^-8, hb := 10^15)
    scale := Max([Abs(v) : v in vals]);
    if Abs(vals[3]) lt tol * scale then
        return true, E ! 0;                      // the point at infinity
    end if;
    x := vals[1] / vals[3];
    y := vals[2] / vals[3];
    if Abs(Imaginary(x)) gt tol * (1 + Abs(x)) or
       Abs(Imaginary(y)) gt tol * (1 + Abs(y)) then
        return false, _;
    end if;
    // increasing denominator bounds: a huge bound makes BestApproximation chase
    // numeric noise instead of rounding to the true small-height rational
    hbk := 100;
    repeat
        hbk := hbk^2;
        xr := BestApproximation(Real(x), hbk);
        yr := BestApproximation(Real(y), hbk);
        if Abs(Real(x) - xr) le tol * (1 + Abs(x)) and
           Abs(Real(y) - yr) le tol * (1 + Abs(y)) then
            ok, PE := IsPoint(E, [xr, yr]);
            if ok then return true, PE; end if;
        end if;
    until hbk gt hb;
    return false, _;
end function;

// Label string for the point rats[j] from the idx -> disc map (0 = cusp).
function PointLabel(idx_to_disc, j)
    if IsDefined(idx_to_disc, j) then
        d := idx_to_disc[j];
        return d eq 0 select "cusp" else Sprintf("CM disc %o", d);
    end if;
    return "NOT CM (exceptional)";
end function;

// Does the place plc match one of the numeric coordinate vectors in evals
// under some complex embedding of its residue field?
function PlaceMatchesEvals(plc, evals, CC : tol := 10^-6)
    if #evals eq 0 then return false; end if;
    coordsK := Eltseq(RepresentativePoint(plc));
    K := Universe(coordsK);
    if Type(K) in {FldRat, RngInt} then
        vec := [CC ! c : c in coordsK];
        return exists{ev : ev in evals | IsProjectivelyEquivalent(vec, ev, tol)};
    end if;
    PC := PolynomialRing(CC);
    for r in Roots(PC ! DefiningPolynomial(K)) do
        h := hom<K -> CC | r[1]>;
        vec := [h(c) : c in coordsK];
        if exists{ev : ev in evals | IsProjectivelyEquivalent(vec, ev, tol)} then
            return true;
        end if;
    end for;
    return false;
end function;

// ---------------------------------------------------------------------------
// Setup shared by every fiber-analysis entry point below (AnalyzeCMFiber,
// SweepCMFibers, RunCuspFiber, FiberPointSearch, ExceptionalFiberRows,
// RamifiedFibers): point search, labeling boosted expansions and
// elliptic-point data.  M is the top level, as everywhere in this file.
// confirm_deg2: forwarded to LabelAndAnalyze (non-hyperelliptic models only;
//   LabelAndAnalyze_hyperelliptic has no such check, it explains exceptional
//   points via HyperellipticInvolutionSearch instead). Defaults to false since
//   callers here only need rational-point labels, not exceptional-point CM
//   certification; the printed plane search still runs either way (idx_to_disc
//   only covers matched rational points), but with confirm_deg2 = false its
//   "matched"/CM= fields never get a chance to confirm a degree-2 residual
//   divisor against a candidate discriminant, set true to get the same
//   CM-certified planes analyze_exceptional / LabelAndAnalyze would report.
// ---------------------------------------------------------------------------
function CMFiberSetup(pi, X, fs, Sstar, M : B := 100000, label := true,
    cm_terms := 3000, print_points := true, confirm_deg2 := false)

    hyp := Type(X) eq CrvHyp;
    if hyp then
        rats := PointsOriginalModel(X, B);
    else
        rats := PointSearch(X, B : Nonsingular := true);
    end if;
    printf "found %o small rational points on X_0(%o)* (bound %o)\n", #rats, M, B;

    cached := #Sstar gt 0 and Type(Sstar[1]) eq RngSerPowElt;
    if cached then
        // Sstar is the cached full-precision expansion list from StarModelWithForms
        fs_cm := Sstar;
        if AbsolutePrecision(fs_cm[1]) lt cm_terms then
            printf "WARNING: cached forms have %o terms < cm_terms = %o\n",
                AbsolutePrecision(fs_cm[1]), cm_terms;
        end if;
    else
        fs_cm := hyp select BoostFsPrec_hyperelliptic(Sstar, cm_terms)
                     else BoostFsPrec(Sstar, cm_terms);
        if #fs_cm eq 0 then
            printf "WARNING: BoostFsPrec failed, using the map-precision expansions\n";
            fs_cm := fs;
        end if;
    end if;

    idx_to_disc := AssociativeArray();
    labels_ok := false;
    if label then
        rat_cm_discs := Keys(RationalCMDiscs(M));
        printf "\nlabeling the rational points:\n";
        if hyp then
            _, _, _, fail_r, idx_to_disc :=
                LabelAndAnalyze_hyperelliptic(M, X, fs_cm, rats, rat_cm_discs);
        else
            // analyze := false: only idx_to_disc is used below, so the
            // coplanarity search is discarded work here, and its Degree2Points
            // call is the expensive step. It also carries genus restrictions
            // the labeling itself does not (Search 2 is g in {3,4} only),
            // which this table's genus-7 and genus-8 levels sit outside.
            _, _, _, fail_r, idx_to_disc :=
                LabelAndAnalyze(M, X, fs_cm, rats, rat_cm_discs : analyze := false, confirm_deg2 := confirm_deg2);
        end if;
        labels_ok := fail_r eq "";
        if not labels_ok then
            printf "labeling failed (%o); retrying with %o-term expansions\n", fail_r, 2*cm_terms;
            fs_cm2 := cached select []
                      else (hyp select BoostFsPrec_hyperelliptic(Sstar, 2*cm_terms)
                                else BoostFsPrec(Sstar, 2*cm_terms));
            if #fs_cm2 gt 0 then
                fs_cm := fs_cm2;
                if hyp then
                    _, _, _, fail_r, idx_to_disc :=
                        LabelAndAnalyze_hyperelliptic(M, X, fs_cm, rats, rat_cm_discs : cc_prec := 500);
                else
                    _, _, _, fail_r, idx_to_disc :=
                        LabelAndAnalyze(M, X, fs_cm, rats, rat_cm_discs : analyze := false, confirm_deg2 := confirm_deg2);
                end if;
                labels_ok := fail_r eq "";
            end if;
            if not labels_ok then
                printf "labeling still failing (%o); points will be reported unlabelled\n", fail_r;
            end if;
        end if;
    end if;

    // Extend(pi) resolves pi's base locus so it evaluates everywhere, but a
    // rational map between smooth curves is a morphism away from any base
    // points regardless, and pi's given polynomials already suffice unless
    // one of `rats` happens to sit exactly in the (typically empty or tiny)
    // base locus of that particular representation. Extend is expensive
    // (elimination/saturation, cost grows fast with genus), so only pay for
    // it when a direct evaluation actually fails.
    E := Codomain(pi);
    piE := pi;
    need_extend := false;
    for j in [1..#rats] do
        try
            _ := pi(X ! Eltseq(rats[j]));
        catch e
            need_extend := true;
        end try;
    end for;
    if need_extend then
        okE, piE2 := LoadExtendedMap(M, X, E);
        if okE then
            printf "[cache] loaded extended map for X_0(%o)*\n", M;
            piE := piE2;
        else
            try
                t0 := Cputime();
                piE := Extend(pi);
                printf "Extend(pi) done (%o s)\n", Cputime(t0);
                SaveExtendedMap(M, E, piE);
            catch e
                printf "(Extend(pi) failed, using pi as given)\n";
            end try;
        end if;
    end if;
    if print_points then
        printf "\nsmall rational points, their labels and images under pi:\n";
        for j in [1..#rats] do
            lbl := labels_ok select PointLabel(idx_to_disc, j) else "unlabelled";
            img := "(evaluation failed)";
            try
                img := Sprint(piE(X ! Eltseq(rats[j])));
            catch e
                img := "(evaluation failed)";
            end try;
            printf "  P%o = %o  [%o]  |-->  %o\n", j, rats[j], lbl, img;
        end for;
    end if;

    ell_pts, disc_ell_pts := EllipticDiscsByOrder(M);

    return rats, fs_cm, idx_to_disc, labels_ok, piE, ell_pts, disc_ell_pts;
end function;

// ---------------------------------------------------------------------------
// Per-discriminant core: evaluate the disc-D CM points of X_0(M)*, push them
// through pi, and (for each rational image Q) pull back the fiber and identify
// its points.  Returns <results, status>:
//   results = list of <D, Q, third_point, label> (non-CM points of CM fibers)
//   status  = short human-readable outcome string
// verbose := false gives one-line reporting suitable for sweeps.
// ---------------------------------------------------------------------------
function CMFiberForDisc(pi, X, E, fs_cm, rats, idx_to_disc, labels_ok,
    M, D, ell_pts, disc_ell_pts : cc_prec := 200, verbose := true)

    hyp := Type(X) eq CrvHyp;
    CC := ComplexField(cc_prec);
    ell_order := 1;
    for ell in [2,3,4,6] do
        if D in Keys(ell_pts[ell]) then ell_order := ell; break; end if;
    end for;
    eqs := DefiningPolynomials(pi);

    // CMTauReps returns [] when there is no optimal embedding of the order,
    // rather than throwing.  One tau per <Gamma_0(M), AL>-orbit: distinct
    // entries are distinct points of X_0(M)*.
    htaus := CMTauReps(D, M, CC);
    if #htaus eq 0 then
        if verbose then
            printf "  --> there are NO disc-%o CM points on X_0(%o)* (no optimal embedding of the order); skipping\n", D, M;
        end if;
        return [* *], "no CM points (no optimal embedding of the order)";
    end if;

    targets := [];      // distinct rational images of the disc-D CM points
    cm_evals := [* *];  // numeric coordinates of the disc-D CM points
    nbad := 0;
    for tau in htaus do
        coords := [];
        if hyp then
            ev := EvaluateAtCM_hyperelliptic(fs_cm, tau, CC : ell_order := ell_order,
                      P_poly := HyperellipticPolynomials(X));
            if #ev eq 2 then coords := [ev[1], ev[2], CC ! 1]; end if;
            if #ev eq 3 then coords := ev; end if;
        else
            ev := EvaluateAtCM(fs_cm, tau, CC, D, ell_pts, disc_ell_pts, M);
            if #ev gt 0 then coords := ev; end if;
        end if;
        if #coords eq 0 then
            if verbose then printf "  (evaluation failed for tau = %o)\n", ComplexField(6) ! tau; end if;
            nbad +:= 1;
            continue;
        end if;
        Append(~cm_evals, coords);
        vals := [Evaluate(f, coords) : f in eqs];
        ok, Q := RationalizeImage(E, vals);
        if ok then
            if verbose then
                printf "  CM point at tau = %o  |-->  Q = %o\n", ComplexField(6) ! tau, Q;
            end if;
            if Position(targets, Q) eq 0 then Append(~targets, Q); end if;
        else
            nbad +:= 1;
            if verbose then
                printf "  CM point at tau = %o: image NOT recognized as rational: %o\n",
                    ComplexField(6) ! tau, [ComplexField(10) | v/vals[3] : v in vals];
            end if;
        end if;
    end for;
    if #targets eq 0 then
        return [* *], nbad gt 0 select "images not rational (no rational fiber)"
                                else "evaluation failed";
    end if;
    if verbose then
        if #targets eq 1 and nbad eq 0 then
            printf "all disc-%o CM points map to the SAME rational point, as expected\n", D;
        elif #targets gt 1 then
            printf "NOTE: the disc-%o CM points map to %o distinct rational points\n", D, #targets;
        end if;
    end if;

    results := [* *];
    for k in [1..#targets] do
        Q := targets[k];
        if verbose then
            printf "\n--- fiber of pi over Q%o = %o (image of the disc-%o CM points) ---\n", k, Q, D;
        end if;
        fiber_ok := true;
        try
            PB := Pullback(pi, Divisor(Q));
        catch e
            printf "  divisor pullback failed: %o\n", e`Object;
            fiber_ok := false;
        end try;
        if not fiber_ok then continue; end if;
        plcs, mults := Support(PB);
        for i in [1..#plcs] do
            plc := plcs[i];
            d := Degree(plc);
            RP := RepresentativePoint(plc);
            is_cm := PlaceMatchesEvals(plc, cm_evals, CC);
            if d eq 1 then
                idx := Index([Sprint(r) : r in rats], Sprint(RP));
                if idx gt 0 then
                    lbl := labels_ok select PointLabel(idx_to_disc, idx)
                                     else Sprintf("= P%o, unlabelled", idx);
                else
                    lbl := "not in the small-point list";
                end if;
                if verbose then
                    printf "  deg-1 place (mult %o): rational point %o  [%o]%o\n",
                        mults[i], RP, lbl, is_cm select "  <-- disc-" cat Sprint(D) cat " CM point" else "";
                end if;
                if not is_cm then
                    for m in [1..mults[i]] do Append(~results, <D, Q, RP, lbl>); end for;
                end if;
            else
                if verbose then
                    K := ResidueClassField(plc);
                    printf "  deg-%o place (mult %o) over %o:\n      %o   %o\n",
                        d, mults[i], K, RP,
                        is_cm select "<-- the two disc-" cat Sprint(D) cat " CM points"
                              else "(quadratic pair, NOT the disc-" cat Sprint(D) cat " CM points)";
                end if;
            end if;
        end for;
    end for;
    if verbose then
        for t in results do
            printf ">>> THIRD POINT in the fiber over Q = %o:\n>>>     %o   [%o]\n", t[2], t[3], t[4];
        end for;
    end if;
    return results, Sprintf("%o rational fiber(s)", #targets);
end function;

// ---------------------------------------------------------------------------
// Cusp fiber.  The (single, rational) cusp of X_0(M)* is a rational point and
// hence a source of forced-rational fiber points exactly as the CM points are:
// in a fiber it anchors the rational divisor class, so the residual splits into
// rational points that need no search.  The map pi is Abel-Jacobi based at the
// cusp, so pi(cusp) = O = E!0.  Pull back the fiber over O, skip the cusp place
// itself, and label the residual points; same treatment CMFiberForDisc gives
// a CM disc, with D = 0 as the cusp sentinel.
// Returns <results, status, pb_cache>; the third value is the pullback cache
// with this call's entries added, which the caller must rebind to keep (Magma
// passes it in by value, and only procedures take ~ reference arguments).
// ---------------------------------------------------------------------------
function CuspFiber(pi, piE, X, E, rats, idx_to_disc, labels_ok, M : verbose := true, pb_cache := AssociativeArray())
    results := [* *];
    Qcusp := E ! 0;

    // Locate the cusp among the small rational points and
    // recognize the cusp place in the pulled-back fiber.
    cusp_idx := 0;
    if labels_ok then
        for j in Keys(idx_to_disc) do
            if idx_to_disc[j] eq 0 then cusp_idx := j; break; end if;
        end for;
    end if;

    // Recognize the cusp place geometrically too, so it is filtered even when
    // CM labeling failed/was skipped: on a canonical model (echelon forms
    // f_i = q^i + ...) the cusp q->0 is the point (1:0:...:0).
    cusp_reps := {};
    if cusp_idx gt 0 then Include(~cusp_reps, Sprint(rats[cusp_idx])); end if;
    if Type(X) ne CrvHyp then
        try
            ncoord := Dimension(AmbientSpace(X)) + 1;
            cusp_can := X ! [Rationals() | i eq 1 select 1 else 0 : i in [1..ncoord]];
            Include(~cusp_reps, Sprint(cusp_can));
        catch e
            ;
        end try;
    end if;

    if cusp_idx gt 0 then
        try
            Qc := piE(X ! Eltseq(rats[cusp_idx]));
            if Qc ne Qcusp then
                if verbose then
                    printf "  NOTE: cusp P%o maps to %o, not O; using that image\n", cusp_idx, Qc;
                end if;
                Qcusp := Qc;
            end if;
        catch e
            if verbose then printf "  (could not evaluate pi at the cusp; using O)\n"; end if;
        end try;
    elif verbose then
        printf "  (cusp not identified among the small points; analyzing the fiber over O anyway,\n   any cusp place will be reported as a residual point and must be read as the cusp)\n";
    end if;

    fiber_ok := true;
    qkey := Sprint(Qcusp);
    if IsDefined(pb_cache, qkey) then
        fiber_ok, PB := Explode(pb_cache[qkey]);
    else
        try
            PB := Pullback(pi, Divisor(Qcusp));
            pb_cache[qkey] := <true, PB>;
        catch e
            printf "  cusp-fiber pullback failed: %o\n", e`Object;
            fiber_ok := false;
            pb_cache[qkey] := <false, 0>;
        end try;
    end if;
    if not fiber_ok then return results, "cusp-fiber pullback failed", pb_cache; end if;

    plcs, mults := Support(PB);
    degs := Sort([Degree(plcs[i]) : i in [1..#plcs]]);
    if verbose then
        printf "\n--- CUSP FIBER: fiber of pi over Q = %o (contains the cusp), splits as degrees %o ---\n",
            Qcusp, degs;
    end if;
    for i in [1..#plcs] do
        plc := plcs[i];
        d := Degree(plc);
        RP := RepresentativePoint(plc);
        if d eq 1 then
            idx := Index([Sprint(r) : r in rats], Sprint(RP));
            is_cusp := (idx gt 0 and idx eq cusp_idx) or (Sprint(RP) in cusp_reps);
            if idx gt 0 then
                lbl := labels_ok select PointLabel(idx_to_disc, idx)
                                 else Sprintf("= P%o, unlabelled", idx);
            else
                lbl := "not in the small-point list";
            end if;
            if verbose then
                printf "  deg-1 place (mult %o): rational point %o  [%o]%o\n",
                    mults[i], RP, lbl, is_cusp select "  <-- the cusp" else "";
            end if;
            if not is_cusp then
                for m in [1..mults[i]] do Append(~results, <0, Qcusp, RP, lbl>); end for;
            end if;
        else
            if verbose then
                K := ResidueClassField(plc);
                printf "  deg-%o place (mult %o) over %o:\n      %o\n", d, mults[i], K, RP;
            end if;
        end if;
    end for;
    if verbose then
        for t in results do
            printf ">>> RESIDUAL POINT in the cusp fiber over Q = %o:\n>>>     %o   [%o]\n",
                t[2], t[3], t[4];
        end for;
    end if;
    return results, Sprintf("cusp fiber: degrees %o", degs), pb_cache;
end function;

// ---------------------------------------------------------------------------
// Rational-point fibers: for every already-known rational point P of
// X_0(M)* (CM, cusp, or exceptional alike), pull back the fiber of pi
// through Q = pi(P) and report every other rational point in that fiber,
// whether or not that other point is itself already independently known.
// Returns <results, status, pb_cache> with results = <src_idx, Q,
// residual_point, label>; pb_cache is this call's entries added to the one
// passed in, and must be rebound by the caller to persist (see CuspFiber).
// ---------------------------------------------------------------------------
function RationalPointFibers(pi, piE, X, E, rats, idx_to_disc, labels_ok, M : verbose := true, pb_cache := AssociativeArray())
    results := [* *];
    rat_strs := [Sprint(r) : r in rats];

    for j in [1..#rats] do
        ok, Q, piE := EvalPiE(pi, piE, X, E, M, X ! Eltseq(rats[j]));
        if not ok then
            printf "  P%o = %o: evaluation failed, skipping\n", j, rats[j];
            continue;
        end if;
        key := Sprint(Q);
        if not IsDefined(pb_cache, key) then
            try
                PB := Pullback(pi, Divisor(Q));
                pb_cache[key] := <true, PB>;
            catch e
                printf "  Q = %o: divisor pullback failed (%o)\n", Q, e`Object;
                pb_cache[key] := <false, 0>;
            end try;
        end if;
        ok, PB := Explode(pb_cache[key]);
        if not ok then continue; end if;
        plcs, mults := Support(PB);
        Pj_str := rat_strs[j];
        lblj := labels_ok select PointLabel(idx_to_disc, j) else Sprintf("= P%o, unlabelled", j);
        if verbose then
            degs := Sort([Degree(plcs[i]) : i in [1..#plcs]]);
            printf "\n--- fiber of pi over Q = %o through known point %o [%o], splits as degrees %o ---\n",
                Q, rats[j], lblj, degs;
        end if;
        for i in [1..#plcs] do
            plc := plcs[i];
            d := Degree(plc);
            RP := RepresentativePoint(plc);
            if d ne 1 then
                if verbose then
                    K := ResidueClassField(plc);
                    printf "  deg-%o place (mult %o) over %o:\n      %o\n", d, mults[i], K, RP;
                end if;
                continue;
            end if;
            is_self := Sprint(RP) eq Pj_str;
            idx := Index(rat_strs, Sprint(RP));
            lbl := idx gt 0 select (labels_ok select PointLabel(idx_to_disc, idx) else Sprintf("= P%o, unlabelled", idx))
                             else "NEW (not in small-point list)";
            if verbose then
                printf "  deg-1 place (mult %o): rational point %o  [%o]%o\n",
                    mults[i], RP, lbl, is_self select "  <-- P itself" else "";
            end if;
            if not is_self and (idx eq 0 or idx gt j) then
                Append(~results, <j, Q, RP, lbl>);
            end if;
        end for;
    end for;
    if verbose then
        for t in results do
            src_lbl := labels_ok select PointLabel(idx_to_disc, t[1]) else "unlabelled";
            printf ">>> PARTNER in the fiber over Q = %o (via known point %o [%o]):\n>>>     %o   [%o]\n",
                t[2], rats[t[1]], src_lbl, t[3], t[4];
        end for;
    end if;
    return results, Sprintf("%o known point(s) checked", #rats), pb_cache;
end function;

// Analyze the fiber of pi through the disc-D CM points of X_0(M)*.
// Prints a full report and returns a list of tuples <D, Q, third_point, label>,
// one per non-CM rational point found in a fiber over an image Q of the
// disc-D CM points.
function AnalyzeCMFiber(pi, X, E, fs, Sstar, M, D :
    B := 100000, label := true, cc_prec := 200, cm_terms := 3000, confirm_deg2 := false)
    printf "\n=== X_0(%o)* -> %o: fiber analysis for D = %o ===\n", M, CremonaReference(MinimalModel(E)), D;
    rats, fs_cm, idx_to_disc, labels_ok, piE, ell_pts, disc_ell_pts :=
        CMFiberSetup(pi, X, fs, Sstar, M : B := B, label := label, cm_terms := cm_terms, confirm_deg2 := confirm_deg2);
    printf "\ndisc-%o CM points of X_0(%o)* and their images under pi:\n", D, M;
    results, status := CMFiberForDisc(pi, X, E, fs_cm, rats, idx_to_disc, labels_ok,
        M, D, ell_pts, disc_ell_pts : cc_prec := cc_prec, verbose := true);
    printf "status: %o\n", status;
    return results;
end function;

// ---------------------------------------------------------------------------
// Sweep every plausible CM discriminant for one triple cover: fundamental
// D < 0 with |D| <= maxD, no prime of M inert, h(D) <= hmax, and D not
// already a rational CM disc of X_0(M)* (those points are rational, not
// conjugate pairs).  Reports, for each disc whose CM points have a rational
// image, the fiber decomposition and the third point.
// ---------------------------------------------------------------------------
function SweepCMFibers(pi, X, E, fs, Sstar, M :
    B := 100000, cm_terms := 3000, cc_prec := 200, confirm_deg2 := false)

    printf "\n===== SWEEP of CM discriminants for X_0(%o)* -> %o =====\n", M, CremonaReference(MinimalModel(E));
    rats, fs_cm, idx_to_disc, labels_ok, piE, ell_pts, disc_ell_pts :=
        CMFiberSetup(pi, X, fs, Sstar, M : B := B, cm_terms := cm_terms, confirm_deg2 := confirm_deg2);

    // exactly the discriminants (fundamental or not) whose CM points are
    // degree-2 points of X_0(M)*, by Shimura reciprocity
    deg2 := Degree2Points(M : compute_fields := false);
    discs := Sort(Setseq(Keys(deg2)), func<a, b | Abs(a) - Abs(b)>);
    printf "\ncandidate discs (degree-2 CM points on X_0(%o)*): %o\n", M, discs;

    rows := [* *];

    // Shared across CuspFiber and RationalPointFibers below so the cusp's
    // Pullback(pi, Divisor(Qcusp)); computed once by CuspFiber; is reused
    // by RationalPointFibers instead of recomputed for the same known point.
    shared_pb_cache := AssociativeArray();

    // The cusp is a rational point too: seed the sweep with its fiber (over O).
    // Magma reference (~) arguments are procedure-only, so the cache comes back
    // as a third return value and is rebound here. Passing it in and dropping
    // the result would hand RationalPointFibers a still-empty cache and
    // recompute the cusp's Pullback, the most expensive call in the sweep.
    cusp_rows, cusp_status, shared_pb_cache := CuspFiber(pi, piE, X, E, rats, idx_to_disc, labels_ok, M : pb_cache := shared_pb_cache);
    printf "cusp-fiber status: %o\n", cusp_status;
    for r in cusp_rows do Append(~rows, r); end for;

    // Every known rational point (CM, cusp, or exceptional alike) anchors a
    // fiber the same way the cusp does; check them all by default, not
    // just the ramification points (RamifiedFibers) or the cusp, for any
    // degree-1 residual not already among the known points there.  This is
    // the only way ramified/split *rational* CM partners (D not among the
    // degree-2 `discs` swept below) can surface: they never get a D-loop
    // iteration of their own.  Folded into `rows` tagged with sentinel 1
    // (0 = cusp, negative = CM disc D, so 1 cannot collide with either).
    // r[1] (the source point's rats index, see RationalPointFibers) is
    // dropped by the <1, Q, RP, lbl> shape below, so its own label (e.g.
    // "exceptional") is folded into the label string here; otherwise a pair
    // where the exceptional point is the lower-indexed side never shows
    // "exceptional" anywhere in the SWEEP/GRAND SUMMARY, only its partner's
    // CM disc.
    ratfiber_rows, ratfiber_status, shared_pb_cache := RationalPointFibers(pi, piE, X, E, rats, idx_to_disc, labels_ok, M : pb_cache := shared_pb_cache);
    printf "rational-point-fiber status: %o\n", ratfiber_status;
    for r in ratfiber_rows do
        src_lbl := labels_ok select PointLabel(idx_to_disc, r[1]) else "unlabelled";
        Append(~rows, <1, r[2], r[3], Sprintf("%o  (partner of known point %o [%o])", r[4], rats[r[1]], src_lbl)>);
    end for;

    for D in discs do
        printf "\n--- D = %o (h = %o) ---\n", D, ClassNumber(QuadraticField(D));
        results, status := CMFiberForDisc(pi, X, E, fs_cm, rats, idx_to_disc, labels_ok,
            M, D, ell_pts, disc_ell_pts : cc_prec := cc_prec, verbose := true);
        printf "status: %o\n", status;
        for r in results do Append(~rows, r); end for;
    end for;

    printf "\n================ SWEEP SUMMARY for X_0(%o)* -> %o ================\n", M, CremonaReference(MinimalModel(E));
    if #rows eq 0 then
        printf "  no CM/cusp fibers with a residual rational point found in the sweep\n";
    end if;
    for r in rows do
        if r[1] eq 0 then
            printf "  CUSP fiber |--> Q = %o; RESIDUAL POINT %o [%o]\n", r[2], r[3], r[4];
        elif r[1] eq 1 then
            printf "  RATIONAL-POINT fiber |--> Q = %o; RESIDUAL POINT %o [%o]\n", r[2], r[3], r[4];
        else
            printf "  D = %o: CM points |--> Q = %o; THIRD POINT %o [%o]\n", r[1], r[2], r[3], r[4];
        end if;
    end for;
    return rows;
end function;

// ---------------------------------------------------------------------------
// Lightweight cusp-fiber check: build the small-point list and pull back the
// single fiber over O = pi(cusp), skipping both CM labeling and the CM-disc
// sweep (the expensive parts).  This answers the census-critical question:
// "does the cusp fiber contain a rational point not already known?", for
// covers where the full sweep is too slow (large genus / uncached models).
// Residuals are reported as known small points (= P_i) or, if genuinely new,
// as "not in the small-point list" (the flag to watch for).
// ---------------------------------------------------------------------------
function RunCuspFiber(pi, X, E, fs, Sstar, M : B := 100000, cm_terms := 3000)
    printf "\n===== CUSP-FIBER-ONLY check for X_0(%o)* -> %o =====\n", M, CremonaReference(MinimalModel(E));
    // label := false skips the CM matching (the slow step); point search stays,
    // so residuals are still tested against every known small rational point.
    rats, fs_cm, idx_to_disc, labels_ok, piE :=
        CMFiberSetup(pi, X, fs, Sstar, M : B := B, cm_terms := cm_terms, label := false);
    rows, status := CuspFiber(pi, piE, X, E, rats, idx_to_disc, labels_ok, M);
    printf "cusp-fiber status: %o\n", status;
    printf "\n================ CUSP-FIBER SUMMARY for X_0(%o)* -> %o ================\n", M, CremonaReference(MinimalModel(E));
    if #rows eq 0 then
        printf "  cusp fiber has no residual rational point (cusp only / residual not rational)\n";
    end if;
    newpts := 0;
    for r in rows do
        is_new := r[4] eq "not in the small-point list";
        if is_new then newpts +:= 1; end if;
        printf "  CUSP fiber |--> Q = %o; RESIDUAL POINT %o [%o]%o\n",
            r[2], r[3], r[4], is_new select "   *** NEW/EXCEPTIONAL ***" else "";
    end for;
    printf "  residuals not in the small-point list: %o\n", newpts;
    return rows;
end function;

// ---------------------------------------------------------------------------
// Fiber point search: every rational point of X_0(M)* lies in the fiber of
// pi over a rational point of E(Q) = X_0(N)*(Q).  Enumerate E(Q) (Mordell-
// Weil group, coefficients up to nmax on the free generators) by height and
// pull back each fiber: any deg-1 place is a rational point of X_0(M)*,
// including points far beyond the PointSearch bound.  Each point found is
// labelled (CM disc / cusp / exceptional) and points not in the small-point
// list are flagged as NEW.
// Returns a list of <Q, point, label, new?>.
// ---------------------------------------------------------------------------
function FiberPointSearch(pi, X, E, fs, Sstar, M :
    nmax := 15, B := 100000, cm_terms := 3000, confirm_deg2 := false)

    printf "\n===== FIBER POINT SEARCH on X_0(%o)* -> %o (nmax = %o) =====\n", M, CremonaReference(MinimalModel(E)), nmax;
    rats, fs_cm, idx_to_disc, labels_ok, piE, ell_pts, disc_ell_pts :=
        CMFiberSetup(pi, X, fs, Sstar, M : B := B, cm_terms := cm_terms, confirm_deg2 := confirm_deg2);

    G, mG := MordellWeilGroup(E);
    inv := Invariants(G);
    printf "\nE(Q) = %o (%o)\n", inv, CremonaReference(E);
    ranges := [inv[i] eq 0 select [-nmax..nmax] else [0..inv[i] - 1] : i in [1..#inv]];
    Qs := [];
    for tup in CartesianProduct(ranges) do
        Q := mG(&+[G | tup[i] * G.i : i in [1..#inv]]);
        Append(~Qs, Q);
    end for;
    // sort by naive height of x-coordinate for readable output
    hts := [Q eq E ! 0 select 0 else Max(Abs(Numerator(Q[1])), Abs(Denominator(Q[1]))) : Q in Qs];
    Sort(~hts, ~perm);
    Qs := [Qs[j^perm] : j in [1..#Qs]];
    printf "pulling back %o fibers over points of E(Q)\n\n", #Qs;

    found := [* *];
    for Q in Qs do
        fiber_ok := true;
        try
            PB := Pullback(pi, Divisor(Q));
        catch e
            printf "Q = %o: divisor pullback failed (%o)\n", Q, e`Object;
            fiber_ok := false;
        end try;
        if not fiber_ok then continue; end if;
        plcs, mults := Support(PB);
        degs := Sort([Degree(plcs[i]) : i in [1..#plcs]]);
        if forall{d : d in degs | d gt 1} then continue; end if;   // no rational point in this fiber
        printf "Q = %o: fiber splits as degrees %o\n", Q, degs;
        for i in [1..#plcs] do
            if Degree(plcs[i]) ne 1 then continue; end if;
            RP := RepresentativePoint(plcs[i]);
            idx := Index([Sprint(r) : r in rats], Sprint(RP));
            isnew := idx eq 0;
            if isnew then
                lbl := "NEW POINT (not in the small-point list!)";
            else
                lbl := labels_ok select PointLabel(idx_to_disc, idx)
                                 else Sprintf("= P%o, unlabelled", idx);
            end if;
            printf "    rational point %o (mult %o)  [%o]\n", RP, mults[i], lbl;
            Append(~found, <Q, RP, lbl, isnew>);
        end for;
    end for;

    printf "\n================ FIBER SEARCH SUMMARY X_0(%o)* -> %o ================\n", M, CremonaReference(MinimalModel(E));
    printf "rational points found in fibers: %o (small-point list had %o)\n",
        #{Sprint(t[2]) : t in found}, #rats;
    for t in found do
        if t[4] then
            printf "  *** NEW rational point %o in the fiber over %o\n", t[2], t[1];
        end if;
    end for;
    exc := [t : t in found | not t[4] and t[3] eq "NOT CM (exceptional)"];
    for t in exc do
        printf "  exceptional point %o sits in the fiber over Q = %o\n", t[2], t[1];
    end for;
    return found;
end function;

// ===========================================================================
// Exceptional-point fiber table
// For each exceptional (non-CM, non-cusp) rational point P of X_0(M)*,
// compute the fiber of pi through P and identify the other points of the
// fiber: a quadratic place is tested against CM points of every order
// discriminant |D| <= max_absD (fundamental or not); rational places carry
// the labels from the matching.  Used by
// scripts/make_exceptional_table.m to reproduce the table of exceptional points
// explained by CM fibers.
// ===========================================================================

// Is the degree-2 place plc the pair of disc-D CM points for some D in the
// candidate list?  The candidates are the discriminants whose CM points are
// degree-2 points of X_0(M)* (Shimura reciprocity via Degree2Points), so
// only a handful of numeric comparisons are needed, no blind scan.
function IdentifyPlaceCMDisc(plc, X, fs_cm, M, ell_pts, disc_ell_pts, candidates :
    cc_prec := 200)
    hyp := Type(X) eq CrvHyp;
    CC := ComplexField(cc_prec);
    for D in candidates do
        htaus := CMTauReps(D, M, CC);
        // This bound is a cost cap, not a correctness condition.  It counts
        // <Gamma_0(M), AL>-orbits; i.e. distinct points of X_0(M)*, and
        // skips discriminants with more than 16 orbits.  This only ever costs
        // a *skip*: a discriminant here is not offered as an explanation for
        // an exceptional point, which is a missed positive, never a wrong
        // one.  No test in the repo currently exercises this function (only
        // scripts/make_exceptional_table.m's ExceptionalFiberRows reaches it).
        if #htaus eq 0 or #htaus gt 16 then continue; end if;
        ell_order := 1;
        for ell in [2,3,4,6] do
            if D in Keys(ell_pts[ell]) then ell_order := ell; break; end if;
        end for;
        evals := [* *];
        for tau in htaus do
            if hyp then
                ev := EvaluateAtCM_hyperelliptic(fs_cm, tau, CC : ell_order := ell_order,
                          P_poly := HyperellipticPolynomials(X));
                if #ev eq 2 then Append(~evals, [ev[1], ev[2], CC!1]); end if;
                if #ev eq 3 then Append(~evals, ev); end if;
            else
                ev := EvaluateAtCM(fs_cm, tau, CC, D, ell_pts, disc_ell_pts, M);
                if #ev gt 0 then Append(~evals, ev); end if;
            end if;
        end for;
        if #evals gt 0 and PlaceMatchesEvals(plc, evals, CC) then
            return true, D;
        end if;
    end for;
    return false, 0;
end function;

// Rows of the exceptional-fiber table for one triple cover X_0(M)* -> E.
// Each row is <M, genus, cond, cofactor, exc_point, partner_string, cm_discs,
// has_cm, Elabel>, where cond = Conductor(E) is the newform level and
// cofactor = M/cond.  An own-level cover has cond = M and cofactor = 1, which
// is the "new" row marker scripts/make_exceptional_table.m keys on.
// known_discs: discriminants expected for the quadratic fiber partners; these
// are tried first.  discover := true additionally tries every disc whose CM
// points are degree-2 points of X_0(M)* (Degree2Points); with discover :=
// false only the known discs are checked (fast verification of the table).
function ExceptionalFiberRows(M, Elabel : B := 100000, cm_terms := 3000, cache_prec := 3000,
    known_discs := [], discover := true, confirm_deg2 := false)
    pi, X, E, fs, Sstar, c := BuildTripleCover(M, Elabel : cache_prec := cache_prec);
    // cond/cofactor, not d: `d` is the place degree in the fiber loops below,
    // and both are resolved once here so no inner binding can reach the row.
    // ExactQuotient rather than `div` so a non-dividing conductor raises
    // instead of rounding down to a plausible-looking level.
    cond := Conductor(E);
    cofactor := ExactQuotient(M, cond);
    g := Genus(X);
    rats, fs_cm, idx_to_disc, labels_ok, piE, ell_pts, disc_ell_pts :=
        CMFiberSetup(pi, X, fs, Sstar, M : B := B, cm_terms := cm_terms, print_points := false, confirm_deg2 := confirm_deg2);
    error if not labels_ok,
        Sprintf("ExceptionalFiberRows: labeling failed for M = %o, cannot find the exceptional points", M);
    exc_idxs := [j : j in [1..#rats] | not IsDefined(idx_to_disc, j)];
    printf "X_0(%o)*: %o exceptional point(s)\n", M, #exc_idxs;
    // candidate discs for a quadratic place in a fiber: the known ones first,
    // then (in discovery mode) every disc whose CM points are degree-2 points
    // of X_0(M)* (Shimura reciprocity)
    candidates := known_discs;
    if discover then
        deg2 := Degree2Points(M : compute_fields := false);
        extra := Sort([D0 : D0 in deg2_discs | D0 notin known_discs], func<a, b | Abs(a) - Abs(b)>)
            where deg2_discs := Setseq(Keys(deg2));
        candidates cat:= extra;
    end if;
    printf "  candidate quadratic-CM discs (%o): %o\n",
        discover select "known + degree-2 list" else "known only", candidates;
    rows := [* *];
    for j in exc_idxs do
        P := X ! Eltseq(rats[j]);
        ok, Q, piE := EvalPiE(pi, piE, X, E, M, P);
        if not ok then
            printf "  exceptional %o: evaluation failed, skipping\n", P;
            continue;
        end if;
        printf "  exceptional %o |--> Q = %o; analyzing fiber...\n", P, Q;
        try
            PB := Pullback(pi, Divisor(Q));
        catch e
            printf "  Q = %o: divisor pullback failed (%o)\n", Q, e`Object;
            continue;
        end try;
        plcs, mults := Support(PB);
        partners := [];
        discs := [];
        has_cm := false;
        for i in [1..#plcs] do
            plc := plcs[i];
            d := Degree(plc);
            RP := RepresentativePoint(plc);
            m := mults[i];
            if d eq 1 and Sprint(RP) eq Sprint(P) then
                if m gt 1 then Append(~partners, Sprintf("exceptional point doubled (mult %o)", m)); end if;
                continue;
            end if;
            if d eq 1 then
                idx := Index([Sprint(r) : r in rats], Sprint(RP));
                lbl := idx gt 0 select PointLabel(idx_to_disc, idx) else "point not in small list";
                if idx gt 0 and IsDefined(idx_to_disc, idx) and idx_to_disc[idx] ne 0 then
                    has_cm := true;
                    Append(~discs, idx_to_disc[idx]);
                end if;
                Append(~partners, Sprintf("rational point %o [%o]%o", RP, lbl,
                    m gt 1 select Sprintf(", mult %o", m) else ""));
            else
                okD, D := IdentifyPlaceCMDisc(plc, X, fs_cm, M, ell_pts, disc_ell_pts, candidates);
                if okD then
                    has_cm := true;
                    Append(~discs, D);
                    Append(~partners, Sprintf("quadratic CM pair of disc %o over %o", D, ResidueClassField(plc)));
                else
                    Append(~partners, Sprintf("quadratic pair over %o, NOT CM",
                        ResidueClassField(plc)));
                end if;
            end if;
        end for;
        Append(~rows, <M, g, cond, cofactor, Sprint(P), Join(partners, "; "), discs, has_cm,
            CremonaReference(E)>);
    end for;
    return rows;
end function;

// ---------------------------------------------------------------------------
// Ramified fibers: the ramification divisor of pi is the zero divisor of the
// pullback differential pi^* omega_E (omega_E has neither zeros nor poles).
// Every rational ramification point P gives a fiber 2P + R with R a rational
// point of X_0(M)*, a height-unbounded source of rational points on rank-1
// bases.  Reports every such fiber with labels; NEW points are flagged.
// Returns a list of <P_ram, Q, residual_point, label>.
// ---------------------------------------------------------------------------
function RamifiedFibers(pi, X, E, fs, Sstar, M : B := 100000, cm_terms := 3000, confirm_deg2 := false)
    printf "\n===== RAMIFIED FIBERS of X_0(%o)* -> (%o) =====\n", M, CremonaReference(E);
    rats, fs_cm, idx_to_disc, labels_ok, piE, ell_pts, disc_ell_pts :=
        CMFiberSetup(pi, X, fs, Sstar, M : B := B, cm_terms := cm_terms, print_points := false, confirm_deg2 := confirm_deg2);

    FE := FunctionField(E);
    xpi := Pullback(pi, FE.1);
    ypi := Pullback(pi, FE.2);
    a1, a2, a3, a4, a6 := Explode(aInvariants(E));
    omega := Differential(xpi) / (2*ypi + a1*xpi + a3);
    R := Divisor(omega);
    plcs, mults := Support(R);
    printf "ramification divisor: degree %o (= 2g - 2 = %o), %o places of degrees %o\n",
        Degree(R), 2*Genus(X) - 2, #plcs, [Degree(pl) : pl in plcs];

    results := [* *];
    for i in [1..#plcs] do
        if Degree(plcs[i]) ne 1 then continue; end if;
        P := RepresentativePoint(plcs[i]);
        idxP := Index([Sprint(r) : r in rats], Sprint(P));
        lblP := idxP gt 0 select (labels_ok select PointLabel(idx_to_disc, idxP) else "unlabelled")
                          else "NEW (not in small-point list)";
        ok, Q, piE := EvalPiE(pi, piE, X, E, M, X ! Eltseq(P));
        if not ok then
            printf "\nrational ramification point %o  [%o]: evaluation failed, skipping\n", P, lblP;
            continue;
        end if;
        printf "\nrational ramification point %o  [%o]  over Q = %o (e = %o)\n",
            P, lblP, Q, mults[i] + 1;
        PB := Pullback(pi, Divisor(Q));
        fplcs, fmults := Support(PB);
        for j in [1..#fplcs] do
            d := Degree(fplcs[j]);
            RP := RepresentativePoint(fplcs[j]);
            if d eq 1 then
                if Sprint(RP) eq Sprint(P) then continue; end if;
                idx := Index([Sprint(r) : r in rats], Sprint(RP));
                lbl := idx gt 0 select (labels_ok select PointLabel(idx_to_disc, idx) else "unlabelled")
                               else "*** NEW RATIONAL POINT ***";
                printf "  residual rational point: %o  [%o]\n", RP, lbl;
                Append(~results, <P, Q, RP, lbl>);
            else
                printf "  (deg-%o place in fiber, mult %o)\n", d, fmults[j];
            end if;
        end for;
    end for;
    printf "\n================ RAMIFIED-FIBER SUMMARY X_0(%o)* ================\n", M;
    if #results eq 0 then printf "  no rational ramification points\n"; end if;
    for r in results do
        printf "  ram. pt %o -> residual %o  [%o]\n", r[1], r[3], r[4];
    end for;
    return results;
end function;
