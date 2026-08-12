// tests/test_plane_from_cm_pair_cofactor.m
// Direct unit test for PlaneFromCMPairCofactor (src/labelling.m): fast, no
// model-building or CM machinery, pure arithmetic on a hand-built
// conjugate pair.
//
// Regression test for the scale-invariance fix: the degeneracy gate
// Abs(vi_cc[piv]) lt tol compared a raw cofactor/determinant magnitude
// (which scales with the input rows' raw coordinate magnitudes) against a
// dimensionless tolerance, so rescaling a projectively-equivalent input by
// a large or small factor could flip the degeneracy verdict even though the
// actual geometric configuration (and the resulting plane) is unchanged.
//
// Run with: tests/run.sh test_plane_from_cm_pair_cofactor

load "src/AtkinLehner.m";
load "tests/assertions.m";

results := NewResults();

// The pre-fix version, kept only here as a comparison baseline; not used
// anywhere in src/.
function OldPlaneFromCMPairCofactor(exc_coords, ev1, ev2, CC, tol, hb_max)
    g := #exc_coords;
    if #ev1 ne g or #ev2 ne g then return false, []; end if;
    pt_Q := [CC!c : c in exc_coords];
    M_pl := Matrix(CC, 3, g, pt_Q cat ev1 cat ev2);
    if g gt 4 then return false, []; end if;
    vi_cc := [];
    for col in [1..g] do
        cols := [c : c in [1..g] | c ne col];
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
            ok := false; break;
        end if;
    end for;
    if not ok then return false, []; end if;
    lcm_d := LCM([Denominator(vi_rat[l]) : l in [1..g]]);
    vi := [Integers()!(vi_rat[l] * lcm_d) : l in [1..g]];
    gv := GCD(vi); if gv ne 0 then vi := [vi[l] div gv : l in [1..g]]; end if;
    if &and[vi[l] eq 0 : l in [1..g]] then return false, []; end if;
    return true, vi;
end function;

// -------------------------------------------------------------------------
// g=4: a rational exceptional point and a hand-built conjugate pair, both
// exactly on the plane z1+z2+z3+z4=0.
// -------------------------------------------------------------------------
CC := ComplexField(50);
exc_coords := [Rationals()| 1, -1, 0, 0];
w  := CC!2 + CC!3*CC.1;
ev1 := [CC!1, w, CC!1, -2-w];
ev2 := [CC!1, Conjugate(w), CC!1, -2-Conjugate(w)];

tol    := 10^-20;
hb_max := 10^6;

ok0, vi0 := PlaneFromCMPairCofactor(exc_coords, ev1, ev2, CC, tol, hb_max);
AssertEqual(~results, ok0 and CanonicalPlaneKey(vi0) eq [1,1,1,1], true,
    Sprintf("baseline (unscaled) input recovers plane [1,1,1,1] up to sign (got ok=%o, vi=%o)", ok0, vi0));

// Rescale ev1/ev2 by a tiny real factor, the same projective points, just
// represented with a much smaller-magnitude coordinate vector (Conjugate of
// a real scalar is itself, so ev2 stays exactly Conjugate(ev1) elementwise).
tiny := CC!(10^-25);
ev1_scaled := [tiny*e : e in ev1];
ev2_scaled := [tiny*e : e in ev2];

ok_new, vi_new := PlaneFromCMPairCofactor(exc_coords, ev1_scaled, ev2_scaled, CC, tol, hb_max);
AssertEqual(~results, ok_new eq ok0 and (not ok_new or CanonicalPlaneKey(vi_new) eq CanonicalPlaneKey(vi0)), true,
    Sprintf("fixed code: rescaling ev1/ev2 by 10^-25 does not change the verdict or the recovered plane (got ok=%o, vi=%o)", ok_new, vi_new));

// The old code's degeneracy gate is expected to be scale-sensitive: this is
// a characterization check on the pre-fix formula, not on current code.
ok_old_base, _ := OldPlaneFromCMPairCofactor(exc_coords, ev1, ev2, CC, tol, hb_max);
ok_old_scaled, _ := OldPlaneFromCMPairCofactor(exc_coords, ev1_scaled, ev2_scaled, CC, tol, hb_max);
AssertEqual(~results, ok_old_base and not ok_old_scaled, true,
    Sprintf("(characterization) OLD code succeeds unscaled but spuriously reports degenerate once rescaled (got ok_base=%o, ok_scaled=%o); the bug the fix addresses", ok_old_base, ok_old_scaled));

// Also check scaling the other direction (large factor) still recovers the
// same plane under the fixed code.
big := CC!(10^25);
ev1_big := [big*e : e in ev1];
ev2_big := [big*e : e in ev2];
ok_big, vi_big := PlaneFromCMPairCofactor(exc_coords, ev1_big, ev2_big, CC, tol, hb_max);
AssertEqual(~results, ok_big eq ok0 and (not ok_big or CanonicalPlaneKey(vi_big) eq CanonicalPlaneKey(vi0)), true,
    Sprintf("fixed code: rescaling ev1/ev2 by 10^25 does not change the verdict or the recovered plane (got ok=%o, vi=%o)", ok_big, vi_big));

Report(~results, "test_plane_from_cm_pair_cofactor");
