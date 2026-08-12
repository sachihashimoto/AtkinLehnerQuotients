// tests/test_match_h2_hyperplane.m
// Direct unit test for MatchH2DataToHyperplane (src/labelling.m): fast, no
// model-building or CM machinery, pure arithmetic on hand-built vectors.
//
// Regression test for the scale-invariance fix: the membership check used a
// raw |vi.ev| lt tol comparison instead of the ScaleInvariantResidual
// already defined earlier in the file for exactly this purpose, so
// rescaling an evaluation by a nonzero factor (a projectively-equivalent
// representative of the same point) could flip the verdict.
//
// Run with: tests/run.sh test_match_h2_hyperplane

load "src/AtkinLehner.m";
load "tests/assertions.m";

results := NewResults();

// The pre-fix version, kept only here as a comparison baseline; not used
// anywhere in src/.
function OldMatchH2DataToHyperplane(vi, h2_data, CC, tol)
    matches := [* *];
    for entry in h2_data do
        d := entry[1]; evs := entry[2];
        n_on := #{l : l in [1..#evs] | Abs(&+[vi[k]*evs[l][k] : k in [1..#vi]]) lt tol};
        if n_on ge 2 then
            Append(~matches, d);
        end if;
    end for;
    return matches;
end function;

CC := ComplexField(50);
vi := [1, -1, 0];

// Two conjugate evaluations only approximately on the plane vi.z=0
// (z1-z2 = -eps, a small but nonzero residual); realistic for a numerical
// CM evaluation, unlike an exactly-zero dot product, which no rescaling
// could ever push past a tolerance. eps is real, so ev_b stays exactly
// Conjugate(ev_a) elementwise.
w   := CC!2 + CC!3*CC.1;
eps := CC!(10^-16);
ev_a := [w, w+eps, CC!5];
ev_b := [Conjugate(w), Conjugate(w)+eps, CC!5];

h2_data := [* <-7, [ev_a, ev_b]> *];

// Fixed code: a tolerance on the scale-invariant residual, well above the
// true relative residual (~eps/(|vi|*|ev_a)| ~ 10^-17), should match
// regardless of how ev_a/ev_b happen to be scaled.
tol_new := 10^-10;

matches_base := MatchH2DataToHyperplane(vi, h2_data, CC, tol_new);
AssertEqual(~results, matches_base, [* -7 *],
    Sprintf("baseline: disc -7 matches the hyperplane vi=%o", vi));

// Rescale both evaluations by a large factor, same projective points, but
// the raw dot product (which was only ~10^-16 to begin with) scales up too.
big := CC!(10^10);
ev_a_scaled := [big*x : x in ev_a];
ev_b_scaled := [big*x : x in ev_b];
h2_data_scaled := [* <-7, [ev_a_scaled, ev_b_scaled]> *];

matches_new := MatchH2DataToHyperplane(vi, h2_data_scaled, CC, tol_new);
AssertEqual(~results, matches_new, [* -7 *],
    "fixed code: rescaling evs by 10^10 does not change the match");

// The old code's raw dot-product check, at a fixed absolute tolerance that
// accepts the small unscaled residual, is expected to reject the same
// (projectively identical) point once rescaled, a characterization check
// on the pre-fix formula, not current code.
tol_old := 10^-15;
matches_old_base := OldMatchH2DataToHyperplane(vi, h2_data, CC, tol_old);
matches_old_scaled := OldMatchH2DataToHyperplane(vi, h2_data_scaled, CC, tol_old);
AssertEqual(~results, matches_old_base eq [* -7 *] and matches_old_scaled eq [* *], true,
    Sprintf("(characterization) OLD code matches unscaled but loses the match once rescaled (got base=%o, scaled=%o); the bug the fix addresses", matches_old_base, matches_old_scaled));

Report(~results, "test_match_h2_hyperplane");
