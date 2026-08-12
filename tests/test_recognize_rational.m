// tests/test_recognize_rational.m
// Direct unit test for RecognizeRationalWithHeightBound (src/labelling.m):
// fast, no model-building or CM machinery; pure arithmetic on hand-built
// values.
//
// Regression test for the uniqueness-bound fix: without a check that the
// accepted rational is forced (not coincidental) at its height, an
// irrational value with an unusually good low-height continued-fraction
// convergent, e.g. Sqrt(2)-1 ~= 275807/665857, error ~1.6e-12; can be
// misrecognized as exactly rational at the tolerances CertifiedPlaneFromCMPair
// actually uses (recon_tol as loose as ~1e-11 at the error_max_recon gate
// boundary, cofactor_hb=1e12). Both lo/hi runs would agree on the same wrong
// convergent regardless of precision, so this was not caught by the
// dual-precision agreement check.
//
// Run with: tests/run.sh test_recognize_rational

load "src/AtkinLehner.m";
load "tests/assertions.m";

results := NewResults();

// The pre-fix formula, kept only here as a comparison baseline to
// demonstrate the bug the uniqueness gate addresses, not used in src/.
function OldRecognizeRationalWithHeightBound(val, tol, hb_max)
    if Abs(Imaginary(val)) gt tol*(1+Abs(val)) then return <2, Rationals()!0>; end if;
    re := Real(val);
    hbs := [10^k : k in [2,4,6,8,10,12] | 10^k le hb_max];
    if #hbs eq 0 or hbs[#hbs] ne hb_max then Append(~hbs, hb_max); end if;
    for hbk in hbs do
        r := BestApproximation(re, hbk);
        if Abs(re - r) le tol*(1+Abs(re)) then
            return r eq 0 select <0, Rationals()!0> else <1, r>;
        end if;
    end for;
    return <2, Rationals()!0>;
end function;

CC := ComplexField(50);

// Worst-case gate boundary actually used by CertifiedPlaneFromCMPair's
// defaults: recon_tol = Maximum(recon_C*observed_error, floor) can reach
// ~10*error_max_recon = 10*10^-12 = 10^-11 just under the accuracy gate;
// cofactor_hb defaults to 10^12.
tol    := 10^-11;
hb_max := 10^12;

// -------------------------------------------------------------------------
// Irrational values with unusually good low-height convergents: the new
// code must refuse to certify these as rational.
// -------------------------------------------------------------------------
irrationals := [
    <"Sqrt(2)-1", CC!(Sqrt(RealField(50)!2) - 1)>,
    <"Sqrt(3)-1", CC!(Sqrt(RealField(50)!3) - 1)>
];

for pair in irrationals do
    label, val := Explode(pair);

    rec_new := RecognizeRationalWithHeightBound(val, tol, hb_max);
    AssertEqual(~results, rec_new[1], 2,
        Sprintf("%o is correctly NOT certified rational at tol=%o, hb_max=%o", label, tol, hb_max));

    rec_old := OldRecognizeRationalWithHeightBound(val, tol, hb_max);
    AssertEqual(~results, rec_old[1], 1,
        Sprintf("(characterization) the OLD formula incorrectly certified %o as rational, the bug the fix addresses", label));
end for;

// -------------------------------------------------------------------------
// Non-regression: genuine low-height rationals must still be recognized.
// -------------------------------------------------------------------------
rec_37 := RecognizeRationalWithHeightBound(CC!(3/7), 10^-13, 100);
AssertEqual(~results, rec_37[1] eq 1 and rec_37[2] eq 3/7, true,
    Sprintf("3/7 is recognized at tight tol / low height (got %o)", rec_37));

rec_0 := RecognizeRationalWithHeightBound(CC!0, 10^-13, 100);
AssertEqual(~results, rec_0[1], 0,
    "0 is recognized as the zero case");

// A rational just inside the uniqueness-certifiable range at a much looser
// tolerance should still be found, the fix should not be so conservative
// that it rejects genuine rationals with headroom to spare.
rec_headroom := RecognizeRationalWithHeightBound(CC!(22/7), 10^-20, 1000);
AssertEqual(~results, rec_headroom[1] eq 1 and rec_headroom[2] eq 22/7, true,
    Sprintf("22/7 is recognized with ample uniqueness headroom (got %o)", rec_headroom));

// -------------------------------------------------------------------------
// Regression for the intermediate-height-bound bug: an earlier version of
// RecognizeRationalWithHeightBound escalated through a schedule of
// intermediate height bounds (10^2, 10^4, ..., hb_max) and accepted the
// first candidate whose uniqueness gate passed at that intermediate bound,
// rather than requiring uniqueness at the full hb_max. Uniqueness among
// rationals of denominator <= hbk does not imply uniqueness among rationals
// of denominator <= hb_max, since a different rational with denominator in
// (hbk, hb_max] can also lie in the eps-ball; so that version could
// silently replace a genuine small nonzero rational allowed under hb_max
// with an incorrect lower-height one. At tol=10^-11, hb_max=10^12, neither
// case below can be certified unique (2*eps*hb_max^2 >> 1), so both must be
// reported inconclusive (<2, _>), never a specific (wrong) rational.
// -------------------------------------------------------------------------
tol_bug    := 10^-11;
hb_max_bug := 10^12;

rec_tiny := RecognizeRationalWithHeightBound(CC!(1/10^12), tol_bug, hb_max_bug);
AssertEqual(~results, rec_tiny[1], 2,
    Sprintf("1/10^12 at tol=%o, hb_max=%o is correctly NOT certified (must not be silently replaced by 0)",
        tol_bug, hb_max_bug));

rec_near_half := RecognizeRationalWithHeightBound(CC!(500000000001/1000000000000), tol_bug, hb_max_bug);
AssertEqual(~results, rec_near_half[1], 2,
    Sprintf("500000000001/1000000000000 at tol=%o, hb_max=%o is correctly NOT certified (must not be silently replaced by 1/2)",
        tol_bug, hb_max_bug));

Report(~results, "test_recognize_rational");
