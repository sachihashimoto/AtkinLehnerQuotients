// test_cm_field_of_definition.m
// Regression test for FieldsOfDefinitionOfCMPoint (src/fields_of_definition.m).
//
// Q(P) is the subfield of A_abs fixed by sigma = c . sigma_a, where A_abs is the
// part of the ring class field H_R fixed by the Atkin-Lehner involutions that act
// as Galois automorphisms, c is complex conjugation and a is an ideal of norm
// N_star_R.  See arXiv:math/0612732v2, Gonzalez-Rotger, Appendix.
//
// The field is a single one and depends on the level: d = -39 gives Q(sqrt(13))
// at N = 286 but Q(sqrt(-3)) at N = 26.
//
// Where the expected values come from.  For f = 1 and for every row of degree
// other than 2 they were generated from ShimuraCurveALQuotients/SchoferFormula.m,
// specialised to D = 1, W = all of Divisors(N).  The three rows of degree 2 with
// f > 1, namely (11, -32), (39, -36) and (377, -36), are where the quaternion
// condition of Gonzalez-Rotger Lemma 5.10 allows two fields.  There A_abs is
// biquadratic, and Q(P) = Q(sqrt(D1)) for the quadratic subfield with
// sign(D1) * KroneckerSymbol(D1, N_star_R) = 1, because sigma_a multiplies
// sqrt(D1) by that Kronecker symbol and c multiplies it by sign(D1).  The rule
// is restated below as its own check.  This test has no dependency on the other
// repository.
//
// Run with: tests/run.sh test_cm_field_of_definition

load "src/AtkinLehner.m";
load "tests/assertions.m";

results := NewResults();

// Tag a field of degree <= 2 by the squarefree part of its discriminant
// (1 for Q); tag higher-degree fields by 10000*degree.  Must match Tag() in
// scripts/gen_cm_field_expectations.m.
function FieldTag(F)
    if Degree(F) eq 1 then return 1; end if;
    if Degree(F) gt 2 then return 10000*Degree(F); end if;
    return Squarefree(Discriminant(MaximalOrder(F)));
end function;

function DistinctTags(flds)
    return Sort(SetToSequence({FieldTag(F) : F in flds}));
end function;

printf "\n=== FieldsOfDefinitionOfCMPoint: fields agree with the reference ===\n";

// <N, d, #fields, sorted distinct field tags>
cases := [
    <11, -39, 1, [ 40000 ]>,
    <11, -95, 1, [ 80000 ]>,
    <11, -36, 0, []>,
    <11, -32, 1, [ -1 ]>,
    <11, -20, 0, []>,
    <11, -23, 0, []>,
    <11, -84, 1, [ 40000 ]>,
    <26, -39, 1, [ -3 ]>,
    <26, -95, 1, [ 80000 ]>,
    <26, -36, 1, [ 1 ]>,
    <26, -32, 0, []>,
    <26, -20, 0, []>,
    <26, -23, 1, [ 30000 ]>,
    <26, -84, 0, []>,
    <39, -39, 1, [ 13 ]>,
    <39, -95, 1, [ 80000 ]>,
    <39, -36, 1, [ 3 ]>,
    <39, -32, 0, []>,
    <39, -20, 0, []>,
    <39, -23, 1, [ 30000 ]>,
    <39, -84, 0, []>,
    <77, -39, 0, []>,
    <77, -95, 0, []>,
    <77, -36, 0, []>,
    <77, -32, 0, []>,
    <77, -20, 0, []>,
    <77, -23, 0, []>,
    <77, -84, 1, [ -3 ]>,
    <143, -39, 1, [ -3 ]>,
    <143, -95, 1, [ 80000 ]>,
    <143, -36, 0, []>,
    <143, -32, 0, []>,
    <143, -20, 0, []>,
    <143, -23, 0, []>,
    <143, -84, 0, []>,
    <286, -39, 1, [ 13 ]>,
    <286, -95, 1, [ 80000 ]>,
    <286, -36, 0, []>,
    <286, -32, 0, []>,
    <286, -20, 0, []>,
    <286, -23, 0, []>,
    <286, -84, 0, []>,
    <377, -39, 0, []>,
    <377, -95, 0, []>,
    <377, -36, 1, [ -3 ]>,
    <377, -32, 0, []>,
    <377, -20, 0, []>,
    <377, -23, 1, [ 30000 ]>,
    <377, -84, 0, []>,
    <510, -39, 0, []>,
    <510, -95, 0, []>,
    <510, -36, 1, [ 1 ]>,
    <510, -32, 0, []>,
    <510, -20, 0, []>,
    <510, -23, 0, []>,
    <510, -84, 1, [ 1 ]>,
];

// FieldTag collapses every field of degree > 2 to 10000*Degree(F), so tags
// alone cannot tell one degree-8 field from several.  Assert #flds alongside
// the tags so the high-degree rows stay discriminating.
rc := AssociativeArray();
for c in cases do
    N := c[1]; d := c[2]; expected_n := c[3]; expected := c[4];
    flds, rc := FieldsOfDefinitionOfCMPoint(N, d : rc_cache := rc);
    got := DistinctTags(flds);
    AssertEqual(~results, (#flds eq expected_n) and (got eq expected), true,
        Sprintf("N=%o, d=%o: %o field(s) with tags %o (got %o with %o)",
            N, d, expected_n, expected, #flds, got));
end for;

// Proposition 5.6 early exit still returns the empty list.
flds_empty, _ := FieldsOfDefinitionOfCMPoint(26, -32);
AssertEqual(~results, #flds_empty, 0,
    "N=26, d=-32: Prop 5.6 rules out a CM point, empty list");

// The degree of the field must agree with DegreeOfFieldOfDefinitionOfCMPoint,
// which never builds the field.  "#flds eq 0" below corresponds to "c[3] = 0"
// (no CM point) above.
printf "\n=== degree agrees with the fast degree function ===\n";
for c in cases do
    N := c[1]; d := c[2];
    flds, rc := FieldsOfDefinitionOfCMPoint(N, d : rc_cache := rc);
    if #flds eq 0 then continue; end if;
    fast := DegreeOfFieldOfDefinitionOfCMPoint(N, d);
    AssertEqual(~results, [Integers()| Degree(F) : F in flds], [fast],
        Sprintf("N=%o, d=%o: one field, of the degree the fast function gives", N, d));
end for;

// The sign rule of the header, computed here without the ring class field, on
// every quadratic row.  Five of those rows have f = 1 and come from the
// reference, so they test the rule; the other three were derived from it.
printf "\n=== quadratic fields obey the sign rule for complex conjugation ===\n";
function NStarR(N, d)
    R := QuadraticOrder(BinaryQuadraticForms(d));
    f := Conductor(R);
    chi := KroneckerCharacter(d);
    return &*[Integers()| p : p in PrimeDivisors(N) | chi(p) eq 1 and (f mod p ne 0)];
end function;
for c in cases do
    N := c[1]; d := c[2];
    if c[3] ne 1 or Abs(c[4][1]) ge 10000 or c[4][1] eq 1 then continue; end if;
    D1 := c[4][1];
    m := NStarR(N, d);
    AssertEqual(~results, Sign(D1) * KroneckerSymbol(D1, m), 1,
        Sprintf("N=%o, d=%o: Q(sqrt(%o)) is fixed by c . sigma_a for a of norm %o", N, d, D1, m));
end for;

// Two discriminants of the same field K, one after the other, both with A_abs = K
// (rational CM points on X_0(30)*).  K is kept alive so that anything Magma caches
// on it survives from the first call to the second.
printf "\n=== A_abs = K at two discriminants sharing K ===\n";
keep15 := NumberField(QuadraticOrder(BinaryQuadraticForms(-15)));
rc15 := AssociativeArray();
for d in [-60, -15] do
    flds, rc15 := FieldsOfDefinitionOfCMPoint(30, d : rc_cache := rc15);
    AssertEqual(~results, [Integers()| Degree(F) : F in flds], [1],
        Sprintf("N=30, d=%o: the field of definition is Q", d));
    AssertEqual(~results, DegreeOfFieldOfDefinitionOfCMPoint(30, d), 1,
        Sprintf("N=30, d=%o: the fast degree function gives 1", d));
end for;
AssertEqual(~results, Degree(keep15), 2, "Q(sqrt(-15)) is still alive after both calls");

Report(~results, "test_cm_field_of_definition");
