load "src/AtkinLehner.m";
load "tests/assertions.m";

results := NewResults();

function SlowDegree(N, d)
    deg := -1;
    try
        flds, _ := FieldsOfDefinitionOfCMPoint(N, d);
        deg := #flds eq 0 select 0 else Degree(flds[1]);
    catch e
        deg := -1;  // slow function errored; skip this pair
    end try;
    return deg;
end function;

// Wider N coverage: omega 1-4
Nvalues := [
    // omega=1
    11, 17, 19, 23, 37, 41, 67, 83, 97,
    // omega=2
    22, 26, 33, 38, 46, 55, 62, 65, 74, 77, 85, 87, 91, 95, 111, 115,
    // omega=3
    66, 78, 110, 114, 130, 138, 154, 165, 170, 182, 190, 210, 231,
    // omega=4
    330, 390, 462, 510, 546, 858
];

// Fundamental discriminants (conductor f=1)
fund_discs := [
    -3,-4,-7,-8,-11,-15,-19,-20,-23,-24,-31,-35,-40,-43,-47,
    -51,-52,-55,-59,-67,-71,-79,-83,-84,-87,-88,-91,-95,
    -107,-111,-115,-116,-120,-123,-132,-136,-139,-148,-151,
    -155,-163,-168,-184,-187,-195,-203,-211,-219,-228,-231
];

// Non-fundamental discriminants (conductor f > 1): d = f^2 * D_K
// f=2
f2_discs := [-12,-16,-28,-32,-44,-48,-60,-76,-88,-92,-112,-120];
// f=3
f3_discs := [-27,-36,-63,-72,-99,-108,-171,-243];
// f=4
f4_discs := [-48,-64,-112,-176,-192];
// f=5
f5_discs := [-75,-100,-175,-275];
// f=6
f6_discs := [-108,-144,-252];

discs := fund_discs cat f2_discs cat f3_discs cat f4_discs cat f5_discs cat f6_discs;

// Deduplicate (some overlap between f-families and fund_discs)
discs := SetToSequence(SequenceToSet(discs));

// Validate: keep only valid quadratic discriminants
valid_discs := [];
for d in discs do
    if (d mod 4) in {0, 1} then
        ok := true;
        try _ := BinaryQuadraticForms(d); catch e ok := false; end try;
        if ok then Append(~valid_discs, d); end if;
    end if;
end for;
discs := valid_discs;

printf "Testing %o N values x %o discriminants = %o pairs\n\n",
    #Nvalues, #discs, #Nvalues * #discs;

total := 0; failures := 0; skipped := 0; nontrivial := 0;
t0 := Cputime();

for N in Nvalues do
    for d in discs do
        deg_slow := SlowDegree(N, d);
        if deg_slow eq -1 then skipped +:= 1; continue; end if;
        deg_fast := DegreeOfFieldOfDefinitionOfCMPoint(N, d);
        total +:= 1;
        AssertEqual(~results, deg_fast, deg_slow,
            Sprintf("N=%o d=%o: DegreeOfFieldOfDefinitionOfCMPoint agrees with FieldsOfDefinitionOfCMPoint",
                N, d));
        if deg_slow ne deg_fast then
            failures +:= 1;
        elif deg_slow gt 0 then
            nontrivial +:= 1;
        end if;
    end for;
end for;

printf "Tested %o pairs (%o skipped) in %o s\n", total, skipped, Cputime()-t0;
printf "Non-trivial CM pairs: %o\n", nontrivial;

// A skipped pair is one where FieldsOfDefinitionOfCMPoint threw and SlowDegree
// swallowed it.  This is asserted rather than merely counted, because a skipped
// pair runs no comparison: if every pair threw, the loop above would make zero
// assertions and a total collapse would otherwise be indistinguishable from a
// total success.  (Report also refuses to pass a suite that asserted nothing,
// which is a second net under the same hole.)
AssertEqual(~results, skipped, 0,
    Sprintf("no pairs errored inside FieldsOfDefinitionOfCMPoint (of %o attempted)",
        #Nvalues * #discs));

printf "\n";
Report(~results, "test_degree_formula");
