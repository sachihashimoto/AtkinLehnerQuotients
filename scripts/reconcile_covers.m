// scripts/reconcile_covers.m
//
// Cross-check the enumerated cover list against the cached maps, both ways.
//
// Each cached map was verified by an explicit degree-3 check when it was built
// (TryMapDegree), so it is independent evidence that a cover exists; it does
// not depend on the degree formula being right.  That makes the cache an oracle
// for the sweep:
//
//   * a cached map with no enumerated cover means the sweep lost one.  That is a
//     bug to investigate, never a file to delete.
//   * an enumerated cover with no cached map needs the map built.
//
// Run:  magma -b scripts/reconcile_covers.m > /tmp/rec.txt 2>&1; cat /tmp/rec.txt

// Magma will not coerce a string to an integer; test the digits explicitly.
function IsIntegerString(s)
    if #s eq 0 then return false, 0; end if;
    for i in [1..#s] do
        if not s[i] in "0123456789" then return false, 0; end if;
    end for;
    return true, StringToInteger(s);
end function;

// A Cremona label: digits, then letters, then digits.
function IsCremonaLabel(s)
    i := 1;
    while i le #s and s[i] in "0123456789" do i +:= 1; end while;
    if i eq 1 then return false; end if;
    j := i;
    while j le #s and s[j] in "abcdefghijklmnopqrstuvwxyz" do j +:= 1; end while;
    if j eq i then return false; end if;
    if j gt #s then return false; end if;
    while j le #s and s[j] in "0123456789" do j +:= 1; end while;
    return j eq #s + 1;
end function;

// (N, target label) pairs from the classification table: columns 1 and 3 of any
// line whose first two fields are integers and next two are Cremona labels.
enumerated := {};
for line in Split(Read("data/triple_cover_classification.txt"), "\n") do
    fs := [w : w in Split(line, " ") | w ne ""];
    if #fs ne 8 then continue; end if;
    okN, N := IsIntegerString(fs[1]);
    okd, _ := IsIntegerString(fs[2]);
    if not okN or not okd then continue; end if;
    if not IsCremonaLabel(fs[3]) or not IsCremonaLabel(fs[4]) then continue; end if;
    Include(~enumerated, <N, fs[3]>);
end for;
printf "enumerated covers: %o\n", #enumerated;

// (N, label) pairs from the migrated cache filenames map_<N>_<label>.m.
listing := "/tmp/reconcile_map_files.txt";
System("ls data/starmodels/map_*.m > " cat listing cat " 2>/dev/null");
cached := {};
prefix := "data/starmodels/";
for path in Split(Read(listing), "\n") do
    if path eq "" then continue; end if;
    base := path[#prefix + 1 .. #path];
    parts := Split(base[5 .. #base - 2], "_");
    if #parts ne 2 then continue; end if;
    okN, N := IsIntegerString(parts[1]);
    if not okN then continue; end if;
    if not IsCremonaLabel(parts[2]) then continue; end if;   // legacy name
    Include(~cached, <N, parts[2]>);
end for;
printf "cached maps:       %o\n", #cached;

printf "\n=== cached but NOT enumerated (INVESTIGATE, do not delete) ===\n";
orphans := cached diff enumerated;
if #orphans eq 0 then printf "  none\n"; end if;
for t in Sort(Setseq(orphans)) do printf "  X_0(%o)* -> %o\n", t[1], t[2]; end for;

printf "\n=== enumerated but NOT cached (needs construction) ===\n";
missing := enumerated diff cached;
if #missing eq 0 then printf "  none\n"; end if;
for t in Sort(Setseq(missing)) do printf "  X_0(%o)* -> %o\n", t[1], t[2]; end for;

printf "\nreconciliation: %o orphan(s), %o missing\n", #orphans, #missing;
quit;
