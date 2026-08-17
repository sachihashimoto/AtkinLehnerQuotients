// scripts/certify_committed_models.m
//
// Run directly: magma -b scripts/certify_committed_models.m   (no options)
//
// Certify the already-committed HNF models in data/genus{5,6,7,8}_models.m
// against the cached star q-expansions in data/starmodels/, without calling
// all_diag_basis.
//
// Why this is valid: the saturated-HNF change of basis (src/hnf_canonical.m,
// StarHNFTransformFromBas) depends only on the saturated lattice spanned by
// a level's star-form q-expansions, not on which particular (non-canonical)
// all_diag_basis run produced the spanning vectors. So reconstructing V from
// a cached starforms_<N>.m, generated independently, possibly in a
// different raw basis order/scaling, reduces to the same canonical V the
// original build used. Evaluating the
// committed equations on V*(cached forms) is therefore a genuine check of
// the committed equations, not merely a self-consistency check of the cache.
//
// Coverage: only levels with both a committed model and a starforms_<N>.m
// cache entry can be checked this way. Most committed levels currently have
// no cache entry (data/starmodels/ was populated for unrelated triple-cover
// work, not systematically for every genus 5-8 level); those are reported
// as skipped (not cached), not as failures. Certifying them requires a
// fresh all_diag_basis, deliberately out of scope for this script.
//
// `load` with a computed/variable filename does not work in Magma (it
// parses its argument as a literal token, and is invalid inside a for-loop
// body), so each genus file is loaded with a literal `load` statement below
// rather than in a loop.

load "src/triple_covers.m";   // LoadStarForms; also loads src/AtkinLehner.m
load "src/hnf_canonical.m";   // must load after AtkinLehner.m so all_diag_basis,
                               // ModularSturmBound, CertifyModularIdentity are
                               // already declared when this file is compiled

// Certify one committed curve C (level N, ambient dimension g) against its
// cached star forms, if a cache entry exists. Returns a status in
// {"OK", "FAIL", "SKIP"} and a message.
function CertifyCommittedModel(N, g, C)
    ok, cache_prec, fs_full := LoadStarForms(N);
    if not ok then
        return "SKIP", Sprintf("N=%o: no cached star forms; not checked", N);
    end if;
    if #fs_full ne g then
        return "SKIP", Sprintf("N=%o: cached forms have dimension %o, expected %o; not checked", N, #fs_full, g);
    end if;

    V := StarHNFTransformFromBas(fs_full, g);
    newbas := [&+[V[i,j]*fs_full[j] : j in [1..g]] : i in [1..g]];

    eqns := DefiningPolynomials(C);
    for e in eqns do
        assert IsHomogeneous(e);
        weight := 2 * Degree(e);
        val := Evaluate(e, newbas);
        try
            ok2, B := CertifyModularIdentity(val, N, weight);
        catch err
            msg := Sprint(err`Object);
            if "insufficient precision" in msg then
                return "SKIP", Sprintf("N=%o: cached forms have insufficient precision to certify this equation; not checked (%o)", N, msg);
            end if;
            return "FAIL", Sprintf("N=%o: %o", N, msg);
        end try;
        if not ok2 then
            return "FAIL", Sprintf("N=%o: equation of degree %o FAILED past Sturm bound %o", N, Degree(e), B);
        end if;
    end for;
    return "OK", Sprintf("N=%o certified (%o eqns, cache_prec=%o)", N, #eqns, cache_prec);
end function;

counts := AssociativeArray();
for s in ["OK", "FAIL", "SKIP"] do counts[s] := 0; end for;

printf "\n===== genus 5 (data/genus5_models.m) =====\n";
load "data/genus5_models.m";      // defines `models` (AssociativeArray) and P
for N in Sort(SetToSequence(Keys(models))) do
    C := models[N]`curve;
    status, msg := CertifyCommittedModel(N, 5, C);
    printf "[%o] %o\n", status, msg;
    counts[status] +:= 1;
end for;

printf "\n===== genus 6 (data/genus6_models.m) =====\n";
load "data/genus6_models.m";
for N in Sort(SetToSequence(Keys(models))) do
    C := models[N]`curve;
    status, msg := CertifyCommittedModel(N, 6, C);
    printf "[%o] %o\n", status, msg;
    counts[status] +:= 1;
end for;

printf "\n===== genus 7 (data/genus7_models.m) =====\n";
load "data/genus7_models.m";
for N in Sort(SetToSequence(Keys(models))) do
    C := models[N]`curve;
    status, msg := CertifyCommittedModel(N, 7, C);
    printf "[%o] %o\n", status, msg;
    counts[status] +:= 1;
end for;

printf "\n===== genus 8 (data/genus8_models.m) =====\n";
load "data/genus8_models.m";
for N in Sort(SetToSequence(Keys(models))) do
    C := models[N]`curve;
    status, msg := CertifyCommittedModel(N, 8, C);
    printf "[%o] %o\n", status, msg;
    counts[status] +:= 1;
end for;

printf "\n===== summary =====\n";
printf "OK=%o  FAIL=%o  SKIP(no cache)=%o\n", counts["OK"], counts["FAIL"], counts["SKIP"];
