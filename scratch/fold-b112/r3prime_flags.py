"""fold-b112 fold 5 (r3prime-etale + r3prime-bc, inbox 68): remove the R3' caveat from the flags of the rows whose
height predicate contains R3' (IsAnMetricSq): gaudronRemondSec9LowerAnSS (what bost-gr9 leaves of bostLowerBoundAnSS),
gaudronRemondThm14AnSS, javanpeykarThm111An; record the closing theorems. Statements unchanged; ratings unchanged
(each row keeps a pending/UNVERIFIED marker, so each stays GLUE). Usage: python3 scratch/fold-b112/r3prime_flags.py"""
import csv
K = 'docs/one-proof/kinds.tsv'
rows = list(csv.DictReader(open(K), delimiter='\t'))
cols = list(rows[0].keys())
CLOSED = ("R3' closed by r3prime-etale + r3prime-bc (ZInQ.R3Etale.isHolChart_iff_isSerreChart', "
          "ZInQ.R3BC.isHolChart_iff_isBCSerreChart, isSerreMetricSq_iff: the IsHolChart atlas is the atlas of Serre's "
          "complex space of A_tau = G x_{O_L,tau} C, from T35; fold-b112)")
EDITS = {
    'gaudronRemondSec9LowerAnSS': [
        ("R3' (etale coordinates are holomorphic charts, inside IsAnMetricSq) remains a step, as for gaudronRemondThm14AnSS",
         CLOSED)],
    'gaudronRemondThm14AnSS': [
        ("R3' remains a step, so GLUE as the row it replaces", CLOSED)],
    'javanpeykarThm111An': [
        ("reading risk: R3' (the IsHolChart atlas is the complex structure of A(C)^an) is the one step left inside the "
         "height predicate, the same step as bostLowerBoundAnSS and gaudronRemondThm14AnSS; ",
         "reading risk: " + CLOSED + "; ")],
}
done = set()
for r in rows:
    for old, new in EDITS.get(r['field'], []):
        assert r['flag'].count(old) == 1, (r['field'], old)
        r['flag'] = r['flag'].replace(old, new)
        assert "R3' remains" not in r['flag'] and "R3' (" not in r['flag'], r['field']
        done.add(r['field'])
assert done == set(EDITS), done
with open(K, 'w', newline='') as fh:
    w = csv.DictWriter(fh, fieldnames=cols, delimiter='\t', lineterminator='\n')
    w.writeheader(); w.writerows(rows)
print('R3\' caveat removed from', sorted(done))
