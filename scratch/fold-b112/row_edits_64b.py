"""fold-b112: inbox 64b, the bergerSurveyF source column (the reviewer). The phrase the inbox names ('Berger survey IV.5.1,
cited print') is not in the row on this base (VERIFIED by grep); the row's leading survey citation is replaced by the
lead's text and the rest (survey sections used, Inventiones numbering, Lean pointers) is kept. Rating unchanged.
Usage: python3 scratch/fold-b112/row_edits_64b.py"""
import csv
K = 'docs/one-proof/kinds.tsv'
rows = list(csv.DictReader(open(K), delimiter='\t'))
cols = list(rows[0].keys())
OLD = ('Berger, An introduction to the theory of p-adic representations (2004), arXiv:math/0210184v1, IV.5.1 and IV.5.3, '
       'with II.2.3, II.3.1, II.3.3, II.5.2, I.2.3; ')
NEW = ("Brinon-Conrad, CMI notes (June 24, 2009 version, the manuscript's citation), Thm 9.3.5, p. 148 (Berger's theorem "
       "stated as background: de Rham iff potentially semistable, i.e. semistable over some finite K'/K); same statement "
       "in Berger's survey (arXiv math/0210184v1, IV.5.1; not in the manuscript's bibliography); the Lean form uses the "
       "survey's IV.5.3, II.2.3, II.3.1, II.3.3, II.5.2, I.2.3; ")
n = 0
for r in rows:
    if r['field'] == 'bergerSurveyF':
        assert r['source'].startswith(OLD), r['source'][:120]
        r['source'] = NEW + r['source'][len(OLD):]
        n += 1
assert n == 1
with open(K, 'w', newline='') as fh:
    w = csv.DictWriter(fh, fieldnames=cols, delimiter='\t', lineterminator='\n')
    w.writeheader(); w.writerows(rows)
print('bergerSurveyF source edited')
