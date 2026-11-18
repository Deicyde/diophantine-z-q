"""ht-merge: kinds.tsv row counts for the joint hand fold (H rows only, i.e. without the frozenTarget row hPC),
ht-abvar's spec versus ht-merge's.  Rule as autofold: a new row is LEAF only if kind == published and its flag is not
a must-be-GLUE flag (render_open.must_be_glue); every consequence row is GLUE."""
import csv, json, os, sys
sys.path.insert(0, 'scripts/one_proof')
import render_open

rows = list(csv.DictReader(open('docs/one-proof/kinds.tsv'), delimiter='\t'))
H = [r for r in rows if r['bundle'] != 'frozenTarget']

def strict(lf):
    return 'LEAF' if lf.get('kind', 'published') == 'published' and not render_open.must_be_glue(lf.get('flag', '')) else 'GLUE'

def count(rs):
    n = len(rs); L = sum(r == 'LEAF' for r in rs); return f'{L}/{n - L} on {n}'

removed = {'picRepresentableAbVar', 'kleimanPicZeroProper954SiteQ', 'hodgeTateDecompOr'}
base = [r['strict'] for r in H]
print('current top (H rows):', count(base))
for spec in sys.argv[1:]:
    s = json.load(open(spec))
    kept = [r['strict'] for r in H if r['field'] not in removed]
    new = [strict(lf) for lf in s['new_leaves']]
    print(spec, '->', count(kept + new), ' new rows:', [(lf['name'], strict(lf)) for lf in s['new_leaves']])
