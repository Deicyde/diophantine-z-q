"""conrad-b3: kinds.tsv row counts (H rows, without frozenTarget's hPC) for the joint hand fold (c8 + Poincare + ht-merge),
before (main) and after.  Rule as autofold / ht-merge's count.py: a new row is LEAF only if kind == published and its
flag is not a must-be-GLUE flag (render_open.must_be_glue); every consequence row is GLUE.
Usage: python3 scratch/conrad-b3/count.py KINDS.tsv"""
import csv, json, sys
sys.path.insert(0, 'scripts/one_proof')
import render_open

kinds = sys.argv[1]
rows = list(csv.DictReader(open(kinds), delimiter='\t'))
H = [r for r in rows if r['bundle'] != 'frozenTarget']

def strict(lf):
    return 'LEAF' if lf.get('kind', 'published') == 'published' and not render_open.must_be_glue(lf.get('flag', '')) else 'GLUE'

def count(rs):
    n = len(rs); L = sum(r == 'LEAF' for r in rs); return f'{L}/{n - L} on {n}'

removed = {'picRepresentableAbVar', 'kleimanPicZeroProper954SiteQ', 'hodgeTateDecompOr'}
kept = [r['strict'] for r in H if r['field'] not in removed]
assert len(kept) == len(H) - 3, 'a removed row is missing from kinds.tsv'
htm = json.load(open('scratch/ht-merge/autofold.json'))['new_leaves']
cb = json.load(open('scratch/conrad-b3/autofold.json'))['new_leaves']
conradB = [lf for lf in cb if lf['name'] == 'conradAppB']
joint_htm = htm
joint_cb = [lf for lf in htm if lf['name'] not in ('conradAppBQp', 'tateTwistInvariantsInertia')] + conradB
def show(label, new):
    print(f'{label:60s} {count(kept + [strict(lf) for lf in new])}   new rows: {[(lf["name"], strict(lf)) for lf in new]}')
print('kinds file:', kinds)
print(f'{"before: current top (H rows)":60s} {count([r["strict"] for r in H])}')
show('joint fold, ht-merge spec (c8-conrad3 C8 leaves)', joint_htm)
show('joint fold, conrad-b3 (ConradAppB merged)', joint_cb)
show('joint fold, ht-merge spec + PR #86 poincareComplement_proof', [lf for lf in joint_htm if lf['name'] != 'poincareComplement'])
show('joint fold, conrad-b3 + PR #86 poincareComplement_proof', [lf for lf in joint_cb if lf['name'] != 'poincareComplement'])
