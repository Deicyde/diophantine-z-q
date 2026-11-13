#!/usr/bin/env python3
"""infra-hodge: check that the Props proved and the blocks copied into the assembled checks appear
verbatim in their owner files. Run from the repository root:
python3 scratch/infra-hodge/verbatim_check.py"""
import re, os
ok = True
def blk(src, name):
    m = re.search(r"/-- [^\n]*\n(?:[^\n]*\n)*?def " + name + r"\b.*?(?=\n\n)", src, re.S)
    m2 = re.search(r"def " + name + r"\b.*?(?=\n\n)", src, re.S)
    return m2.group(0) if m2 else None
def noprint(t): return '\n'.join(l for l in t.split('\n') if not l.startswith('#print'))
def check(target, items):
    global ok
    if not os.path.exists(target):
        print(target, 'missing'); ok = False; return
    t = open(target).read()
    for label, b in items:
        r = b is not None and b in t
        ok &= r
        print(f"{target}: {label}: {r}")
s = 'scratch/infra-stalks/'
met = open('scratch/metrization/Metrization.lean').read().split('\n', 1)[1]
sp = open(s+'StalkPullback.lean').read(); sp = sp[sp.index('universe u'):]
cp = open(s+'CotangentProduct.lean').read(); cp = cp[cp.index('namespace IsLocalRing'):]
ef = open('ZInQKernel/Contrib/HodgeBC2/ExtFrac.lean').read().split('\n', 1)[1]
items = [
  ('def ProductHodgeLattice verbatim from scratch/metrization/part_prodsplit.lean',
   blk(open('scratch/metrization/part_prodsplit.lean').read(), 'ProductHodgeLattice')),
  ('def ProductHodgeLattice verbatim from scratch/infra-stalks/ProductLocalStructure.lean',
   blk(open(s+'ProductLocalStructure.lean').read(), 'ProductHodgeLattice')),
  ('Metrization.lean body', met),
  ('infra-stalks StalkPullback body', sp), ('infra-stalks CotangentProduct body', cp),
  ('infra-stalks cot_pullback part', noprint(open(s+'cot_pullback.lean.part').read())),
  ('infra-stalks local_structure part', noprint(open(s+'local_structure.lean.part').read())),
  ('infra-stalks pls_proof part', noprint(open(s+'pls_proof.lean.part').read())),
  ('hodge-bc2 ExtFrac.lean body', ef)]
check('scratch/infra-hodge/ProductHodgeLattice.lean', items)
if os.path.exists('scratch/infra-hodge/ProductSplit.lean'):
    ph = open('scratch/product-height/ProductHeight.lean').read()
    check('scratch/infra-hodge/ProductSplit.lean', [
      ('def ProductMetrizationOfProductUnif verbatim from scratch/g0-assemble2/parts/a25_productheight.lean',
       blk(open('scratch/g0-assemble2/parts/a25_productheight.lean').read(), 'ProductMetrizationOfProductUnif')),
      ('def ProductMetrizationOfProductUnif verbatim from scratch/product-height/ProductHeight.lean',
       blk(ph, 'ProductMetrizationOfProductUnif'))])
print('ALL OK' if ok else 'FAILURES')
