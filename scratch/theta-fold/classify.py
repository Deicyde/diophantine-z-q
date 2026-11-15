"""Classify cmp_hashes_out.txt's changed constants (yu-prune). Writes classify_out.txt."""
import re
d = 'scratch/theta-fold/'
lines = open(d + 'cmp_hashes_out.txt').read().split('## changed')[1].split('\n')[1:]
ch = [l.split() for l in lines if l.strip()]
bundles = ['TextbookLeaves'] + [f'OpenTextbookLeaves{n}' for n in (2, 3, 4, 6, 7, 8, 9, 10, 11)]
consumers = """comIntOrQuadOrder_of comIntOrQuadOrder_of_leaves fibreComTrivialFull_of_leaves fibreComTrivialFull_of_leaves'
fibreComTrivialFull_of_leaves'' fibreSimple_of_leaves fibreSimple_of_pieces fibreSimple_of_pieces' fibreSimple_of_pieces''
endEqOFibre_of kernelFieldExists_of_descent kernelFieldExists_of_final kernelFieldExists_of_final' kernelFieldExists_of_five
kernelFieldExists_of_kerUnitOpen kernelFieldExists_of_kerUnitOpen' kernelFieldExists_of_mulIsogeny kernelFieldExists_of_rigidity
kernelFieldExists_of_semilinear kernelFieldExists_of_split'' kernelFieldExists_of_twist gluePieces_of_open4
linkedTateLocal_of_leaves3 qmEndRank_of_leaves3 qmEndRank_of qmEndRank_of_leaves""".split()
cats = {}
for kind, n, m in ch:
    last = n.split('.')[-1]
    parts = n.split('.')
    if any(f'HSyn.{b}.' in n for b in bundles): c = 'bundle structure / generated auxiliaries'
    elif re.match(r'(textbookLeaves\d*_of_open\d*|openTextbookLeaves10_of_OpenTextbookLeaves11)$', last): c = 'conversion'
    elif re.match(r'sixContactMin_of_open\d+$', last) or n == 'ZInQ.OneProof.frozenTarget': c = 'sixContactMin_of_open* / frozenTarget'
    elif last in consumers: c = 'edited consumer'
    elif n.startswith('HDec.QMLattice.'): c = 'QMLattice (moved def; aux proofs)'
    else: c = 'other'
    cats.setdefault(c, []).append(f'{kind} {n} ({m.split(".")[-1]})')
out = []
for c, v in cats.items():
    out.append(f'## {c}: {len(v)}')
    out += ['  ' + x for x in v]
open(d + 'classify_out.txt', 'w').write('\n'.join(out) + '\n')
print('\n'.join(x for x in out if x.startswith('##')))
open(d + 'used-consts-names.txt', 'w').write('\n'.join(x.split()[1] for x in cats.get('other', []) + cats.get('QMLattice (moved def; aux proofs)', [])) + '\n')
