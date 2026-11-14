#!/usr/bin/env python3
"""leaf-fold5: the leaf and glue statements of part e10 have their sources' text (vert-witness VertMain.lean.part,
model-glue ModelGlue*.lean.part), and HeckeVertWitness in leaf-fold4's chain (part c80) has hecke-rest's text as
copied by vert-witness. Run from scratch/leaf-fold5."""
import sys
sys.path.insert(0, 'py')
from chunks import chunks, text
def decls(t):
    return {c['name']: text(c) for c in chunks(t) if c['kind'] == 'decl' and c['name']}
src = ''.join(open('../' + f).read() + '\n' for f in ['vert-witness/VertMain.lean.part'] +
              ['model-glue/ModelGlue%s.lean.part' % s for s in ['', '2', '3', '4', '5', '6']])
S = decls(src); E = decls(open('parts/e10_vertmodel.lean').read())
names = ['ShimuraGoodReduction', 'ShimuraSmoothModel', 'IsShimuraModel', 'CMObjectsExist', 'CoordFibres',
         'SmoothFibreReduced', 'ModelCoordinate', 'ModelComparison', 'ModelCoordinateResidue', 'CurveBijIso',
         'heckeVertWitness_of_leaves', 'heckeVertWitness_of_curveBijIso']
ok = True
for n in names:
    same = n in S and n in E and S[n] == E[n]
    ok &= same
    print(n, 'IDENTICAL' if same else 'DIFFERENT')
V = decls(open('../vert-witness/VertWitness.lean').read()); C = decls(open('../leaf-fold4/partsF/c80_propts.lean').read())
for n in ['HeckeVertWitness', 'VertUnramWitness', 'NormalizationModel']:
    same = V.get(n) == C.get(n)
    ok &= same
    print(n, '(vert-witness prefix vs leaf-fold4 c80)', 'IDENTICAL' if same else 'DIFFERENT')
print('ALL OK' if ok else 'MISMATCH')
