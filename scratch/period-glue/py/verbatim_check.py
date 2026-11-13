"""period-glue: verbatim checks of the copied material.
(1) PGBase.lean = FibreQM.lean[1:20634] + part_fqm + period-map parts; PGLight.lean = PMLight.lean.
(2) The MulRigidity body in BCU.lean = mul-rigidity's Rigidity.lean lines 21-182.
(3) The AutOExt body in QMTwist.lean = mobius-glue's MobiusGlue.lean lines 663-814.
(4) The six period-map statements targeted here occur verbatim in PGBase / PGLight.
Run from the repository root: ~/pyenv/bin/python -I scratch/period-glue/py/verbatim_check.py"""
import os, sys
R = os.getcwd()
def rd(p): return open(os.path.join(R, p)).read()
D = 'scratch/period-glue'
ok = True
fq = rd('scratch/fibre-qm-period/FibreQM.lean').splitlines(keepends=True)
base = ''.join(fq[:20634]) + ''.join(rd(f) for f in ['scratch/fibre-qm-period/part_fqm.lean'] +
    ['scratch/period-map/%s.lean' % x for x in ['part_light','part_theta','part_siegel','part_order','part_heavy']])
if os.path.exists(os.path.join(R, D, 'PGBase.lean')):
    r = rd(D + '/PGBase.lean') == base; ok &= r; print('PGBase verbatim:', r)
if os.path.exists(os.path.join(R, D, 'PGLight.lean')):
    r = rd(D + '/PGLight.lean') == rd('scratch/period-map/PMLight.lean'); ok &= r; print('PGLight verbatim:', r)
rig = ''.join(rd('scratch/mul-rigidity/Rigidity.lean').splitlines(keepends=True)[20:182])
r = rig in rd(D + '/BCU.lean'); ok &= r; print('rigidity copy verbatim:', r)
aut = ''.join(rd('scratch/mobius-glue/MobiusGlue.lean').splitlines(keepends=True)[662:814])
r = aut in rd(D + '/QMTwist.lean'); ok &= r; print('AutOExt copy verbatim:', r)
heavy = rd('scratch/period-map/part_heavy.lean'); light = rd('scratch/period-map/part_light.lean')
order = rd('scratch/period-map/part_order.lean')
def stmt(src, name):
    i = src.index('def ' + name); j = src.index('\n\n', i); return src[i:j]
for name, src in [('BaseChangeClassUnique', heavy), ('PiTwistC', heavy), ('QMTwistLattice', heavy),
                  ('S8Nonzero', light), ('SphereFactorAffine', light), ('S8WeightExact', order),
                  ('ValenceBoundGammaStar', light), ('CMDescends', heavy)]:
    s = stmt(src, name)
    r = s in base and (name not in ('S8Nonzero','SphereFactorAffine','S8WeightExact','ValenceBoundGammaStar') or s in rd('scratch/period-map/PMLight.lean'))
    ok &= r; print('statement', name, 'present verbatim in the bases:', r)
mg = rd('scratch/mobius-glue/MobiusGlue.lean')
i = mg.index('def AutOInnerFinite'); j = mg.index('\n\n', i)
orig = mg[i:j].replace('(O ≃+* O)', '(LeafQM.O ≃+* LeafQM.O)')
print('AutOInnerFinite (mobius-glue) for comparison:\n' + mg[i:j])
sys.exit(0 if ok else 1)
