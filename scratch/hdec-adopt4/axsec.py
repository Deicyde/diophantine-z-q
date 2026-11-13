# Print the section of `#print axioms` lines added to scripts/print_axioms.lean by hdec-adopt4.
import sys
sys.path.insert(0, 'scratch/hdec-adopt2')
from decls import decls
D = 'ZInQKernel/HDecomp/'
full = {}
for m in ['LeafPush2/Bridge', 'LeafPush2/R18', 'LeafPush2/R22', 'LeafPush2/R3', 'LeafPush2/T', 'LeafPush2/UnifBridge', 'Analytic/Torus',
          'Analytic/QMLattice', 'Analytic/Hom', 'Analytic/Uniformization', 'QM/Polar']:
    for n, p, i in decls(D + m + '.lean'): full[n] = m
# the drafts' own `#print axioms` targets (leaf-push2's stableFaltingsHeight is already listed as
# ZInQ.DefFaltings.stableFaltingsHeight), then bp-analytic's main glue theorems (it has none).
lp2 = [l.split()[2] for l in open('scratch/leaf-push2/LeafPush2.lean') if l.startswith('#print')]
lp2 = [n for n in lp2 if n != 'ZInQ.LeafPush2.stableFaltingsHeight']
pol = [l.split()[2] for l in open('scratch/rv-qm-polar/QMPolar.lean') if l.startswith('#print')]
tor = ['BPAnalytic.' + s for s in '''isCoveringMap_proj isLocalHomeomorph_proj contMDiff_proj
 contMDiff_of_comp_proj ker_torusExp contMDiff_torusExp det_im_ne_zero_of_mem_siegelSpace
 riemannTheta_add_period thetaConst_eq_riemannTheta torusDiffeo_apply exists_realLinear_lift
 exists_complexLinear_lift covolume_periodLattice covolume_periodLattice_of_mem'''.split()]
tor += ['BPAnalytic.QM.' + s for s in '''det_im_Omega_ne_zero map_periodLattice_Omega
 Omega_transpose Omega_mem_siegelSpace riemannTheta_Omega_add_period'''.split()]
tor += ['BPAnalytic.Uniformization.' + s for s in '''IsUniformization.continuous_comparison
 IsUniformization.exists_realLinear evalAt_comp IsUniformization.continuous_endo
 IsUniformization.exists_realLinear_endo IsUniformization.exists_complexLinear_endo
 IsUniformization.exists_complexLinear eq_of_proj_eq IsUniformization.exists_equiv
 IsUniformization.dim_eq analyticRep_unique analyticRep_id analyticRep_comp analyticRep_mul
 torsion_iff'''.split()]
br = ['ZInQ.LeafPush2.' + s for s in '''isSiegel_iff isPeriodMatrix_periodLattice
 isPeriodMatrix_of_map isSiegel_Omega isPeriodMatrix_qmLattice thetaConst_eq
 cEvalAt_eq_evalAt isUniformization_of_bp exists_isUniformization_of_leaf'''.split()]
names = lp2 + br + pol + tor
for n in names: assert n in full, n
print('\n-- hdec-adopt4: leaf-push2 (`HDecomp.LeafPush2`), rv-qm-polar (`HDecomp.QM.Polar`) and')
print('-- bp-analytic (`HDecomp.Analytic`); the bridges `HDecomp.LeafPush2.Bridge`,')
print('-- `HDecomp.LeafPush2.UnifBridge` (new).')
for n in names: print('#print axioms ' + n)
