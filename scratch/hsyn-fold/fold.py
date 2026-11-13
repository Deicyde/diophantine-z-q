# One-shot edit of scratch/h-decomposition/Leaves.lean (task hsyn-fold).
import sys
R = lambda p: open(p).read().split('\n')
L = open('scratch/h-decomposition/Leaves.lean').read()
A6 = R('scratch/glue-a6-alg/A6.lean'); C10 = R('scratch/glue-c10/C10.lean')
TR = R('scratch/glue-c10/Trace.lean'); LOC = R('scratch/glue-d1-local/Local.lean')
PU = R('scratch/leaf-push/Push.lean'); PD = R('scratch/leaf-push/PushDR.lean')
seg = lambda xs, a, b: '\n'.join(xs[a-1:b])
def rep1(s, old, new):
    assert s.count(old) == 1, (old[:80], s.count(old)); return s.replace(old, new)
# 1. GlueA6Alg.Alg before PkgI2Sec
assert A6[46].startswith('namespace GlueA6Alg.Alg') and A6[520].startswith('end GlueA6Alg.Alg')
L = rep1(L, '\nsection PkgI2Sec\n', '\nsection GlueA6AlgSec\n/-! ### Copied from `scratch/glue-a6-alg/A6.lean` lines 47-521 (compiled there; hsyn-fold). -/\n\n'
         + seg(A6, 47, 521) + '\n\nend GlueA6AlgSec\n\nsection PkgI2Sec\n')
# 2. quatUnipotentTrivial after its definition
assert A6[948].startswith('open GlueA6Alg.Alg in') and A6[1008].startswith('  exact E_inj')
L = rep1(L, '    ∀ x, x ^ (3 ^ k) = 1 → S x = x\n\nsection A6\n',
         '    ∀ x, x ^ (3 ^ k) = 1 → S x = x\n\n-- hsyn-fold: proved in scratch/glue-a6-alg/A6.lean (copied).\n'
         + seg(A6, 949, 1009) + '\n\nsection A6\n')
# 3. rename and add the hypothesis-free A6
L = rep1(L, 'theorem goodReduction_of_QM_rational3 (hNOS', 'theorem goodReduction_of_QM_rational3_of_alg (hNOS')
assert A6[1080].startswith('/-- **Glue A6') and A6[1122].startswith('end A6')
new = seg(A6, 1081, 1122).replace('Alg.exists_valuationSubring_comap_eq', 'GlueA6Alg.Alg.exists_valuationSubring_comap_eq')
L = rep1(L, '    rw [Nat.cast_pow]; exact h3\'.pow _\n\nend A6\n',
         '    rw [Nat.cast_pow]; exact h3\'.pow _\n\n-- hsyn-fold: from scratch/glue-a6-alg/A6.lean.\n' + new + '\n')
# 4. trace_indep_of_ell in PkgI3
assert TR[336].startswith('namespace PkgI3') and TR[374].startswith('end PkgI3')
tr = seg(TR, 337, 342) + '\n' + seg(TR, 349, 375)
L = rep1(L, '\nend PkgI3\n\nend\nend PkgI3Sec\n',
         '\nend PkgI3\n\n-- hsyn-fold: C10 trace comparison, from scratch/glue-c10/Trace.lean (pkg-I3 copy dropped).\n'
         + tr + '\n\nend\nend PkgI3Sec\n')
# 5. T23 in PkgI4
i = [k for k, x in enumerate(PD) if x.startswith('/-! ## leaf-push: T23')][0]
j = [k for k, x in enumerate(PD) if x.startswith('end Fontaine')][0]
L = rep1(L, '  omega\n\nend PkgI4\n\nend\n\n\nend PkgI4Sec\n',
         '  omega\n\n-- hsyn-fold: copied from scratch/leaf-push/PushDR.lean.\n' + '\n'.join(PD[i:j+1])
         + '\n\nend PkgI4\n\nend\n\n\nend PkgI4Sec\n')
# 6. D1 local after CondBreaksSec
assert LOC[399].startswith('end GlueConductor') and LOC[634].startswith('end GlueD1Local')
L = rep1(L, '\nend CondBreaksSec\n',
         '\nend CondBreaksSec\n\nsection D1LocalSec\n/-! ### Copied from `scratch/glue-d1-local/Local.lean` lines 401-635 (its copy of Breaks.lean dropped; hsyn-fold). -/\n'
         + seg(LOC, 401, 635) + '\n\nend D1LocalSec\n')
# 7-8. C10 and LeafPush before HSyn
assert C10[8].startswith('open NumberField') and C10[463].startswith('end GlueC10')
i35 = [k for k, x in enumerate(PU) if x.startswith('section AV')][0]
i106 = [k for k, x in enumerate(PU) if x.startswith('end AV')][0]
assert PU[25].startswith('universe u') and PU[270].startswith('end LeafPush')
pu = '\n'.join(PU[25:i35]) + '\n-- hsyn-fold: pkg-I2 copy (Push.lean §1) replaced by PkgI2\'s definitions.\nopen PkgI2\n' + '\n'.join(PU[i106+1:271])
L = rep1(L, '\nend RepoNumericsSec\n\nnoncomputable section\n\nnamespace HSyn\n',
         '\nend RepoNumericsSec\n\nsection GlueC10Sec\n/-! ### Copied from `scratch/glue-c10/C10.lean` (compiled there; hsyn-fold). -/\n'
         + seg(C10, 9, 464) + '\n\nend GlueC10Sec\n\nsection LeafPushSec\n/-! ### Copied from `scratch/leaf-push/Push.lean` (compiled there; hsyn-fold), over PkgI2. -/\n'
         + pu + '\n\nend LeafPushSec\n\nnoncomputable section\n\nnamespace HSyn\n')
open('scratch/h-decomposition/Leaves.lean', 'w').write(L)
print('ok')
