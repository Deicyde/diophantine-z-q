"""assemble-port: parts/z95b_homunify.lean = hom-unify's single leaf `HomUnify.HomLatticeCorr` (scratch/hom-unify/parts/
H20_bundle.lean L184-224: namespace, opens, the def with its docstring, `homLinearLift_of_corr`, verbatim), then
`t11a_riemannEnd_of_corr` (the text of ZInQKernel/Contrib/HomUnify/Corr.lean L109-112, for this file's copies) and a new
three-line `t11aRiemannHom_of_corr` (period-glue's `T11aRiemannHom` is the two clauses at `g = h`, `σ = id`). Run from
scratch/assemble-port."""
H = open('../hom-unify/parts/H20_bundle.lean').read().split('\n')
assert H[183] == 'namespace HomUnify' and H[222].startswith('theorem homLinearLift_of_corr'), (H[183], H[222])
blk = '\n'.join(H[183:223])
K = open('../../ZInQKernel/Contrib/HomUnify/Corr.lean').read().split('\n')
assert K[108].startswith('theorem t11a_riemannEnd_of_corr'), K[108]
t11a = '\n'.join(K[107:112]) if K[107].startswith('/--') else '\n'.join(K[108:112])
new = '''
/-- **`T11aRiemannHom` (period-glue's T11(a) in `Hom` form) from `HomLatticeCorr` (proved):** the realization clause at
`h = g` and the lifting clause at `K = ℂ`, `σ = id`. -/
theorem t11aRiemannHom_of_corr (h : HomLatticeCorr) : HSyn.G0Split.FibreQM.PeriodGlue.T11aRiemannHom :=
  fun A A' g Λ Λ' Φ Φ' hA hA' hU hU' =>
    ⟨fun M hM => h.2 A A' g g Λ Λ' Φ Φ' hA hA' hU hU' M hM,
     fun f => h.1 ℂ A A' (RingHom.id ℂ) g g Λ Λ' Φ Φ' hA hA' hU hU' f⟩
'''
txt = ('/-! ## assemble-port: hom-unify\'s leaf `HomLatticeCorr` (mk/mk_z95b.py) -/\n\nsection HomUnifySec\n\n' + blk + '\n\n' + t11a +
       '\n' + new + '\nend HomUnify\n\nend HomUnifySec\n\n#print axioms HomUnify.t11a_riemannEnd_of_corr\n#print axioms HomUnify.t11aRiemannHom_of_corr\n')
open('parts/z95b_homunify.lean', 'w').write(txt)
print('ok')
