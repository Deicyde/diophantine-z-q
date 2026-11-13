"""Generate LeavesIntegrated.lean (not committed; run from the worktree root):
scratch/h-decomposition/Leaves.lean + product-height §1-§6 + ProductUnif §1-§4 (product-unif's
build_integrated.sh recipe) + metrization2's kernel file (as in build_combined.py) + this task's
parts, all without `open PkgI3 (AbVar)` (in Leaves.lean `AbVar` is `ZInQ.DefFaltings.AbVar`),
+ a theorem closing Leaves.lean's `GluePieces.productModelHeight` from `TextbookLeaves.t35` and
`TangentDimAtOrigin`.  Check: lake env lean scratch/unif-dims/LeavesIntegrated.lean (~10 min)."""
d = 'scratch/unif-dims/'
def body(path):
    return '\n'.join(l for l in open(path).read().splitlines()
                     if not l.startswith('#print') and not l.startswith('import '))
def cut(path):
    return open(path).read().split('#print axioms')[0]
leaves = open('scratch/h-decomposition/Leaves.lean').read()
src = open('scratch/product-height/ProductHeight.lean').read()
start = src.index('namespace ZInQ.ProductHeight')
end_ = src.index('end ZInQ.ProductHeight') + len('end ZInQ.ProductHeight')
ph = src[start:end_]
a = ph.index('/-! ## §0.'); b = ph.index('open H5Neron')
ph = ph[:a] + ph[b:]
pu = open('scratch/product-unif/ProductUnif.lean').read()
pu = pu[pu.index('/-! ## §1. Elementary analysis'):pu.index('#print axioms')]
kl = open(d + 'base/Kernel_metrization2.lean').read().splitlines()
i_jdd = next(i for i, l in enumerate(kl) if l.startswith('/-- **Glue (the Jacobian descends'))
i_m2 = next(i for i, l in enumerate(kl) if l.startswith('/-! ## metrization2: `JacDetNondegenerate` from'))
kernel = '\n'.join(kl[1:i_jdd]) + '\nend ZInQ.Metrization\n\n' + \
    '\n'.join(l for l in kl[i_m2:] if not l.startswith('#print'))
mine = '\n\n'.join([body(d + 'Torsion.lean'), cut(d + 'part_main.lean'), body(d + 'DetProd.lean'),
    cut(d + 'part_phl.lean'), cut(d + 'part_final.lean'), cut(d + 'part_combined.lean'),
    body(d + 'base/StalkPullback_infra.lean'), body(d + 'base/CotangentProduct_infra.lean'),
    body(d + 'part_pc.lean'), cut(d + 'part_pcfinal.lean'), cut(d + 'part_final2.lean'),
    cut(d + 'part_combined2.lean')])
tail = '''

namespace ZInQ.UnifDims

/-- Integration check: Leaves.lean's glue piece 5 (`GluePieces.productModelHeight`) from the
textbook leaf `TextbookLeaves.t35` and hodge-lattice's `TangentDimAtOrigin`. -/
theorem productModelHeight_of_leaves (t : HSyn.TextbookLeaves)
    (hT : ZInQ.DefFaltings.HodgeLattice.TangentDimAtOrigin) : ZInQ.H5Neron.ProductModelHeight :=
  productModelHeight_of_tangentDim t.t35 hT

end ZInQ.UnifDims

#print axioms ZInQ.UnifDims.productUnifDims_of_uniformizationExists
#print axioms ZInQ.UnifDims.detLatticeProd
#print axioms ZInQ.UnifDims.productCotangent
#print axioms ZInQ.UnifDims.productHodgeLattice_of_tangentDim
#print axioms ZInQ.UnifDims.productModelHeight_of_leaves
'''
allbody = ('\n\n' + ph + '\n\n' + pu + '\n\n' + kernel + '\n\n' + mine).replace('open PkgI3 (AbVar)\n', '')
open(d + 'LeavesIntegrated.lean', 'w').write(leaves + allbody + tail)
