"""Generate LeavesIntegrated.lean (not committed; run from the worktree root):
scratch/h-decomposition/Leaves.lean + product-height §1-§6 + ProductUnif §1-§4 (product-unif's
build_integrated.sh recipe) + metrization2's kernel file (as in build_combined.py) + this task's
parts, all without `open PkgI3 (AbVar)` (in Leaves.lean `AbVar` is `ZInQ.DefFaltings.AbVar`),
+ a theorem closing Leaves.lean's `GluePieces.productModelHeight` from `AnalyticUniformizationOfDim`
and `TangentDimAtOrigin` (see the comment on T35 below).  Check: lake env lean scratch/unif-dims/LeavesIntegrated.lean (~10 min)."""
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
# In Leaves.lean, leaf-push2's T35 (`ZInQ.LeafPush2.UniformizationExists`) is stated over
# `PkgI3.AbVar` with its own copy of the model layer, while def-faltings' models use
# `ZInQ.DefFaltings.AbVar` (two distinct structures there; one in the kernel). So metrization2's
# transport of T35 (its section "complex points of a group model are complex points of A_L") and
# every theorem of this task taking T35 are dropped here; the check is from
# `AnalyticUniformizationOfDim` instead (T35 ⇒ AnalyticUniformizationOfDim is checked in the
# kernel world: Combined.lean, UnifDims.lean, metrization2's Kernel.lean).
i_tr = next(i for i, l in enumerate(kl) if l.startswith('/-! ## metrization2: complex points of a group model'))
i_tr2 = next(i for i, l in enumerate(kl) if l.startswith('/-! ## metrization2: toward `ProductMapLocalStructure`'))
kernel = '\n'.join(kl[1:i_jdd]) + '\nend ZInQ.Metrization\n\n' + \
    '\n'.join(l for l in kl[i_m2:i_tr] + kl[i_tr2:] if not l.startswith('#print'))
def dropT35(text):
    parts = text.split('\n/-- ')
    out = [parts[0]]
    for c in parts[1:]:
        if 'LeafPush2.UniformizationExists' in c:
            k = c.find('\n\n')
            out.append(None if k < 0 else c[k:])
        else:
            out.append('/-- ' + c)
    return '\n'.join(x for x in out if x is not None)
mine = '\n\n'.join([body(d + 'Torsion.lean'), cut(d + 'part_main.lean'), body(d + 'DetProd.lean'),
    cut(d + 'part_phl.lean'), cut(d + 'part_final.lean'),
    body(d + 'base/StalkPullback_infra.lean'), body(d + 'base/CotangentProduct_infra.lean'),
    body(d + 'part_pc.lean'), cut(d + 'part_pcfinal.lean'), cut(d + 'part_final2.lean')])
mine = dropT35(mine)
tail = '''

namespace ZInQ.UnifDims

open ZInQ.DefFaltings.HodgeLattice

/-- Integration check: Leaves.lean's glue piece 5 (`GluePieces.productModelHeight`) from
metrization's `AnalyticUniformizationOfDim` (which follows from T35 in the kernel world) and
hodge-lattice's `TangentDimAtOrigin`. -/
theorem productModelHeight_of_leaves (hU : ZInQ.Metrization.AnalyticUniformizationOfDim)
    (hT : TangentDimAtOrigin) : ZInQ.H5Neron.ProductModelHeight :=
  ZInQ.ProductUnif.productModelHeight_of_local (hodgeLatticeTheorem_of_tangent hT dimBaseChange)
    (productUnifDims_of_unifOfDim hU) ZInQ.Metrization2.productLocalStructure
    (productHodgeLattice_of productCotangent detLatticeProd
      (cotangentRank_of_tangentDim (tangentDim_of_abVar hT dimBaseChange)) hU)

end ZInQ.UnifDims

#print axioms ZInQ.UnifDims.productUnifDims_of_unifOfDim
#print axioms ZInQ.UnifDims.detLatticeProd
#print axioms ZInQ.UnifDims.productCotangent
#print axioms ZInQ.UnifDims.productHodgeLattice_of
#print axioms ZInQ.UnifDims.productModelHeight_of_leaves
'''
allbody = ('\n\n' + ph + '\n\n' + pu + '\n\n' + kernel + '\n\n' + mine).replace('open PkgI3 (AbVar)\n', '')
open(d + 'LeavesIntegrated.lean', 'w').write(leaves + allbody + tail)
