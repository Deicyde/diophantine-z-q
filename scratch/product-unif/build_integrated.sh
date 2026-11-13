#!/bin/bash
# Builds LeavesIntegrated.lean = scratch/h-decomposition/Leaves.lean
#   + §1-§6 of scratch/product-height/ProductHeight.lean (as in product-height's build_integrated.sh)
#   + §1-§4 of scratch/product-unif/ProductUnif.lean (without its §0 copy)
#   (all without `open PkgI3 (AbVar)`: in Leaves.lean `AbVar` is `ZInQ.DefFaltings.AbVar`)
#   + a theorem closing Leaves.lean's `ZInQ.H5Neron.ProductModelHeight` (the type of
#     `GluePieces.productModelHeight`) from `HodgeLatticeTheorem`, `ProductUnifDims`,
#     `ProductLocalStructure`, `ProductHodgeLattice`.
# Check with: lake env lean scratch/product-unif/LeavesIntegrated.lean  (about 9 min). Not committed.
set -e
cd "$(dirname "$0")/../.."
OUT=scratch/product-unif/LeavesIntegrated.lean
cp scratch/h-decomposition/Leaves.lean $OUT
python3 - <<'PY'
src = open('scratch/product-height/ProductHeight.lean').read()
start = src.index('namespace ZInQ.ProductHeight')
end_ = src.index('end ZInQ.ProductHeight') + len('end ZInQ.ProductHeight')
body = src[start:end_]
a = body.index('/-! ## §0.')
b = body.index('open H5Neron')
body = body[:a] + body[b:]
pu = open('scratch/product-unif/ProductUnif.lean').read()
mine = pu[pu.index('/-! ## §1. Elementary analysis'):pu.index('#print axioms')]
body = (body + '\n\n' + mine).replace('open PkgI3 (AbVar)\n', '')
tail = '''

namespace ZInQ.ProductUnif

/-- Integration check: Leaves.lean's glue piece 5 (`ProductModelHeight`) from `HodgeLatticeTheorem`
and the glue Props `ProductUnifDims`, `ProductLocalStructure`, `ProductHodgeLattice`. -/
theorem productModelHeight_of_local (hH : DefFaltings.HodgeLatticeTheorem)
    (hD : ProductUnifDims) (hLS : ZInQ.Metrization.ProductLocalStructure)
    (hL : ZInQ.Metrization.ProductHodgeLattice) : ZInQ.H5Neron.ProductModelHeight :=
  ZInQ.ProductHeight.productModelHeight_of_splits productUnifSplits
    (productMetrizationOfProductUnif_of_local hH hD hLS hL)

end ZInQ.ProductUnif

#print axioms ZInQ.ProductUnif.productUnifSplits
#print axioms ZInQ.ProductUnif.productModelHeight_of_local
'''
with open('scratch/product-unif/LeavesIntegrated.lean', 'a') as f:
    f.write('\n' + body + tail)
PY
echo "wrote $OUT"
