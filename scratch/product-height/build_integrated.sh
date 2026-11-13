#!/bin/bash
# Builds LeavesIntegrated.lean = scratch/h-decomposition/Leaves.lean + §1-§6 of ProductHeight.lean
# (without the §0 copy and without `open PkgI3 (AbVar)`), plus an `example` closing Leaves.lean's
# `ZInQ.H5Neron.ProductModelHeight` (the type of `GluePieces.productModelHeight`).
set -e
cd "$(dirname "$0")/../.."
OUT=scratch/product-height/LeavesIntegrated.lean
cp scratch/h-decomposition/Leaves.lean $OUT
python3 - <<'PY'
src = open('scratch/product-height/ProductHeight.lean').read()
start = src.index('namespace ZInQ.ProductHeight')
end_ = src.index('end ZInQ.ProductHeight') + len('end ZInQ.ProductHeight')
body = src[start:end_]
# drop the §0 copy and `copy_iff`
a = body.index('/-! ## §0.')
b = body.index('open H5Neron')
body = body[:a] + body[b:]
body = body.replace('open PkgI3 (AbVar)\n', '')
tail = '''

/-- Integration check: Leaves.lean's glue piece 5 from the two AN3-free glue Props. -/
example (hS : ZInQ.ProductHeight.ProductUnifSplits)
    (hA : ZInQ.ProductHeight.ProductMetrizationOfProductUnif) : ZInQ.H5Neron.ProductModelHeight :=
  ZInQ.ProductHeight.productModelHeight_of_splits hS hA

#print axioms ZInQ.ProductHeight.productModelHeight_of_splits
#print axioms ZInQ.ProductHeight.productModelHeight_of_geo
'''
with open('scratch/product-height/LeavesIntegrated.lean', 'a') as f:
    f.write('\n' + body + tail)
PY
echo "wrote $OUT"
