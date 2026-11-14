#!/bin/bash
# parts/b08_productunif.lean: scratch/product-unif/WithProductHeight.lean lines 980-1577 (product-unif §1-§3:
# elementary analysis, points of an affine open, `ZInQ.ProductUnif.productUnifSplits`), verbatim except that
# the lines `open PkgI3 (AbVar)` are deleted, as g0-assemble2 did for product-height (part a25). Its lines
# 11-977 are product-height's ProductHeight.lean, which part a25 already holds.
cd "$(dirname "$0")"
{ echo "/-! ## leaf-fold2: product-unif §1-§3 (scratch/product-unif/WithProductHeight.lean lines 980-1577; see mk_b08.sh) -/"; sed -n 980,1577p ../product-unif/WithProductHeight.lean | grep -v "^open PkgI3 (AbVar)$"; } > parts/b08_productunif.lean
