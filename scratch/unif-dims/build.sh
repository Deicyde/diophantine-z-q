#!/bin/bash
# Builds UnifDims.lean (imports ZInQKernel.HDecomp.LeafPush2.T only):
#  1. base/Kernel_metrization2.lean: verbatim copy of scratch/metrization2/Kernel.lean
#     (origin/wip/metrization2 6a687213), without its #print axioms lines;
#  2. scratch/product-unif/ProductUnif.lean lines 25-100 (namespace header + §0 `Points`:
#     ptsProj ... prodUnif_clauses, product-height's verbatim copies), verbatim;
#  3. ProductUnif.lean lines 2236-2279 (section SAlg header + `ProductUnifDims`, verbatim) and
#     lines 2561-2591 (`ProductUnifDimsEq`, `productUnifDims_of`, end SAlg), verbatim;
#  4. Torsion.lean (this task, Mathlib only) without import / #print;
#  5. part_main.lean (this task);
#  6. ProductUnif.lean lines 1842-1904 (metrization's pullGerm, ProductHodgeLattice), verbatim;
#  5b. DetProd.lean (this task) without import / #print, after part_main;
#  7. part_phl.lean, part_final.lean (this task);
#  8. infra-stalks' StalkPullback.lean, CotangentProduct.lean (verbatim copies in base/), part_pc.lean,
#     part_pcfinal.lean, part_final2.lean (this task).
# Prerequisite: lake build ZInQKernel.HDecomp.LeafPush2.T
cd "$(dirname "$0")"
PU=../product-unif/ProductUnif.lean
{ echo 'import ZInQKernel.HDecomp.LeafPush2.T'
  echo 'import ZInQKernel.HDecomp.Faltings.HodgeLattice'
  echo 'import Mathlib'
  grep -v '^#print axioms\|^import' base/Kernel_metrization2.lean
  echo
  sed -n 25,100p $PU
  echo
  echo "end ZInQ.ProductHeight"
  echo
  echo "namespace ZInQ.ProductUnif"
  echo
  sed -n 2236,2279p $PU
  sed -n 2561,2591p $PU
  echo
  echo "end ZInQ.ProductUnif"
  echo
  grep -v '^import\|^#print axioms' Torsion.lean
  echo
  cat part_main.lean
  echo
  grep -v '^import\|^#print axioms' DetProd.lean
  echo
  # metrization's pullGerm and ProductHodgeLattice, verbatim (ProductUnif.lean lines 1842-1904)
  sed -n 1842,1904p $PU
  echo "end ZInQ.Metrization"
  echo
  cat part_phl.lean
  cat part_final.lean
  echo
  grep -v '^import' base/StalkPullback_infra.lean
  echo
  grep -v '^import' base/CotangentProduct_infra.lean
  echo
  grep -v '^#print axioms' part_pc.lean
  cat part_pcfinal.lean
  cat part_final2.lean
} > UnifDims.lean
