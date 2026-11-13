#!/bin/bash
# Builds PC.lean: imports; infra-stalks' StalkPullback.lean and CotangentProduct.lean (verbatim copies
# in base/, origin/wip/infra-stalks 3cbf276a, without their `import Mathlib`); part_pullgerm.lean
# (metrization's pullGerm, verbatim: ProductUnif.lean lines 1842-1877); part_pc.lean, part_pcfinal.lean (this task).
cd "$(dirname "$0")"
{ echo 'import ZInQKernel.HDecomp.Faltings.HodgeLattice'
  echo 'import Mathlib'
  echo
  grep -v '^import' base/StalkPullback_infra.lean
  echo
  grep -v '^import' base/CotangentProduct_infra.lean
  echo
  cat part_pullgerm.lean
  echo
  cat part_pc.lean
  cat part_pcfinal.lean
} > PC.lean
