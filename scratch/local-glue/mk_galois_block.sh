#!/bin/bash
# galois_block.lean: verbatim scratch/g0-mod-galois/part_galois.lean lines 40-58.
cd "$(dirname "$0")"
{ echo; echo "/-! ## §5' (local-glue). Verbatim copy from scratch/g0-mod-galois/part_galois.lean lines 40-58 -/"
  echo; echo "noncomputable section"; echo; echo "namespace G0Galois"; echo
  sed -n 40,58p ../g0-mod-galois/part_galois.lean
  echo "end G0Galois"; echo; echo "end"; echo; } > galois_block.lean
