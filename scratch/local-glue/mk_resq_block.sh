#!/bin/bash
# resq_block.lean: verbatim scratch/g0-assemble/parts/75_modfield.lean l.786 (`numberField_of_fd`)
# and l.895-985 (`actQ`, `actK`, `resQ_comm'`, `resQ_range`), with the renames
# `GaloisCopy.resQ` -> `G0Galois.resQ`, `(L : IF)` -> `(L : IntermediateField ℚ PkgI4.Qbar)`,
# `Qbar` -> `PkgI4.Qbar`, and names prefixed `RQ.` (namespace) to avoid clashes.
cd "$(dirname "$0")"
SRC=../g0-assemble/parts/75_modfield.lean
{
  echo "namespace RQ"
  echo
  sed -n 786p $SRC
  echo
  sed -n 895,985p $SRC
  echo
  echo "end RQ"
} | sed -e 's/GaloisCopy\.resQ/G0Galois.resQ/g' -e 's/(L : IF)/(L : IntermediateField ℚ PkgI4.Qbar)/g' \
      -e 's/\bQbar\b/PkgI4.Qbar/g' -e 's/PkgI4\.PkgI4\./PkgI4./g' > resq_block.lean
