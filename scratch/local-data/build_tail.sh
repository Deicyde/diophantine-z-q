#!/bin/bash
# Tail.lean = scratch/g0-mod-newform/NewForm.lean (verbatim, extra imports appended after its own)
# + G0Galois.G11Out and G15Ram §1-§3 (verbatim from scratch/g15-ram/G15Ram.lean, as g15-ram's
# build_tail.sh) + the part_galois copies and §4 of LocalData.lean + tail_part.lean.
# Run ./build.sh first (LocalData.lean is the source of the part_galois block).
cd "$(dirname "$0")"
G=../g15-ram/G15Ram.lean
{
  sed -n '1,7p' ../g0-mod-newform/NewForm.lean
  echo "import ZInQKernel.HDecomp.Conductor.Breaks"
  echo "import ZInQKernel.HDecomp.Textbook.Different"
  echo "import ZInQKernel.HDecomp.Descent.Constants"
  echo "import ZInQKernel.Multiplication.Certificate.Constants"
  echo "import ZInQKernel.HDecomp.Descent.ProjRep"
  echo "import ZInQKernel.HDecomp.Descent.B2Glue"
  echo "import ZInQKernel.HDecomp.Descent.Chi"
  sed -n '8,$p' ../g0-mod-newform/NewForm.lean
  echo
  echo "noncomputable section"
  echo
  sed -n '/^namespace G0Galois/,/^end G0Galois/p' $G
  echo
  sed -n '/^\/-! ## §1. The smaller named Props/,/^end G15Ram/p' $G
  echo
  echo "end"
  echo
  sed -n "/^\/-! ## §3' (local-data)/,/^end G0GaloisSec/p" LocalData.lean
  grep -v '^#print axioms' part_local.lean
  cat tail_part.lean
} > Tail.lean
