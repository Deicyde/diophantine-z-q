#!/bin/bash
# Assemble Tail.lean = extra imports + verbatim copy of scratch/g0-mod-newform/NewForm.lean
# (without its import lines) + G0Galois.G11Out + G15Ram.lean §1-§3 + tail_part.lean.
cd "$(dirname "$0")"
{
  sed -n '1,7p' ../g0-mod-newform/NewForm.lean
  echo "import ZInQKernel.HDecomp.Conductor.Breaks"
  echo "import ZInQKernel.HDecomp.Textbook.Different"
  echo "import ZInQKernel.HDecomp.Descent.Constants"
  echo "import ZInQKernel.Multiplication.Certificate.Constants"
  sed -n '8,$p' ../g0-mod-newform/NewForm.lean
  echo
  echo "noncomputable section"
  echo
  sed -n '/^namespace G0Galois/,/^end G0Galois/p' G15Ram.lean
  echo
  sed -n '/^\/-! ## §1. The smaller named Props/,/^end G15Ram/p' G15Ram.lean
  echo
  echo "end"
  cat tail_part.lean
} > Tail.lean
