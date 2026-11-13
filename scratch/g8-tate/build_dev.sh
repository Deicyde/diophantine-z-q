#!/bin/bash
# Assemble Dev.lean (development environment for part_onl.lean):
#   scratch/alg-frob-red/AlgFrobRed.lean verbatim (frob-trace's FrobTrace.lean = unram-tate's
#     TateBridge.lean [ModField.lean L1-1036 + UnramTate] + g14-trace's part_bridge.lean +
#     frob-trace's part_frob.lean; mul-rigidity's Rigidity.lean; alg-frob-red's part_red.lean),
#     with three extra imports added after its import block
#   + scratch/g0-mod-galois/part_galois.lean L27-152 verbatim (G0Galois: resQ, Vb, tate, ..., G8Out)
#   + scratch/g8-object/part_split.lean L48-59 verbatim (G8Object.OnL), in namespace G8Object
#   + part_onl.lean (this task).
cd "$(dirname "$0")"
SRC=../alg-frob-red/AlgFrobRed.lean
NIMP=$(grep -c '^import ' $SRC)
{
  sed -n "1,${NIMP}p" $SRC
  echo "import ZInQKernel.HDecomp.I3Linalg.TateBC"
  echo "import ZInQKernel.HDecomp.Descent.ProjRep"
  echo "import ZInQKernel.HDecomp.Conductor.LadicCond"
  echo "section AlgFrobRedCopy"
  sed -n "$((NIMP+1)),\$p" $SRC
  echo "end"   # close the anonymous section left open in the copy
  echo "end AlgFrobRedCopy"
  echo
  echo "/-! Copied verbatim from scratch/g0-mod-galois/part_galois.lean L27-152. -/"
  echo "noncomputable section"
  sed -n '27,152p' ../g0-mod-galois/part_galois.lean
  echo
  echo "end G0Galois"
  echo "end"
  echo
  echo "/-! Copied verbatim from scratch/g8-object/part_split.lean L48-59 (\`G8Object.OnL\`). -/"
  echo "noncomputable section"
  echo "namespace G8Object"
  echo "open PkgI4 (GQ GQp GaloisRep decomp)"
  echo "open LadicCond"
  echo "open G0ModField"
  sed -n '48,59p' ../g8-object/part_split.lean
  echo "end G8Object"
  echo "end"
  echo
  cat part_onl.lean
  echo
  cat part_g7d.lean
} > Dev.lean
