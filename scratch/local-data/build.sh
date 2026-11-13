#!/bin/bash
# LocalData.lean = imports + scratch/g15-ram/G15Ram.lean lines 8-718 (verbatim: §0 copies, §1 the
# Props incl. LocalData, §2 local-field lemmas) + verbatim defs from
# scratch/g0-mod-galois/part_galois.lean (resQ, Vb, tate, Intertwines, G7Out, G8Out) + part_local.lean
cd "$(dirname "$0")"
G=../g15-ram/G15Ram.lean
P=../g0-mod-galois/part_galois.lean
{
  sed -n 1,7p $G
  echo "import ZInQKernel.HDecomp.I3Linalg.C2"
  echo "import ZInQKernel.HDecomp.Descent.ProjRep"
  echo
  echo "/-! # local-data: \`LocalData p r\` (scratch/g15-ram) on G8's \`r\`"
  echo
  echo "Assembled by \`scratch/local-data/build.sh\`. Check with"
  echo "\`lake env lean scratch/local-data/LocalData.lean\`. The first part (through \`end Tame\`) is a"
  echo "verbatim copy of \`scratch/g15-ram/G15Ram.lean\` lines 8-718; then verbatim definitions from"
  echo "\`scratch/g0-mod-galois/part_galois.lean\`; then §4 (new). -/"
  sed -n 8,718p $G
  echo
  echo "end G15Ram"
  echo
  echo "/-! ## §3' (local-data). Verbatim copies from scratch/g0-mod-galois/part_galois.lean -/"
  echo
  sed -n 23,40p $P
  sed -n 66,73p $P
  echo
  sed -n 83,88p $P
  sed -n 110,133p $P
  sed -n 142,153p $P
  echo "end G0Galois"
  echo
  echo "end"
  echo
  echo "end G0GaloisSec"
  cat part_local.lean
} > LocalData.lean
