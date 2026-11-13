#!/bin/bash
# Assemble X1OnModel.lean = header + body of scratch/x1-belyi/X1Belyi.lean (lines 2-365, copied,
# imports the same kernel module) + part_onmodel.lean (this task) + part_final.lean.
cd "$(dirname "$0")"
{ echo "import ZInQKernel.HDecomp.ModCurves.Glue"
  echo "/-! # g0-x1belyi: \`X1BelyiOnModel\` (Split.lean missing piece 3) from \`BelyiX1\`; see"
  echo "\`docs/research/g0-x1belyi.md\`. Lines up to \`end X1Belyi\` are copied verbatim from"
  echo "\`scratch/x1-belyi/X1Belyi.lean\` (compiled there). -/"
  sed -n 2,365p ../x1-belyi/X1Belyi.lean; cat part_onmodel.lean part_final.lean; } > X1OnModel.lean
