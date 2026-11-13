#!/bin/bash
# Assembles TwistDescent.lean: kf-glue's KfGlue.lean verbatim (one import line added for the
# Mathlib-only module ZInQKernel.Contrib.TwistDescent.GaloisDescent) + the new parts.
set -e
cd "$(dirname "$0")/../.."
S=scratch/kf-glue/KfGlue.lean
O=scratch/twist-descent/TwistDescent.lean
N=$(grep -n '^import ' $S | tail -1 | cut -d: -f1)
{
head -n $N $S
echo "import ZInQKernel.Contrib.TwistDescent.GaloisDescent"
tail -n +$((N+1)) $S
echo
echo "/-! ################################################################################"
echo "  twist-descent (new). Everything above is scratch/kf-glue/KfGlue.lean verbatim. -/"
echo
cat scratch/twist-descent/PartXC.lean
echo
cat scratch/twist-descent/PartHFD.lean
echo
cat scratch/twist-descent/PartMain.lean
echo
cat scratch/twist-descent/PartFinal.lean
} > $O
wc -l $O
