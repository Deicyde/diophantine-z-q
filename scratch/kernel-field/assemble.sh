#!/bin/bash
# Assembles KernelField.lean from verbatim copies (scratch files cannot import each other).
set -e
cd "$(dirname "$0")/../.."
O=scratch/kernel-field/KernelField.lean
{
cat <<'H'
import Mathlib
import ZInQKernel.HDecomp.Objects
import ZInQKernel.HDecomp.B3Unram.B3b
import ZInQKernel.HDecomp.Repo.TorsionFree
import ZInQKernel.HDecomp.Repo.Numerics
import ZInQKernel.HDecomp.Descent.B3Assembly
import ZInQKernel.HDecomp.QM.Leaves
import ZInQKernel.HDecomp.Descent.ProjRep
import ZInQKernel.HDecomp.Conductor.LadicCond
import ZInQKernel.HDecomp.Descent.WP3
import ZInQKernel.HDecomp.I3Linalg.C2
import ZInQKernel.HDecomp.ModCurves.Defs
import ZInQKernel.HDecomp.Assembly
import ZInQKernel.HDecomp.B3Unram.T32a
import ZInQKernel.Hypotheses.JHeight
import ZInQKernel.HDecomp.Repo.TorsionFree
import ZInQKernel.Multiplication.Certificate.ConstantsProperties
import ZInQKernel.Progressions.Final.Instance
import ZInQKernel.Size.Constants.T
import ZInQKernel.HDecomp.Textbook.SkolemNoether
H
echo
echo "/-! # Part 1. scratch/morph-descend/Descend.lean lines 3-401 (verbatim) -/"
echo "section PartDescend"
sed -n 3,401p scratch/morph-descend/Descend.lean | grep -v "^#print axioms"
echo "end PartDescend"
echo
echo "/-! # Part 2. scratch/inertia-homs/InertiaHoms.lean lines 7-2089 (verbatim; G4.lean + inertia-homs) -/"
echo "section PartInertia"
sed -n 7,2089p scratch/inertia-homs/InertiaHoms.lean | grep -v "^#print axioms"
echo "end PartInertia"
echo
echo "/-! # Part 3. scratch/morph-descend/G4Closed.lean lines 1867-1897 (verbatim) -/"
echo "section PartClosed"
sed -n 1867,1897p scratch/morph-descend/G4Closed.lean | grep -v "^#print axioms"
echo "end PartClosed"
echo
echo "/-! # Part 4. scratch/g0-dim/Dim.lean lines 107-305 (verbatim, namespace G0Dim) -/"
echo "section PartDim"
echo "open Order TensorProduct"
sed -n 107,305p scratch/g0-dim/Dim.lean | grep -v "^#print axioms"
echo "end PartDim"
echo
echo "/-! # Part 5. scratch/g0-mod-field/ModField.lean lines 17-end (verbatim) -/"
echo "section PartModField"
sed -n '17,$p' scratch/g0-mod-field/ModField.lean | grep -v '^#print'
echo "end PartModField"
echo
cat scratch/kernel-field/New.lean
} > $O
wc -l $O
