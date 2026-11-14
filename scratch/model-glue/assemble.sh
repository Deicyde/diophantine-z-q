#!/bin/sh
# Assemble ModelGlue.lean: scratch/vert-witness/VertWitness.lean (verbatim, whole file) + ModelGlue.lean.part.
cd "$(dirname "$0")"
cat ../vert-witness/VertWitness.lean ModelGlue.lean.part > ModelGlue.lean
# ModelGlue2.lean: extra import of the proved Möbius curve facts, then the same + step 2.
{ echo "import ZInQKernel.Contrib.Mobius.Main"; cat ../vert-witness/VertWitness.lean ModelGlue.lean.part ModelGlue2.lean.part; } > ModelGlue2.lean
# ModelGlue3.lean: ModelGlue2.lean + step 3 (generic fibre, Jacobson density).
cat ModelGlue2.lean ModelGlue3.lean.part > ModelGlue3.lean
# ModelGlue4.lean: ModelGlue3.lean + step 4 (comparison morphism, ModelIntegral).
cat ModelGlue3.lean ModelGlue4.lean.part > ModelGlue4.lean
# ModelGlue5.lean: ModelGlue4.lean + step 5 (ModelFunctionField from CurveBijIso).
cat ModelGlue4.lean ModelGlue5.lean.part > ModelGlue5.lean
