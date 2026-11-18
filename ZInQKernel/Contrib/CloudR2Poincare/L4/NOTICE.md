# Third-party source notice — H-72 L4

AxiomMath/Stacks: https://github.com/AxiomMath/Stacks
Pinned source: c496df0d9beea9deaeabcea8492605f9a0a2313b
License: Apache License 2.0, retained verbatim in LICENSE.Stacks.

Modified/extracted sources:
- DimensionFiniteType.lean: elementary finite-type algebra dimension argument from StacksFrontier/RingTheory/KrullDimension/FiniteTypeNeTop.lean, integrated into an affine-open/compact-scheme bound.
- ProductGeometry.lean: residue-field bijectivity argument from StacksFrontier/AlgebraicGeometry/F6Rank128/FiberResidueField.lean:73–79; the remaining product-section/fibre constructions are proved directly with Mathlib.
- FibreStalk.lean: the localization equivalence, canonical quotient-stalk bridge, and normalized fibre-stalk equivalence from StacksFrontier/AlgebraicGeometry/Morphisms/CohenMacaulay/FibreStalk.lean:93–192,341–358, and flat-stalk specialization from FibreDimensionBaseChange/LocalRing.lean:149–167.

Prominent modification notices are also in the Lean module headers. New declarations are confined to ZInQ.Contrib.CloudR2Poincare.L4; shared upstream dimension and base-change primitives are imported from the single L3-owned vendor copy, not re-vendored here. The source's Cohen–Macaulay/global-dimension/pointwise-flat auxiliary trees are not copied into this lane.

Project source reuse:
KernelGeometry.lean credits the unconditional scheme-theoretic kernel/lift/shear constructions in scratch/av-glue/Kernel.lean at df98652abbeeef78b57f0868f19523a26d811b58. Conditional leaves in that scratch source are not imported or assumed.
