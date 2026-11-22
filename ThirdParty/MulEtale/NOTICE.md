# Reused proof sources

This directory contains selected proof sources from
[AxiomMath/Stacks](https://github.com/AxiomMath/Stacks), pinned to commit
`c496df0d9beea9deaeabcea8492605f9a0a2313b`. The upstream license is reproduced in
[`LICENSE`](LICENSE); existing source notices and author information are retained.

- `Direct/Original/`: the tangent definitions, functoriality, geometric-field-change
  and identity-tangent modules, together with their citation-attribute modules.
  Mathematical declarations retain their original namespaces. Module import
  paths are adapted to this repository.
- `Direct/Shared/`: selected pullback/base-change/fibre-stalk and stalk-congruence
  sources from the same pinned snapshot, with isolated vendor declaration
  namespaces. These use the same citation-attribute modules as `Direct/Original/`
  instead of registering a second copy of those metadata attributes.
- `StacksVendor/LFPFromComposite.lean`: selected proofs from
  `StacksFrontier/AlgebraicGeometry/Morphisms/FinitePresentation/Basic.lean`,
  lines 43–82, deriving finite presentation of a morphism from its composite
  and finite type of the following structural morphism.
- `Direct/Global/PushoutCotangent.lean`: selected proofs from
  `StacksFrontier/AlgebraicGeometry/FiberCotangentIdentification/Kaehler.lean`,
  lines 45–86, giving the quotient-pushout and Kähler base-change dictionary.

The adapted source files identify their original locations and hashes where
applicable. Lean 4.35 API/proof compatibility repairs and the direct tangent,
local-cotangent, field-descent, scheme-fibre detection and final H-101 assembly
are part of this contribution. No new Lake dependency on the upstream Stacks
repository is introduced.
