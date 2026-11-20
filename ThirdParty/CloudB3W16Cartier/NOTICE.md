# H98 Cartier proof source notice

Selected mathematical proofs are adapted from AxiomMath/Stacks,
https://github.com/AxiomMath/Stacks, immutable revision
`c496df0d9beea9deaeabcea8492605f9a0a2313b`, under Apache-2.0.
The complete upstream license is reproduced in LICENSE. Upstream source
notices, credits, documentation, and references are retained in the selected
sources. SOURCE_MANIFEST.json and EXTRACTED_SOURCES.json record original
paths, source SHA256 hashes, and extracted line ranges.

Changes for this contribution:
- New module paths lie under ZInQKernel.Contrib.CloudB3W16Cartier.
- Vendor mathematical declarations are isolated under
  ZInQ.Contrib.CloudB3W16Cartier.Vendor to avoid collisions with existing ports.
- Citation metadata attributes and their registrars are not copied.
- Differential BaseChange retains only the base-change comparison (01V0),
  omitting the unneeded direct-sum/triangle comparison (01V1).
- CharZeroRegularity retains the 00TX finite-free-differentials induction;
  conormal injectivity and residue-field formal smoothness use Mathlib, and
  the regular-local smoothness edge reuses the existing Jacobian-Challenge
  contribution on main.
- The spectrum-of-field module equivalence is reused from the existing
  Jacobian contribution; no quasi-coherence or finite-type sheaf cone is
  duplicated.
- Stalk/base-change foundations reuse the folded MulEtale contribution.

All compatibility repairs are mathematical proof/API changes only.
