# Vendored Tau Ceti code: notice

This file is written by this repository. Tau Ceti has no `NOTICE` file of its own (none in
`~/tc-oct16`, `~/tc-nov01` or the current main, checked 2026-11-13), so Apache License 2.0
section 4(d) adds no notice text. `LICENSE` in this directory is a byte-for-byte copy of Tau Ceti's
`LICENSE` (Apache License, Version 2.0; SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`, the same at both source
commits below).

## Source

- Repository: TauCetiProject/TauCeti (https://github.com/TauCetiProject/TauCeti).
- Authors: The Tau Ceti contributors (the copyright line of every Tau Ceti file). Some file
  headers name individual authors as well; those headers are kept verbatim.
- Commit `5a01f5fe3621126cccf9ba22e700493cbc7b7156` (2026-10-17, the last Tau Ceti commit on Lean
  v4.35.0, Mathlib `ccbef15e`): 1129 modules (the 1118 of the tc-port task and 11 more vendored by
  the diff-bridge task).
- Commit `97a5b23586f9c42610765c701daedc7522a93c26` (2026-11-02, Lean v4.36.0-rc1): the 44
  modules of the Kronecker–Weber import closure that do not exist at `5a01f5fe`, and the
  declarations copied into the 36 files of `Backport/` (kw-new task).

## Where the code is

The vendored modules are in `ZInQKernel/Contrib/TauCeti/` (module prefix
`ZInQKernel.Contrib.TauCeti.`). Declaration names and namespaces are unchanged. Every file copied
from Tau Ceti keeps its Tau Ceti copyright header verbatim. Below that header it carries one
provenance line naming the source commit and the original module:

    -- Vendored from Tau Ceti (https://github.com/TauCetiProject/TauCeti, commit <sha12>, module TauCeti.X), Apache-2.0.

The headers say "Released under Apache 2.0 license as described in the file LICENSE". For these
copies, that file is `ThirdParty/TauCeti/LICENSE`.

## License

Apache License, Version 2.0; see `LICENSE` in this directory. The modifications listed below are
distributed under the same license.

## Modifications in this repository

Mechanical change in every copied file: `import TauCeti.X` (also with `public`, `meta` or `all`)
is rewritten to `import ZInQKernel.Contrib.TauCeti.X`, and the provenance line is added. All
1173 files carrying a provenance line were regenerated from the named commit and compared byte for
byte (`scratch/tc-port2/regen_diff.py`, output `scratch/tc-port2/regen_diff.txt`). 1146 of them
are exactly the mechanical copy. The other 27 were edited further, to compile against this
project's Mathlib (`56a00585`, older than the Mathlib of either source commit) or to use the
`Backport/` helpers:

- `GroupTheory/GroupAction/Norm.lean` (nov01; 5 lines added, 32 removed: five `groupNorm*`
  declarations taken from oct16 `GroupCohomology.Cocycle` instead)
- `GroupTheory/SpecificGroups/Cyclic/PowMonoidHom.lean` (nov01; 2 added)
- `NumberTheory/ClassFieldTheory/ClassFields/KroneckerWeber.lean` (nov01; 1 added)
- `NumberTheory/ClassFieldTheory/ClassFields/RaySubgroup.lean` (nov01; 1 added)
- `NumberTheory/ClassFieldTheory/Formation/InvariantKernel.lean` (oct16; 1 changed: `.isPGroup` → `.isPGroup'`)
- `NumberTheory/ClassFieldTheory/Global/AdmissibleModulus/Basic.lean` (nov01; 2 added)
- `NumberTheory/ClassFieldTheory/Global/AdmissibleModulus/Ramification.lean` (nov01; 1 added)
- `NumberTheory/ClassFieldTheory/Global/AdmissibleModulus/Reciprocity.lean` (nov01; 2 added)
- `NumberTheory/ClassFieldTheory/Global/ClassFormation.lean` (nov01; 4 added, 1 removed)
- `NumberTheory/ClassFieldTheory/Global/CorestrictionLocalization.lean` (nov01; 1 added)
- `NumberTheory/ClassFieldTheory/Global/Kummer/Index.lean` (nov01; 4 added, 1 removed)
- `NumberTheory/ClassFieldTheory/Global/LocalArtin/Compatibility.lean` (nov01; 2 added)
- `NumberTheory/ClassFieldTheory/Global/LocalArtin/Frobenius.lean` (nov01; 2 added)
- `NumberTheory/ClassFieldTheory/Global/Reciprocity.lean` (nov01; 2 added)
- `NumberTheory/ClassFieldTheory/GlobalExistence/NormLimitation.lean` (nov01; 2 added)
- `NumberTheory/NumberField/InfinitePlace/Completion/Real.lean` (nov01; 3 added, 7 removed)
- `RepresentationTheory/Cyclic/Norm.lean` (nov01; 2 added)
- `RepresentationTheory/Homological/ContCohomology/Coinduced/Discrete.lean` (oct16; 3 changed:
  explicit `G A` in three `Is*Apply` instances)
- `RepresentationTheory/Homological/ContCohomology/Corestriction/Mackey/Pullback.lean` (nov01; 2 added)
- `RepresentationTheory/Homological/GroupCohomology/PrimeIndex.lean` (oct16; 2 changed: `.isPGroup'`)
- `RepresentationTheory/Homological/TateCohomology/TrivialityCriterion.lean` (oct16; 1 changed: `.isPGroup'`)
- `RingTheory/Polynomial/Cyclotomic/PrimePow.lean` (nov01; 2 added)
- `Topology/Algebra/Group/Profinite/Generation.lean` (oct16; 1 added: a `rfl`)
- `Topology/Algebra/Group/Profinite/Sylow/Basic.lean` (oct16; 1 changed: `.isPGroup'`)
- `Topology/Algebra/Group/Profinite/Sylow/Containment.lean` (oct16; 1 added: import of
  `MathlibBackport/Sylow.lean`)
- `Topology/Algebra/Group/Profinite/Sylow/Existence.lean` (oct16; 1 changed: `.isPGroup'`)
- `Topology/Algebra/Star/Completion.lean` (nov01; 4 added, 1 removed: explicit continuity proof)

The "added" lines of the nov01 files are mostly `import`s of `Backport/` helpers. Comparing a
file with its source module at the named commit shows every edit. The per-change reasons are in
`docs/research/tc-port.md` (oct16 files) and `docs/research/kw-new.md` (nov01 files).

Files that are not copies of one Tau Ceti module:

- `Backport/**` (36 files): declarations added to a Tau Ceti module between `5a01f5fe` and
  `97a5b235`, copied verbatim from `97a5b235` (three of them are whole-module nov01 replacement
  copies of `Global.PrescribedInvariant`, `Global.Kummer.Norm` and `Global.Kummer.AuxiliaryPlaces`).
  Each header names the source module and commit.
- `Backport/Mathlib/Polynomial.lean`: `Polynomial.X_pow_sub_X_ne_zero`, a Mathlib lemma newer than
  this project's pin, with a proof written in this repository (its header carries the Tau Ceti
  copyright line; the proof is not Tau Ceti's).
- `MathlibBackport/Sylow.lean`: `Sylow.maximal_isPGroup`, a Mathlib field newer than this
  project's pin, derived here as a theorem (written in this repository).
- `Notice.lean`: attribution docstring, no declarations.

No statement of a copied declaration was changed except where a Backport replacement copy
substitutes the nov01 statement for the oct16 one (listed in `docs/research/kw-new.md`). No
`sorry`, `axiom`, `native_decide`, `implemented_by` or `extern` was added; every vendored constant
depends only on `propext`, `Classical.choice` and `Quot.sound` (audits in `scratch/tc-port/` and
`scratch/kw-new/`).

Note for the integrator: unlike `ThirdParty/GreenTao/`, the 27 modified files do not yet carry a
one-line "changed in this repository" comment (Apache License 2.0, section 4(b)); this list is the
notice. If the files are edited before they are pinned, adding that line to each is recommended.
