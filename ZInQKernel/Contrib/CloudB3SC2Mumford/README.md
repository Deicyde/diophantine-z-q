# Mumford group law over a connected locally noetherian base

This contribution proves the current statement
`DictModels.MumfordConn.MumfordGroupLawConn` in
`ZInQKernel/Contrib/OneProof/MumfordGroupLawConnProof.lean`.

The construction first proves the unconditional group law over any locally
noetherian base, then applies the repository's `conn_of_field`. No projectivity
or additional mathematical assumption is introduced.

## Proof

The proved deformation, completion, descent and affine group-law machinery is
ported from [Anthropic's Fermat project](https://github.com/anthropics/fermats-last-theorem)
at `6e837e75355538c7f80bab5b956861e86c4eacc2`.
Its projectivity-dependent algebraization step is replaced by a proved graph
algebraization theorem for proper schemes. The unique affine-local group laws
are glued as scheme morphisms over the base, including nonreduced bases.

## Verification

- All 756 contributed Lean modules were rebuilt from source independently.
- The exact current closing type and the canonical discharge check pass.
- The closing theorem has no remaining assumptions and uses exactly
  `propext`, `Classical.choice`, and `Quot.sound`.
- Current-main coexistence, source policy, provenance and public hygiene pass.
- Existing repository modules and dependency pins are unchanged.

The independent rebuild used a 24 GB Lean heap for modules that exceeded a
smaller 7.5 GB cap. Source compatibility changes and preserved upstream credits
are recorded in the vendor notices and manifest.

This is AI-assisted work. Private evidence bundle available to the maintainer.
No land or fold is performed by this contribution.
