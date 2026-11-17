# Mumford group law over a locally noetherian base

This contribution is being developed for the exact open statement
`ZInQ.Contrib.MumfordRigidity.MumfordGroupLaw`.

**Status: proof development only. No open hypothesis is discharged by this file.**

## Planned mathematical route

The starting sources are the proved deformation and algebraization material in
[Anthropic's Fermat project](https://github.com/anthropics/fermats-last-theorem)
at revision `6e837e75355538c7f80bab5b956861e86c4eacc2`.

The projective-base proof is not sufficient for the requested statement. The
proper, smooth family in the statement need not be projective, including over a
nonreduced base. The intended route therefore replaces projective morphism
algebraization with graph algebraization for proper schemes, using finite-cover
existence, formal closed-immersion recognition, and formal isomorphism recognition.
The remaining deformation, descent, localization, uniqueness, and gluing steps
are then transported to the original objects and hypotheses.

All ported proof sources will retain their applicable licenses and attribution.
Existing repository modules and dependency pins are not changed. New supporting
modules belong in this directory, and the eventual exact closing theorem will
belong in `ZInQKernel/Contrib/OneProof/MumfordGroupLawConnProof.lean`.

## Acceptance checks still required

- Compile the complete supporting import cone from source on the pinned toolchain.
- Prove the exact statement with no additional mathematical assumptions.
- Run the prescribed discharge check against the newest main.
- Check that the closing theorem uses only `propext`, `Classical.choice`, and
  `Quot.sound`, and that no contributed source contains build-time code.
- Independently review the final source, statement, and provenance.

This is an AI-assisted contribution. Private evidence bundle available to the maintainer.
