# Openness of the identity component of a smooth group scheme

Target: `CToPrinted.SGA3_VIB_3_10`.

**Status: proof development only. This file discharges no hypothesis.**

The intended proof retains the exact original telescope: an arbitrary scheme
`S`, a group object `G` over `S`, and smoothness of its structure morphism. No
Noetherian, field-base, quasi-compactness, or quasi-separatedness hypothesis is
added to the target.

## Source reuse

The proved relative connected-component-section openness theorem, Stacks 055R,
is present in AxiomMath/Stacks at revision
`c496df0d9beea9deaeabcea8492605f9a0a2313b`, in
`StacksFrontier/AlgebraicGeometry/MoreMorphisms/GenericFibre/ShrinkingConsequences.lean`.
Its import cone proves the required generalization-stability and
geometric-irreducibility-after-shrinking results.

Affine restrictions around a point of the identity section supply the
finite-presentation hypotheses locally from smoothness. The resulting connected
fibre-component neighbourhood maps into the original fibre component. The
existing translation proof on `wip/gt-sga3` then propagates neighbourhoods along
the group law to establish openness of the full identity-component set.
The geometric-connectedness proof in pull request #25 is also a reuse candidate.

Copied sources will retain their source revisions, licenses and attribution.
All new support belongs in this directory; the eventual closing theorem belongs
in a new file under `ZInQKernel/Contrib/OneProof/`. Existing modules and dependency
pins are not changed.

Compilation, exact type and axiom checks, the prescribed discharge output, and
independent final-source review remain to be completed.

This is an AI-assisted contribution. Private evidence bundle available to the maintainer.
