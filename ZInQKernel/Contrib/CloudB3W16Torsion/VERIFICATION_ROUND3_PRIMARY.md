# Round-3 primary math/API verification

All seven primary-retained modules newly reached by provider round3 compile on
Lean4.35/Mathlib56a00585. The fresh seven-module axiom scratch returns0,4.89s,
7188216KiB peak RSS, printing seven actual solution axiom lists, all exactly
`[propext, Classical.choice, Quot.sound]`.

Repairs preserve the source statements and mathematical objects:

- Curve-model assembly: current term/type transparency behavior, removal of
  absent namespace opens, explicit scalar-tower intermediate type.
- Reflective monoidal sheafification: one-based TFAE positions.
- Affine section base change and line-bundle gluing: activate the existing root
  scoped section notation, preserve the separately declared local helper scope,
  and remove tactics after their goals are already solved.
- Overlap quotient base change: use the existing kernel proof directly, without
  an unnecessary simplifier step.
- Prime-ideal construction: current MvPolynomial representation and ENat cardinality.
- Finite-presentation flatness: current transparency behavior, retaining the
  original residue-field tensor argument.

No new hypothesis, admission, axiom, syntax or notation is added. This is a
source-port checkpoint only: the full degree/cardinality provider and exact
Mumford leaf remain unclaimed until their own kernel/discharge checks succeed.
The source provenance, full upstream notices and licenses remain unchanged.
