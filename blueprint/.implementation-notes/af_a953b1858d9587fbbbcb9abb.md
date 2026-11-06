# Implementation note: Point routines

- Lean names: `ZInQ.Compiler.IR.JPt` (three `FElt`), routines `pConstP0`, `pConstO`, `pNeg`,
  `pAdd` (branching), `pDbl`, `pMul` (halving loop), Hoare lemmas stating the output
  represents `jaddB`, `jdblB`, `jmul` of the decision layer.
- Proof of `pMul`: loop invariant through `BigStep.whileLt` with measure the counter
  register; the decision layer's `jmulNat` is defined by the same recursion, so the
  invariant is `Repr` of the three loop variables.
- Mathlib: as in the field routines.
- Upstream reuse: none.
- FINITE COMPUTATION: no. Difficulty: medium (≈250 lines; long straight-line code).
