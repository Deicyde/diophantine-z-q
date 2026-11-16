# Round-2 primary math/API repairs

The frozen provider run at `96c864727` compiled 143 additional modules and exposed
48 newly reachable failures: 41 metadata/scope modules transferred to disjoint
A14/B14/C13 owners, and these seven primary math/API modules.

All seven now compile on Lean4.35/Mathlib56a00585. A fresh scratch importing those
seven modules prints seven actual kernel axiom lists, all exactly
`[propext, Classical.choice, Quot.sound]`: exit0,5.01s,7195912KiB peak RSS.
The raw output is `round2-primary7-axioms.log` beside this document.

- CurveModelConstruction: restore the current term-transparency setting and the
  type-only transparency compatibility setting. The original construction and
  all of its proofs compile unchanged; its existing char-zero support theorem
  remains conditional exactly as before, not imposed on Mumford's theorem.
- isCurveOver_of_ringEquiv_functionField: restore current transparency behavior.
- Ordered-affine-cover cohomology equivalence: remove a reflexivity tactic after
  the preceding rewrite already closed the goal.
- Cartier graph kernel: compare both kernel memberships to the same map-equals-zero
  proposition directly, avoiding simplification of a hypothesis to True.
- IntermediateField wrapper: current transparency behavior matches its already
  verified source theorem.
- Finite-generation flat descent: open the source's existing scoped FreeCover
  instances and disambiguate the ordinary identity function.
- Closed-fibre prime-ideal argument: current transparency avoids speculative
  MvPolynomial scalar-instance loops; use ENat cardinality and the current
  zero-coefficient representation.

No theorem telescope or hypothesis is strengthened, and no geometric provider
is assumed. The full degree/cardinality provider and exact Mumford leaf are still
pending compilation of the remaining Picard/cube cone. These seven native/axiom
checks are a porting checkpoint, not a Mumford discharge claim.
