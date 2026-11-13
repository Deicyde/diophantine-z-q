# t28-igusa results log

Leaf: `PkgI1.IgusaClebschSeparation` (T28), copied verbatim with its definitions
(`J2 J4 J6 j10Data J10 sexticAct lyVec`) from scratch/h-decomposition/Leaves.lean lines 423-784
into scratch/t28-igusa/Defs.lean. Compiles (VERIFIED, `lake env lean`, 77 s).

## Plan (route choice)
- (⇒) transformation law: elementary; proof by generators of GL2 (diag, swap, translations),
  cocycle identity for `sexticAct`, and for translations the derivation trick
  (d/dt J(f(x+t)) = (D J)(f(x+t)), D = Σ (i+1) a_{i+1} ∂/∂a_i, D J = 0 by `ring`).
- (⇐) reduction to exact equality of invariants (scaling by a square root of r).
- (⇐) content: see docs/research/t28-igusa.md for the route comparison.
