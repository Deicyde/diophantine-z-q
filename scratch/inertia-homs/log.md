# inertia-homs results log

## Statements
- Target: `G4WeilRes.InertiaFixesHoms` (scratch/g4-weilres/G4.lean L1318).

## Findings
- F1 (VERIFIED by reading the definition; mathematical argument): `InertiaFixesHoms` as stated
  quantifies over ALL morphisms `φ : A_{e₁} → B_{e₂}` in `Over (Spec ℚ̄)`, not only homomorphisms.
  It is false for non-homomorphisms: a constant morphism with value a point `b ∈ B(ℚ̄)` not fixed
  by inertia (e.g. `E` with good reduction at `p`, `b = (√p, y)`; or any `p`-torsion point, since
  `E[p]` is ramified at `p` by the Weil pairing) is not fixed by conjugation. Not refutable in
  Lean (no nonzero `AbVar` can be constructed), but the input is mathematically false; its only
  consumer `conjAction_inertia` applies it to homomorphisms only. Corrected form: add `IsMonHom φ`.
