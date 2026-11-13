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

## Compile outcomes (scratch/inertia-homs/Dev.lean, `lake env lean`)
- 02:20 VERIFIED compiled, no sorry: `G4Conj.conj_agree`, `G4Conj.cmp_fixed_of_fst`,
  `G4Conj.secFst` (+ `_mul`, `_one`, `_pow`, `secFstHom`), `InertiaHoms.isInertia_iff`,
  `InertiaHoms.inertia_transport`, `InertiaHoms.exists_closure_equiv`,
  `InertiaHoms.isUnit_prime_of_liesOver`, `G4WeilRes.point_fixed` (NOS transported to the
  conjugate `A ×_{K,e} ℚ̄` via `ℚ̄ ≅ K̄`), `G4WeilRes.ptIso`, `G4WeilRes.fixes_of_spec`,
  `G4WeilRes.inertiaFixesHomsMon : NOS → HomFreeFinite → ComapDVR → InertiaFixesHomsMon`.
- `InertiaFixesHomsMon` = `InertiaFixesHoms` restricted to homomorphisms
  (`φ : AbVar.Hom (bcAlong A e₁) (bcAlong B e₂)`, conclusion on `φ.hom`) and places over a prime
  (`p.Prime`, `LiesOver w p`). `ComapDVR`: valuation rings `w ∩ K` of number fields over `p` are DVRs
  (standard; to be proved).
