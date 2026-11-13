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
- 02:16 VERIFIED compiled: `InertiaHoms.mem_of_isIntegral_int`, `InertiaHoms.comap_isDVR`
  (w ∩ F is a DVR for F a number field, w | p), `G4WeilRes.comapDVR`,
  `G4WeilRes.inertiaFixesHomsMon_of_leaves : NOS → HomFreeFinite → InertiaFixesHomsMon`.
- 02:20 Merged file `scratch/inertia-homs/InertiaHoms.lean` (2095 lines = G4.lean L1-1454
  verbatim + new part). `lake env lean`: 0 errors, ~40 s. `#print axioms`: all printed
  declarations (G4's 19 and the new `inertiaFixesHomsMon_of_leaves`, `conjAction_inertia'`,
  `homField_of_model_leaves'`, `comap_isDVR`, `point_fixed`) depend only on
  [propext, Classical.choice, Quot.sound]. VERIFIED.
- New headline `G4WeilRes.homField_of_model_leaves'`: G4 from `HomFreeFinite`,
  `MorphismsDescend`, `NeronOggShafarevich` (+ hK, hgood, hdim).
- Dev.lean (development copy with stubs) removed; its content is in InertiaHoms.lean.
