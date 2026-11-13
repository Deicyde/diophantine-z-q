# conj-twist results log

## Statements
- `ConjTwistNontrivial`, `ConjTwistFromLeaves` copied verbatim from scratch/g10-odd/G10Odd.lean
  (L185-205, L383-391) into scratch/conj-twist/ConjTwist.lean §1, with `resQ`, `qEmbRing`,
  `resQ_spec`, `isComplexConj_mul_self`, `qEmbRing_bijective`, `range_stable`,
  `one_tmul_injective`, `baseChange_injective'`, `baseChange_injective₂`,
  `eq_zero_of_holo_of_antiholo`, `matrix_mem_of_map_mem_span`, `mem_of_baseChange_mem_span`,
  `betti_skeleton_fd` (verbatim, proofs included). VERIFIED (diff of the defs).

## Compile outcomes
- 2026-11-13 05:31 `lake env lean scratch/conj-twist/ConjTwist.lean`: 0 errors (warnings: letI
  style lints in the verbatim `resQ_spec`, deprecations). New, all with axioms
  [propext, Classical.choice, Quot.sound], VERIFIED (compiled):
  - `faltingsV` (FaltingsTate + TateModuleFree ⇒ G_K-equivariant V_ℓ(A) → V_ℓ(B) lies in the
    ℚ_ℓ-span of {V_ℓ(f)}),
  - `conjData` (c ∈ G_ℚ complex conjugation, K/ℚ Galois ⇒ cc ∈ Aut(K̄) involutive, preserving K,
    complex conjugation for some ι : K̄ → ℂ, twist τ∘cc = cc∘σ ⇒ resQ τ = c resQ σ c⁻¹),
  - `exists_twist` (every τ ∈ G_K is a cc-twist of some σ),
  - `holoSub` (ℚ-subspace of holomorphic maps),
  - glue def `ConjBettiData` (conjugate variety + Artin comparison + holomorphy),
  - `conjTwistNontrivial_of_conjBettiData : TateModuleFree → ConjBettiData → ConjTwistNontrivial`,
  - `conjTwistFromLeaves_of_conjBettiData : ConjBettiData → ConjTwistFromLeaves`.
- 2026-11-13 05:34 §5 added: `conjVar` (A^s = pullback of A along Spec(s), s : K →+* K),
  `ccHom`, `conjPt` (A(K̄) →* A^s(K̄), P ↦ adjunction(Spec(cc) ≫ P)), `conjPt_galAct`
  (τ∘cc = cc∘σ ⇒ c_*(σP) = τ c_*(P)), `conjT`, `conjV`, `conjV_galRep` (twisted equivariance on
  V_ℓ), `restrictK` (s = cc|_K), glue def `ConjBettiComparison` (Betti data for the concrete
  c_* = conjV), `conjBettiData_of_comparison`, `conjTwistNontrivial_of_comparison`
  (TateModuleFree → ConjBettiComparison → ConjTwistNontrivial),
  `conjTwistFromLeaves_of_comparison` (ConjBettiComparison → ConjTwistFromLeaves).
  Compiles: 0 errors, 0 sorry; all 8 `#print axioms` [propext, Classical.choice, Quot.sound].
  VERIFIED (compiled).
- 2026-11-13 05:38 §6 added (next split of ConjBettiComparison): `embHom`, `toC`
  (A(K̄) →* A(ℂ)_{ι∘alg}), statements N1 `ArtinTorsion` (glue), N4 `TateLattice` (glue),
  N2 `HomLinearLift` (textbook leaf, BL 1.2.1 Hom form), `conjHom`, `conjCs`, `mapPtIso`,
  `twistC`, N3 `ConjAntiLift` (glue), N5 `ConjVarDim` (glue); proved `toC_conjPt`
  (toC(c_* P) = twistC(toC P)). Compiles, 0 errors; axioms standard. VERIFIED (compiled).
- 2026-11-13 05:40 §7 added: `lift_mem_lattice` (a lift of a homomorphism maps Λ_A into Λ_B),
  `homT_tateLattice` (N1 ⇒ T_ℓ(f) α_A(1⊗λ) = α_B(1⊗Mλ)), `conjT_tateLattice`
  (N1 + toC_conjPt ⇒ c_* α_A(1⊗λ) = α_{A^s}(1⊗Nλ)). Compiles, 0 errors, axioms standard.
  VERIFIED (compiled).
- 2026-11-13 05:47 §8 added: `toMatrix_of_lattice`, `toLin_of_lattice`, `lattice_contradiction`,
  `twistC_one`, **`conjTwistNontrivial_of_lattice : TateModuleFree → UniformizationExists →
  ArtinTorsion → HomLinearLift → ConjAntiLift → TateLattice → ConjVarDim → ConjTwistNontrivial`**
  and `conjTwistFromLeaves_of_lattice : ArtinTorsion → HomLinearLift → ConjAntiLift →
  TateLattice → ConjVarDim → ConjTwistFromLeaves`. `ConjAntiLift` (N3) now also asserts
  `Function.Injective N` (true: N lifts the bijection twistC). Whole file: 0 errors, 0 sorry,
  14 `#print axioms` all [propext, Classical.choice, Quot.sound]. VERIFIED (compiled).
- 2026-11-13 05:55 §9 added: `ringHom_bijective_of_numberField`, **`conjVarDim : ConjVarDim`**
  (N5 proved: Spec(s) iso ⇒ pullback.fst iso ⇒ homeomorphism ⇒ equal topologicalKrullDim),
  `conjTwistNontrivial_of_lattice'` (T26 → T35 → N1 → N2 → N3 → N4 → ConjTwistNontrivial),
  `conjTwistFromLeaves_of_lattice'` (N1 → N2 → N3 → N4 → ConjTwistFromLeaves). Whole file:
  0 errors, 0 sorry, 17 `#print axioms` standard. VERIFIED (compiled).
- 2026-11-13 05:57 §10 added: `TateLatticeInj` (N4': α only injective), `tateLatticeInj_of_tateLattice`,
  **`conjTwistNontrivial_of_latticeInj : TateModuleFree → UniformizationExists → ArtinTorsion →
  HomLinearLift → ConjAntiLift → TateLatticeInj → ConjTwistNontrivial`** (flatness of ℚ_ℓ over
  ℤ_ℓ, postcomposition with ℚ_ℓ ⊗ α_B injective, matrices on ℚ_ℓ ⊗ (ℤ_ℓ ⊗ Λ)); old
  `conjTwistNontrivial_of_lattice` now derived from it (N5 discharged by `conjVarDim`);
  `conjTwistFromLeaves_of_latticeInj`, `conjTwistFromLeaves_of_lattice`. Naturality lemmas
  generalized to linear α. Whole file: 0 errors, 0 sorry, 17 `#print axioms` standard.
  VERIFIED (compiled).
- 2026-11-13 06:05 §11 added: `phi_zero`, `phi_nsmul`, `phi_sum`, `smul_inv_pow`, `smul_inv_succ`,
  `phi_tors`, `xPt`/`xPt_spec`, `xSeq` (x(λ) ∈ T_ℓ(A)), `xHom`, `xLin`,
  `xLin_liftBaseChange_injective`, **`tateLatticeInj_of_artinTorsion : ArtinTorsion →
  TateLatticeInj`** (N4' proved from N1), **`conjTwistNontrivial_of_N123 : TateModuleFree →
  UniformizationExists → ArtinTorsion → HomLinearLift → ConjAntiLift → ConjTwistNontrivial`**,
  **`conjTwistFromLeaves_of_N123 : ArtinTorsion → HomLinearLift → ConjAntiLift →
  ConjTwistFromLeaves`**. Whole file: 0 errors, 0 sorry, 20 `#print axioms` standard.
  VERIFIED (compiled).
- 2026-11-13 06:09 §12 added: **`toC_injective`** (proved with Mathlib's
  `ext_of_isDominant_of_isSeparated`: Spec ℂ → Spec K̄ surjective, Spec K̄ reduced, A proper),
  glue def `ArtinTorsionSurj` (N1-surj), `artinTorsion_of_surj`,
  **`conjTwistNontrivial_of_surj : TateModuleFree → UniformizationExists → ArtinTorsionSurj →
  HomLinearLift → ConjAntiLift → ConjTwistNontrivial`**, `conjTwistFromLeaves_of_surj`.
  Whole file: 0 errors, 0 sorry, 23 `#print axioms` standard. VERIFIED (compiled).
- 2026-11-13 06:15 §9b added: `conjL` (conjugation on ℂ^g), glue def `ConjUniformization` (N3a:
  z ↦ twistC(Φ z̄) satisfies IsUniformization for A^s with kernel Λ̄), `ConjAntiLiftLat` (N3 for
  number fields and full lattices), `conjAntiLiftLat_of_conjAntiLift`, `conjHomInv`,
  `mapPtIsoInv`, `twistC_injective`, `eq_zero_of_real_smul_mem` (real multiples in a full lattice
  ⇒ 0, via ofZLatticeBasis coordinates), **`conjAntiLiftLat_of : HomLinearLift →
  ConjUniformization → ConjAntiLiftLat`** (N2 for id of A^s). §10 main theorem now takes
  ConjAntiLiftLat. **`conjTwistNontrivial_main : TateModuleFree → UniformizationExists →
  ArtinTorsionSurj → HomLinearLift → ConjUniformization → ConjTwistNontrivial`**,
  **`conjTwistFromLeaves_main : ArtinTorsionSurj → HomLinearLift → ConjUniformization →
  ConjTwistFromLeaves`**. Whole file: 0 errors, 0 sorry, 26 `#print axioms` standard.
  VERIFIED (compiled).
- 2026-11-13 06:25 refactor: `toC_injective` moved before §7; naturality lemmas and the §11
  construction use it (§11 now takes a local torsion-surjectivity hypothesis `hsurj`); main
  theorem `conjTwistNontrivial_of_latticeInj` no longer takes N1. §13 added:
  **`torsion_surj_of_T5`** (T5 + a uniformization with full lattice ⇒ every n-torsion complex
  point comes from A(K̄): A(ℂ)[n] ↪ (ℤ/n)^{2g} via lattice coordinates of nz, |A(K̄)[n]| = n^{2g}
  by T5, toC injective, Nat.card), **`tateLatticeInj_of_T5`**,
  **`conjTwistNontrivial_final : TorsionStructure → TateModuleFree → UniformizationExists →
  HomLinearLift → ConjUniformization → ConjTwistNontrivial`**,
  **`conjTwistFromLeaves_final : HomLinearLift → ConjUniformization → ConjTwistFromLeaves`**.
  Whole file: 0 errors, 0 sorry, all `#print axioms` standard. VERIFIED (compiled).
