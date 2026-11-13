# g10-odd: the glue Prop `G10Glue` (oddness of `r_ℓ`)

Task g10-odd, 2026-11-13. Lean: `scratch/g10-odd/G10Odd.lean` (681 lines; compiles with
`lake env lean scratch/g10-odd/G10Odd.lean` after
`lake build ZInQKernel.HDecomp.LeafPush2.T ZInQKernel.HDecomp.I3Linalg.C2`; no `sorry`; the eight
main theorems use only `propext`, `Classical.choice`, `Quot.sound`). Log: `scratch/g10-odd/log.md`.

## Result

1. **`G10Glue` is proved from one strictly smaller named glue Prop** (VERIFIED, compiled):
   `G0Galois.g10Glue_of_conjTwist : ConjTwistNontrivial → G10Glue`. `G10Glue` is copied
   verbatim from `scratch/g0-mod-galois/part_galois.lean` (L224-242), with its dependencies.
   ```
   def ConjTwistNontrivial : Prop :=
     PkgI3.FaltingsTate →
     ∀ (K : Type) [Field K] [NumberField K] [IsGalois ℚ K] (A : PkgI3.AbVar K) (ℓ : ℕ)
       [Fact ℓ.Prime], A.dim = 2 → ∀ c : PkgI4.GQ, PkgI4.IsComplexConj c →
       ¬ ∀ σ τ : Field.absoluteGaloisGroup K, resQ K τ = c * resQ K σ * c⁻¹ →
         A.galRep ℓ τ = A.galRep ℓ σ
   ```
   This is a statement about `A` alone: complex conjugation does not act trivially by
   conjugation on the image of `G_K` in `GL(V_ℓ(A))`. `r`, `e`, the rank-4, division and
   noncommutativity hypotheses and the two opaque placeholders do not appear. **Glue**
   (STANDARD, N5 L742-751 / h-trust C5). The Lean proof of the reduction: `r(c)² = 1` (a complex
   conjugation is an involution, `isComplexConj_mul_self`); a 2×2 involution other than `±1` has
   determinant `−1` (`det_eq_neg_one_of_sq_eq_one`); if `r(c) = ±1` then `r(cσc⁻¹) = r(σ)`, so the
   intertwiner `e` gives `tate(τ) = tate(σ)` on `ℚ̄_ℓ ⊗ V_ℓ(A)`, and base change along
   `ℚ_ℓ → ℚ̄_ℓ` is injective (`baseChange_injective'`, flatness), so `ρ_ℓ(τ) = ρ_ℓ(σ)` on `V_ℓ(A)`,
   contradicting `ConjTwistNontrivial`.

2. **Defect in the statement (not a falsity):** `G10Glue`'s hypotheses `HSyn.T11_RiemannGAGA`
   and `HSyn.T12_ArtinComparison` are `opaque … : Prop` placeholders (VERIFIED, Split.lean
   L19261-19268). Nothing can be derived from them, so they are inert: a proof of `G10Glue` can
   only use `PkgI3.FaltingsTate`. The statement is true (by the argument below) and is kept. The
   **corrected statement** `G10GlueConcrete` replaces them by the concrete leaves of
   `ZInQKernel/HDecomp/LeafPush2/T.lean` and `Objects.lean`: T11(a) `T11a_RiemannEnd`, T11(b)
   `T11b_Rigidity`, T35 `UniformizationExists`, T5 `PkgI2.TorsionStructure`, T26
   `PkgI3.TateModuleFree` (T12 is glue, so it is not a hypothesis). The conclusion is unchanged.
   Proved (VERIFIED, compiled): `g10GlueConcrete_of_conjTwistFromLeaves : ConjTwistFromLeaves →
   G10GlueConcrete`, with `ConjTwistFromLeaves := T11a → T11b → T35 → T5 → T26 →
   ConjTwistNontrivial` (glue). Recommendation for integration: replace `odd : G10Glue` in
   g0-mod-galois's `ModGaloisPieces` by `ConjTwistNontrivial`. Both `G10Glue` and the
   conclusion of `G10GlueConcrete` follow from it (`g10Out_of_conjTwist`, which needs no opaque
   hypothesis).

3. **Alternative split through a number-field form of T12** (VERIFIED, compiled):
   `g10Glue_of_T12K_conjTwistOutside : T12K_ComplexConjEigen → ConjTwistOutside → G10Glue`.
   - `T12K_ComplexConjEigen` (**glue target**, same proof and sources as `T12_ComplexConjEigen`):
     for `A/K` of dimension `g` and `σ ∈ G_K` whose image `resQ K σ` is a complex conjugation,
     `ker(ρ_ℓ(σ) − 1)` and `ker(ρ_ℓ(σ) + 1)` have dimension `g`. Proved:
     `t12_of_t12K : T12K_ComplexConjEigen → ZInQ.LeafPush2.T12_ComplexConjEigen`, so T12K
     contains the existing T12 target. It settles the case `c ∈ G_K`
     (`not_pm_one_of_mem_range`), and alone gives oddness when every complex conjugation lies
     in `G_K`, e.g. `K` totally real (`isOdd_of_T12K_of_forall_mem`).
   - `ConjTwistOutside` (**glue**): `ConjTwistNontrivial` for `c ∉ (resQ K).range` only.
   - In Glazer's application this split does not help. The case `c ∈ G_K` does not occur
     there (F5 below), so `ConjTwistOutside` carries all of G10's content.

4. **The linear algebra of `ConjTwistNontrivial`'s proof is proved** (§6, VERIFIED, compiled):
   `betti_skeleton`. Let `H, H'` be ℚ-spaces with complex structures `J, J'` on `H⊗ℝ, H'⊗ℝ`,
   `W ⊆ Hom_ℚ(H,H')` a subspace of holomorphic maps, and `F` antiholomorphic. Suppose `F ⊗ 1` lies
   in the `E`-span of `W ⊗ 1`, read through an injective canonical map
   `E ⊗ Hom → Hom_E(E⊗H, E⊗H')`. Then `F = 0`. The ingredients are
   `mem_of_one_tmul_mem_span` (`(W ⊗ E) ∩ U = W`) and `eq_zero_of_holo_of_antiholo`.
   `betti_skeleton_fd` is the finite-dimensional form with no canonical-map hypothesis. Its
   hypothesis is `F ⊗ 1 ∈ span_E {φ ⊗ 1 : φ ∈ W}` inside `Hom_E(E⊗H, E⊗H')`, which is exactly
   what Faltings plus the Artin comparison give. Its proof goes through matrices
   (`LinearMap.toMatrix_baseChange`, `matrix_mem_of_map_mem_span`, `mem_of_baseChange_mem_span`).

5. **`ConjTwistNontrivial` is not vacuous in its quantifier** (§8, VERIFIED, compiled):
   `exists_resQ_conj`. For `K/ℚ` Galois and `g ∈ G_ℚ`, every `g σ g⁻¹` with `σ ∈ G_K` is
   `resQ K τ` for some `τ ∈ G_K`, so the twist condition constrains every `σ`. The proof uses
   `qEmbRing_bijective` (`ℚ̄ → K̄` is onto) and `range_stable` (the copy of `K` in `ℚ̄` is
   `G_ℚ`-stable, from `Normal.splits`). Without normality the condition could hold vacuously, and
   the Prop would claim more than the mathematics gives.

## The proof of `ConjTwistNontrivial` (STANDARD; not formalized)

Suppose `ρ_ℓ(τ) = ρ_ℓ(σ)` whenever `τ = cσc⁻¹`. Let `ι : ℚ̄ → ℂ` realize `c`. Since `K` is
normal, `c̄ = c|_K` is an automorphism of `K`; let `A^c = A ⊗_{K,c̄} K`. The `c`-semilinear
bijection `A(K̄) → A^c(K̄)` gives `c_* : V_ℓ(A) → V_ℓ(A^c)` with `c_* ρ_A(σ) = ρ_{A^c}(cσc⁻¹) c_*`.
By the assumption `c_*` is `G_K`-equivariant, so by Faltings (`PkgI3.FaltingsTate`, R9b)
`c_* ∈ Hom(A, A^c) ⊗ ℚ_ℓ`. By the Artin comparison at `ι` (uniformization T35, torsion T5,
T26), `c_* = F_* ⊗ 1`, where `F : A(ℂ) → A^c(ℂ)` is complex conjugation, antiholomorphic, and
`F_*` is ℚ-rational on `H₁`. Elements of `Hom(A, A^c)` act holomorphically (T11). By
`betti_skeleton`, `F_* = 0`, but `F_*` is bijective and `H₁ ≠ 0`. If `c ∈ G_K`, then `A^c = A`
and `c_* = ρ_A(c)`. This is the argument sketched in `G10Glue`'s docstring, made precise.

**What remains to formalize it** (glue, all missing in the project):
- the conjugate variety `A^c` over `K` as a `PkgI3.AbVar K`, which needs base change along an
  automorphism of `K`, not just along an algebra map;
- the map `c_*` on Tate modules;
- the Artin comparison `T_ℓ(A) ≅ Λ ⊗ ℤ_ℓ` at `ι` for `A` over a number field, with the
  semilinear `c_*` matched to `F_*`;
- the instantiation of `betti_skeleton_fd` (its linear algebra is done).

T12 shares these needs (its docstring), but `T12_ComplexConjEigen` itself is too weak (F4).

## Findings

- **F1** (VERIFIED): T11 and T12 in `G10Glue` are opaque, so they are inert (item 2).
- **F2** (VERIFIED, compiled): `G10Glue` follows from `ConjTwistNontrivial`, and from
  `T12K_ComplexConjEigen` together with `ConjTwistOutside`.
- **F3** (VERIFIED, compiled): `T12K_ComplexConjEigen → T12_ComplexConjEigen`.
- **F4** (argument, not machine-checked): `T12_ComplexConjEigen` cannot replace Faltings when
  `c ∉ G_K`, and Weil restriction does not help. For `W = Res_{K/ℚ}A`,
  `V_ℓ(W) ⊗ ℚ̄_ℓ ≅ (r ⊗ ℚ̄_ℓ[Gal(K/ℚ)])²`. If `c|_K ≠ id`, then `c` permutes `Gal(K/ℚ)` without
  fixed points, so its eigenspaces on `V_ℓ(W)` have dimensions `(2n, 2n)` whether or not
  `r(c) = ±1`.
- **F5** (STANDARD argument; Shimura, Math. Ann. 215 (1975), UNVERIFIED reference): under
  `G10Glue`'s hypotheses `End⁰_K(A) = B` is a quaternion division algebra over `ℚ` (rank 4,
  noncommutative, division). Then `K` has no real place: for `c ∈ G_K`, `F_∞` commutes with `B` on
  `H₁(A(ℂ),ℚ)`, which is free of rank 1 over `B`, so `F_∞ ∈ B^op` and `F_∞² = 1` give `F_∞ = ±1`,
  contradicting the `(2,2)` eigenspaces. The analogous ℓ-adic argument fails when `B ⊗ ℚ_ℓ` is
  split, so the Betti ℚ-structure, through the Artin comparison, cannot be avoided.
- The hypotheses `finrank End = 4`, `EndDivision` and noncommutativity are not used by any proof
  here, and `IsGalois ℚ K` only through `ConjTwistNontrivial`. This is consistent with the
  docstring of `G10Glue`.

## Leaves and glue after this task

| Name | Kind | Status |
|---|---|---|
| `PkgI3.FaltingsTate` | leaf (Faltings 1983, Satz 4 / Kor. 1) | in Objects.lean |
| T11a, T11b, T35 (`ZInQ.LeafPush2`), T5 `PkgI2.TorsionStructure`, T26 `PkgI3.TateModuleFree` | textbook leaves | in the build |
| `ConjTwistNontrivial` (or `ConjTwistFromLeaves`) | glue, STANDARD | unproved; linear-algebra core proved (`betti_skeleton`) |
| `T12K_ComplexConjEigen` | glue target (generalizes T12) | unproved; implies `T12_ComplexConjEigen` (proved) |
| `ConjTwistOutside` | glue (part of `ConjTwistNontrivial`) | unproved |
| reduction `G10Glue ⇐ ConjTwistNontrivial` | glue | **proved** |
| reduction `G10GlueConcrete ⇐ ConjTwistFromLeaves` | glue | **proved** |
| reduction `G10Glue ⇐ T12K ∧ ConjTwistOutside` | glue | **proved** |
