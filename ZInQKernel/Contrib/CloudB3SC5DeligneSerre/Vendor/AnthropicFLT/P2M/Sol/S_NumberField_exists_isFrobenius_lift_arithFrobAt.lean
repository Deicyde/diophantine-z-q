/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_NumberField_exists_isFrobenius_lift_arithFrobAt (git blob 36499ae8bf7c1db8d7c7755e8e7dcfc7d10b92bf, sha256 27a93c5a4753b335e1b9a124bff23c3926d6f9e62cb36939fda97e8c3abd4dd8).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_TaylorWiles_Primes
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_FieldTheory_RatAlgClosureGalois
import Mathlib.RingTheory.Invariant.Profinite
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.KrullTopology
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.Topology.Algebra.MulAction
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Algebra.Rat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_NumberField_exists_isFrobenius_lift_arithFrobAt.C6P1T2
end P2MW.S_NumberField_exists_isFrobenius_lift_arithFrobAt.C6P1T2

namespace P2MW.S_NumberField_exists_isFrobenius_lift_arithFrobAt

open scoped NumberField Pointwise




noncomputable section

namespace C6P1T2

section T1
variable (E : IntermediateField ℚ (AlgebraicClosure ℚ))

scoped instance smulCommClass_gal_ringOfIntegers : SMulCommClass ((AlgebraicClosure ℚ) ≃ₐ[E] (AlgebraicClosure ℚ)) (𝓞 E) (𝓞 (AlgebraicClosure ℚ)) where
  smul_comm g a b := by
    apply Subtype.ext
    change g ((algebraMap (𝓞 E) (𝓞 (AlgebraicClosure ℚ)) a : (AlgebraicClosure ℚ)) * (b : (AlgebraicClosure ℚ))) = (algebraMap (𝓞 E) (𝓞 (AlgebraicClosure ℚ)) a : (AlgebraicClosure ℚ)) * g (b : (AlgebraicClosure ℚ))
    rw [map_mul]
    congr 1
    exact g.commutes (a : E)

scoped instance continuousSMul_gal_ringOfIntegers :
    @ContinuousSMul ((AlgebraicClosure ℚ) ≃ₐ[E] (AlgebraicClosure ℚ)) (𝓞 (AlgebraicClosure ℚ)) _ _ ⊥ := by
  letI : TopologicalSpace (𝓞 (AlgebraicClosure ℚ)) := ⊥
  haveI : DiscreteTopology (𝓞 (AlgebraicClosure ℚ)) := ⟨rfl⟩
  rw [continuousSMul_iff_stabilizer_isOpen]
  intro b
  have h := stabilizer_isOpen_of_isIntegral (K := E) (L := (AlgebraicClosure ℚ)) (b : (AlgebraicClosure ℚ))
  convert h using 1
  ext g
  simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
  exact ⟨fun hg => congrArg Subtype.val hg, fun hg => Subtype.ext hg⟩

scoped instance isInvariant_gal_ringOfIntegers :
    Algebra.IsInvariant (𝓞 E) (𝓞 (AlgebraicClosure ℚ)) ((AlgebraicClosure ℚ) ≃ₐ[E] (AlgebraicClosure ℚ)) where
  isInvariant b hb := by

    have hbE : (b : (AlgebraicClosure ℚ)) ∈ (⊥ : IntermediateField E (AlgebraicClosure ℚ)) := by
      rw [InfiniteGalois.mem_bot_iff_fixed]
      intro g
      exact congrArg Subtype.val (hb g)
    obtain ⟨e, he⟩ := IntermediateField.mem_bot.mp hbE

    have hint : IsIntegral ℤ e := by
      have hb' : IsIntegral ℤ (b : (AlgebraicClosure ℚ)) := b.2
      rw [← he] at hb'
      exact (isIntegral_algHom_iff (algebraMap E (AlgebraicClosure ℚ)).toIntAlgHom (algebraMap E (AlgebraicClosure ℚ)).injective).mp hb'
    refine ⟨⟨e, hint⟩, Subtype.ext ?_⟩
    exact he

end T1

section T2
variable (E : IntermediateField ℚ (AlgebraicClosure ℚ)) [IsGalois ℚ E]

theorem restrictNormal_restrictScalars (δ : (AlgebraicClosure ℚ) ≃ₐ[E] (AlgebraicClosure ℚ)) :
    (δ.restrictScalars ℚ).restrictNormal E = 1 := by
  apply AlgEquiv.ext
  intro x
  apply (algebraMap E (AlgebraicClosure ℚ)).injective
  rw [AlgEquiv.restrictNormal_commutes]
  exact δ.commutes x

end T2

end C6P1T2
open scoped _root_.P2MW.S_NumberField_exists_isFrobenius_lift_arithFrobAt.C6P1T2

end
open scoped _root_.P2MW.S_NumberField_exists_isFrobenius_lift_arithFrobAt.C6P1T2

open C6P1T2 in
theorem solution
    (E : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField E] [IsGalois ℚ E]
    (ℓ : ℕ) (hℓ : ℓ.Prime) (Q : Ideal (𝓞 E)) [Q.IsPrime] [Q.LiesOver (FrobeniusDensity.ratPrimeIdeal ℓ)]
    [Finite (𝓞 E ⧸ Q)] :
    ∃ (Qt : Ideal (𝓞 (AlgebraicClosure ℚ))) (_ : Qt.IsMaximal)
      (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
      Qt.LiesOver Q ∧ AlgEquiv.restrictNormal τ E = arithFrobAt ℤ (E ≃ₐ[ℚ] E) Q ∧
      (∀ x : 𝓞 (AlgebraicClosure ℚ), τ • x ∈ Qt ↔ x ∈ Qt) ∧
      ∀ x : 𝓞 (AlgebraicClosure ℚ), τ • x - x ^ ℓ ∈ Qt := by
  letI : TopologicalSpace (𝓞 (AlgebraicClosure ℚ)) := ⊥
  haveI : DiscreteTopology (𝓞 (AlgebraicClosure ℚ)) := ⟨rfl⟩

  have hQbot : Q ≠ ⊥ := FrobeniusDensity.ne_bot_of_liesOver_ratPrimeIdeal hℓ
  haveI hQmax : Q.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hQbot

  haveI : Algebra.IsIntegral (𝓞 E) (𝓞 (AlgebraicClosure ℚ)) := IsIntegralClosure.isIntegral_algebra (𝓞 E) (A := 𝓞 (AlgebraicClosure ℚ)) (AlgebraicClosure ℚ)
  obtain ⟨Qt, hQt, hQtQ⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 (AlgebraicClosure ℚ)) Q
  haveI := hQt; haveI := hQtQ

  set φ : E ≃ₐ[ℚ] E := arithFrobAt ℤ (E ≃ₐ[ℚ] E) Q with hφdef
  have hφQ : φ • Q = Q := IsArithFrobAt.arithFrobAt_mem_stabilizer ℤ (E ≃ₐ[ℚ] E) Q
  have coe_smul : ∀ (g : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (b : 𝓞 (AlgebraicClosure ℚ)), ((g • b : 𝓞 (AlgebraicClosure ℚ)) : (AlgebraicClosure ℚ)) = g (b : (AlgebraicClosure ℚ)) := fun _ _ => rfl
  have coe_smul' : ∀ (g : (AlgebraicClosure ℚ) ≃ₐ[E] (AlgebraicClosure ℚ)) (b : 𝓞 (AlgebraicClosure ℚ)), ((g • b : 𝓞 (AlgebraicClosure ℚ)) : (AlgebraicClosure ℚ)) = g (b : (AlgebraicClosure ℚ)) := fun _ _ => rfl
  have coe_smulE : ∀ (g : E ≃ₐ[ℚ] E) (a : 𝓞 E), ((g • a : 𝓞 E) : E) = g (a : E) := fun _ _ => rfl
  have coe_alg : ∀ a : 𝓞 E, ((algebraMap (𝓞 E) (𝓞 (AlgebraicClosure ℚ)) a : 𝓞 (AlgebraicClosure ℚ)) : (AlgebraicClosure ℚ)) = ((a : E) : (AlgebraicClosure ℚ)) := fun _ => rfl

  have smul_alg : ∀ (τ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (a : 𝓞 E),
      τ • algebraMap (𝓞 E) (𝓞 (AlgebraicClosure ℚ)) a = algebraMap (𝓞 E) (𝓞 (AlgebraicClosure ℚ)) ((τ.restrictNormal E) • a) := by
    intro τ a
    apply Subtype.ext
    exact (AlgEquiv.restrictNormal_commutes τ E (a : E)).symm
  have res_scalars : ∀ (δ : (AlgebraicClosure ℚ) ≃ₐ[E] (AlgebraicClosure ℚ)) (b : 𝓞 (AlgebraicClosure ℚ)), (δ.restrictScalars ℚ) • b = δ • b := fun _ _ => rfl
  have res_scalars_ideal : ∀ (δ : (AlgebraicClosure ℚ) ≃ₐ[E] (AlgebraicClosure ℚ)) (I : Ideal (𝓞 (AlgebraicClosure ℚ))), (δ.restrictScalars ℚ) • I = δ • I := by
    intro δ I
    rw [Ideal.pointwise_smul_def, Ideal.pointwise_smul_def]
    congr 1

  obtain ⟨τ₀, hτ₀⟩ := AlgEquiv.restrictNormalHom_surjective (F := ℚ) (K₁ := E) (E := AlgebraicClosure ℚ) φ
  have hτ₀' : τ₀.restrictNormal E = φ := hτ₀

  have hunder : (τ₀ • Qt).under (𝓞 E) = Qt.under (𝓞 E) := by
    ext a
    rw [Ideal.under_def, Ideal.under_def, Ideal.mem_comap, Ideal.mem_comap,
      Ideal.mem_pointwise_smul_iff_inv_smul_mem, smul_alg]
    have hinv : (τ₀⁻¹).restrictNormal E = φ⁻¹ := by
      change AlgEquiv.restrictNormalHom E τ₀⁻¹ = φ⁻¹
      rw [map_inv]; exact congrArg _ hτ₀
    rw [hinv, ← Ideal.mem_of_liesOver Qt Q, ← Ideal.mem_of_liesOver Qt Q,
      ← Ideal.mem_inv_pointwise_smul_iff, inv_inv, hφQ]
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite
    (A := 𝓞 E) (B := 𝓞 (AlgebraicClosure ℚ)) (G := (AlgebraicClosure ℚ) ≃ₐ[E] (AlgebraicClosure ℚ)) (τ₀ • Qt) Qt hunder

  set τ₁ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) := g.restrictScalars ℚ * τ₀ with hτ₁def
  have hτ₁Qt : τ₁ • Qt = Qt := by
    rw [hτ₁def, mul_smul, res_scalars_ideal, ← hg]
  have hτ₁res : τ₁.restrictNormal E = φ := by
    change AlgEquiv.restrictNormalHom E (g.restrictScalars ℚ * τ₀) = φ
    rw [map_mul]
    change (g.restrictScalars ℚ).restrictNormal E * τ₀.restrictNormal E = φ
    rw [restrictNormal_restrictScalars, one_mul, hτ₀']
  have hstab₁ : ∀ x : 𝓞 (AlgebraicClosure ℚ), τ₁ • x ∈ Qt ↔ x ∈ Qt := fun x => by
    conv_lhs => rw [← hτ₁Qt]
    exact Ideal.smul_mem_pointwise_smul_iff

  have hℓQ : ((ℓ : ℤ) : 𝓞 E) ∈ Q := by
    have := (Ideal.mem_of_liesOver Q (FrobeniusDensity.ratPrimeIdeal ℓ) (ℓ : ℤ)).mp
      (Ideal.mem_span_singleton_self _)
    simpa using this
  have hℓQt : ((ℓ : ℕ) : 𝓞 (AlgebraicClosure ℚ)) ∈ Qt := by
    have h2 := (Ideal.mem_of_liesOver Qt Q ((ℓ : ℤ) : 𝓞 E)).mp hℓQ
    simpa using h2
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI hchar : CharP (𝓞 (AlgebraicClosure ℚ) ⧸ Qt) ℓ :=
    (CharP.charP_iff_prime_eq_zero hℓ).mpr ((Ideal.Quotient.eq_zero_iff_mem).mpr (by simpa using hℓQt))
  let F : 𝓞 (AlgebraicClosure ℚ) ⧸ Qt →+* 𝓞 (AlgebraicClosure ℚ) ⧸ Qt := frobenius (𝓞 (AlgebraicClosure ℚ) ⧸ Qt) ℓ
  have hFbij : Function.Bijective F := by
    refine ⟨frobenius_inj _ _, fun y => ?_⟩
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (b : (AlgebraicClosure ℚ)) hℓ.pos
    have hcint : IsIntegral ℤ c := IsIntegral.of_pow hℓ.pos (by rw [hc]; exact b.2)
    refine ⟨Ideal.Quotient.mk Qt ⟨c, hcint⟩, ?_⟩
    change (Ideal.Quotient.mk Qt ⟨c, hcint⟩) ^ ℓ = _
    rw [← map_pow]
    congr 1
    exact Subtype.ext hc

  have hle : ∀ τ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), (∀ x : 𝓞 (AlgebraicClosure ℚ), τ • x ∈ Qt ↔ x ∈ Qt) →
      Qt ≤ Qt.comap (MulSemiringAction.toRingHom (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (𝓞 (AlgebraicClosure ℚ)) τ) := fun τ h x hx => (h x).mpr hx
  have hstab₁' : ∀ x : 𝓞 (AlgebraicClosure ℚ), τ₁⁻¹ • x ∈ Qt ↔ x ∈ Qt := fun x => by
    rw [← hstab₁ (τ₁⁻¹ • x), smul_inv_smul]
  let θinv : 𝓞 (AlgebraicClosure ℚ) ⧸ Qt →+* 𝓞 (AlgebraicClosure ℚ) ⧸ Qt := Ideal.quotientMap Qt _ (hle τ₁⁻¹ hstab₁')
  have hθinv : ∀ x : 𝓞 (AlgebraicClosure ℚ), θinv (Ideal.Quotient.mk Qt x) = Ideal.Quotient.mk Qt (τ₁⁻¹ • x) := fun x => rfl

  have hφfrob : ∀ a : 𝓞 E, φ • a - a ^ ℓ ∈ Q := by
    intro a
    have h := (IsArithFrobAt.arithFrobAt ℤ (E ≃ₐ[ℚ] E) Q) a
    have hcard : Nat.card (ℤ ⧸ Q.under ℤ) = ℓ := by
      rw [← Q.over_def (FrobeniusDensity.ratPrimeIdeal ℓ)]
      rw [Nat.card_congr (Int.quotientSpanNatEquivZMod ℓ).toEquiv, Nat.card_zmod]
    rw [hcard] at h
    exact h
  have hinv1 : (τ₁⁻¹).restrictNormal E = φ⁻¹ := by
    change AlgEquiv.restrictNormalHom E τ₁⁻¹ = φ⁻¹
    rw [map_inv]; exact congrArg _ hτ₁res
  have hcomm : ∀ a : 𝓞 E, F (θinv (Ideal.Quotient.mk Qt (algebraMap (𝓞 E) (𝓞 (AlgebraicClosure ℚ)) a)))
      = Ideal.Quotient.mk Qt (algebraMap (𝓞 E) (𝓞 (AlgebraicClosure ℚ)) a) := by
    intro a
    rw [hθinv, smul_alg, hinv1, frobenius_def, ← map_pow, ← map_pow, Ideal.Quotient.eq, ← map_sub,
      ← Ideal.mem_of_liesOver Qt Q]
    have h := hφfrob (φ⁻¹ • a)
    rw [smul_inv_smul] at h
    rw [← neg_sub]
    exact Q.neg_mem h

  let θ : 𝓞 (AlgebraicClosure ℚ) ⧸ Qt →+* 𝓞 (AlgebraicClosure ℚ) ⧸ Qt := Ideal.quotientMap Qt _ (hle τ₁ hstab₁)
  have hθ : ∀ x : 𝓞 (AlgebraicClosure ℚ), θ (Ideal.Quotient.mk Qt x) = Ideal.Quotient.mk Qt (τ₁ • x) := fun x => rfl
  have hθinv_bij : Function.Bijective θinv := by
    refine Function.bijective_iff_has_inverse.mpr ⟨θ, fun y => ?_, fun y => ?_⟩
    · obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
      rw [hθinv, hθ, smul_inv_smul]
    · obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
      rw [hθ, hθinv, inv_smul_smul]
  let ψ₀ : 𝓞 (AlgebraicClosure ℚ) ⧸ Qt →+* 𝓞 (AlgebraicClosure ℚ) ⧸ Qt := F.comp θinv
  have hψ₀ : ∀ x : 𝓞 (AlgebraicClosure ℚ), ψ₀ (Ideal.Quotient.mk Qt x) = F (θinv (Ideal.Quotient.mk Qt x)) := fun _ => rfl
  let ψ₁ : (𝓞 (AlgebraicClosure ℚ) ⧸ Qt) →ₐ[𝓞 E ⧸ Q] (𝓞 (AlgebraicClosure ℚ) ⧸ Qt) :=
    { ψ₀ with
      commutes' := fun r => by
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
        rw [Ideal.Quotient.algebraMap_mk_of_liesOver]
        exact hcomm a }
  let ψ : (𝓞 (AlgebraicClosure ℚ) ⧸ Qt) ≃ₐ[𝓞 E ⧸ Q] (𝓞 (AlgebraicClosure ℚ) ⧸ Qt) := AlgEquiv.ofBijective ψ₁ (hFbij.comp hθinv_bij)
  have hψ : ∀ x : 𝓞 (AlgebraicClosure ℚ), ψ (Ideal.Quotient.mk Qt x) = F (θinv (Ideal.Quotient.mk Qt x)) := fun _ => rfl

  obtain ⟨δ, hδ⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite (G := (AlgebraicClosure ℚ) ≃ₐ[E] (AlgebraicClosure ℚ)) Q Qt ψ
  have hδ' : ∀ b : 𝓞 (AlgebraicClosure ℚ), Ideal.Quotient.mk Qt ((δ : (AlgebraicClosure ℚ) ≃ₐ[E] (AlgebraicClosure ℚ)) • b) = F (θinv (Ideal.Quotient.mk Qt b)) := by
    intro b
    have := DFunLike.congr_fun hδ (Ideal.Quotient.mk Qt b)
    rw [Ideal.Quotient.stabilizerHom_apply] at this
    rw [← hψ, ← this]
    rfl
  have hδQt : ∀ y : 𝓞 (AlgebraicClosure ℚ), (δ : (AlgebraicClosure ℚ) ≃ₐ[E] (AlgebraicClosure ℚ)) • y ∈ Qt ↔ y ∈ Qt := fun y => by
    have h2 : (δ : (AlgebraicClosure ℚ) ≃ₐ[E] (AlgebraicClosure ℚ)) • Qt = Qt := δ.2
    have h3 := (Ideal.smul_mem_pointwise_smul_iff (a := (δ : (AlgebraicClosure ℚ) ≃ₐ[E] (AlgebraicClosure ℚ))) (S := Qt) (x := y))
    rwa [h2] at h3

  refine ⟨Qt, hQt, ((δ : (AlgebraicClosure ℚ) ≃ₐ[E] (AlgebraicClosure ℚ)).restrictScalars ℚ) * τ₁, hQtQ, ?_, ?_, ?_⟩
  · change AlgEquiv.restrictNormalHom E (((δ : (AlgebraicClosure ℚ) ≃ₐ[E] (AlgebraicClosure ℚ)).restrictScalars ℚ) * τ₁) = φ
    rw [map_mul]
    change ((δ : (AlgebraicClosure ℚ) ≃ₐ[E] (AlgebraicClosure ℚ)).restrictScalars ℚ).restrictNormal E * τ₁.restrictNormal E = φ
    rw [restrictNormal_restrictScalars, one_mul, hτ₁res]
  · intro x
    rw [mul_smul, res_scalars, hδQt, hstab₁]
  · intro x
    rw [← Ideal.Quotient.eq, map_pow, mul_smul, res_scalars, hδ', hθinv, inv_smul_smul, frobenius_def]
