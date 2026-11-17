/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_FrobeniusDensity_frobeniusPowerDense_of_le_ker (git blob 3bd603b02e1e54f64b2fe8e96eb5a6a7908e0a77, sha256 345cb44dee30d33194617d4a06876785fb77efba55fc867856f84fd43a0decf8).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_GaloisRep_FrobeniusPowerDense
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_TaylorWiles_Primes
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_FrobeniusDensity_statement
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_FrobeniusDensity_exists_frobenius_conj_pow_of_statement

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_FrobeniusDensity_frobeniusPowerDense_of_le_ker

set_option autoImplicit false

theorem solution (F : Type) [Field F] [NumberField F] [IsGalois ℚ F]
    [Algebra F (AlgebraicClosure ℚ)] [IsScalarTower ℚ F (AlgebraicClosure ℚ)]
    {H : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)}
    (hker : (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) F).ker ≤ H)
    (S : Finset ℕ) : FrobeniusPowerDense S H := by
  intro σ
  let ι : F →ₐ[ℚ] AlgebraicClosure ℚ := IsScalarTower.toAlgHom ℚ F (AlgebraicClosure ℚ)
  let L : IntermediateField ℚ (AlgebraicClosure ℚ) := ι.fieldRange
  haveI : FiniteDimensional ℚ L := Module.Finite.equiv
    (((IntermediateField.topEquiv (F := ℚ) (E := F)).symm.trans (IntermediateField.equivMap ⊤ ι)).trans
      (IntermediateField.equivOfEq (AlgHom.fieldRange_eq_map ι).symm)).toLinearEquiv
  have hFD : ∀ (M : Type) [Field M] [NumberField M] [IsGalois ℚ M], FrobeniusDensity.Statement M :=
    fun M _ _ _ => FrobeniusDensity.statement M
  obtain ⟨ℓ, hℓ, hℓS, A, τ, γ, j, hA, hτ, hLfix⟩ :=
    FrobeniusDensity.exists_frobenius_conj_pow_of_statement hFD L σ S
  have hmemL : ∀ y : F, algebraMap F (AlgebraicClosure ℚ) y ∈ L := fun y =>
    AlgHom.mem_fieldRange.mpr ⟨y, rfl⟩
  have hfixF : ∀ y : F, (γ * τ ^ j * γ⁻¹ * σ⁻¹) (algebraMap F (AlgebraicClosure ℚ) y)
      = algebraMap F (AlgebraicClosure ℚ) y := by
    intro y
    have hy' : σ⁻¹ (algebraMap F (AlgebraicClosure ℚ) y) ∈ L := by
      have := AlgEquiv.restrictNormal_commutes σ⁻¹ F y
      rw [← this]
      exact hmemL _
    have h := hLfix _ hy'
    rw [AlgEquiv.mul_apply, ← h, ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
  refine ⟨ℓ, A, τ, γ, j, hℓ, hℓS, hA, hτ, hker ?_⟩
  rw [MonoidHom.mem_ker]
  apply AlgEquiv.ext
  intro y
  apply (algebraMap F (AlgebraicClosure ℚ)).injective
  have hc := AlgEquiv.restrictNormal_commutes (γ * τ ^ j * γ⁻¹ * σ⁻¹) F y
  change algebraMap F (AlgebraicClosure ℚ) (((γ * τ ^ j * γ⁻¹ * σ⁻¹).restrictNormal F) y)
    = algebraMap F (AlgebraicClosure ℚ) ((1 : F ≃ₐ[ℚ] F) y)
  rw [AlgEquiv.one_apply, hc]
  exact hfixF y
