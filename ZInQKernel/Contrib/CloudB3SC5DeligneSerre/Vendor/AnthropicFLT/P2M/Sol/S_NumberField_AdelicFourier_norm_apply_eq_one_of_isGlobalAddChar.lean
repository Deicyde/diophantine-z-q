/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_NumberField_AdelicFourier_norm_apply_eq_one_of_isGlobalAddChar (git blob 205d41602e2bff9e084cac3cdde22c1e89250878, sha256 e3df1a34e16910761a35db69776149c39fc9ebcc8a19c5dea3ef9e123f80a460).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicBox
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Complex.Circle

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_NumberField_AdelicFourier_norm_apply_eq_one_of_isGlobalAddChar

set_option autoImplicit false

open _root_.NumberField
namespace NumberField
end NumberField
open _root_.P2MW.S_NumberField_AdelicFourier_norm_apply_eq_one_of_isGlobalAddChar.NumberField
open _root_.IsDedekindDomain
open _root_.AutomorphicForm
open _root_.Filter

noncomputable section

namespace NumberField
export _root_.NumberField (AdeleRing AdelicBox.existsUnique_algebraMap_add_mem_adelicBox AdelicBox.exists_isCompact_adelicBox_subset)
namespace AdelicFourier
open _root_.NumberField

variable (F : Type) [Field F] [NumberField F]




theorem exists_norm_apply_le_of_isGlobalAddChar {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ) :
    ∃ M : ℝ, ∀ x : (AdeleRing (𝓞 F) F), ‖ψ x‖ ≤ M := by
  obtain ⟨C, hC, hsub⟩ := AdelicBox.exists_isCompact_adelicBox_subset F
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hψ.continuous.continuousOn
  refine ⟨M, fun x => ?_⟩
  obtain ⟨k, hk⟩ := (AdelicBox.existsUnique_algebraMap_add_mem_adelicBox F x).exists
  have hkx : ψ ((algebraMap F (AdeleRing (𝓞 F) F)) k + x) = ψ x := by
    rw [AddChar.map_add_eq_mul, hψ.principalInvariant k, one_mul]
  rw [← hkx]
  exact hM _ (hsub hk)

theorem norm_apply_le_one_of_bounded {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} {M : ℝ} (hM : ∀ x : (AdeleRing (𝓞 F) F), ‖ψ x‖ ≤ M)
    (x : (AdeleRing (𝓞 F) F)) : ‖ψ x‖ ≤ 1 := by
  by_contra h
  have h1 : 1 < ‖ψ x‖ := lt_of_not_ge h
  have hpow : ∀ n : ℕ, ‖ψ x‖ ^ n ≤ M := fun n => by
    rw [← norm_pow, ← AddChar.map_nsmul_eq_pow]
    exact hM _
  obtain ⟨n, hn⟩ := ((tendsto_pow_atTop_atTop_of_one_lt h1).eventually (eventually_gt_atTop M)).exists
  exact absurd (hpow n) (not_le.mpr hn)

theorem norm_apply_eq_one_of_isGlobalAddChar_impl {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ) (x : (AdeleRing (𝓞 F) F)) :
    ‖ψ x‖ = 1 := by
  obtain ⟨M, hM⟩ := exists_norm_apply_le_of_isGlobalAddChar F hψ
  refine le_antisymm (norm_apply_le_one_of_bounded F hM x) ?_
  have hneg : ‖ψ (-x)‖ ≤ 1 := norm_apply_le_one_of_bounded F hM (-x)
  have hprod : ‖ψ (-x)‖ * ‖ψ x‖ = 1 := by
    rw [← norm_mul, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, norm_one]
  calc (1 : ℝ) = ‖ψ (-x)‖ * ‖ψ x‖ := hprod.symm
    _ ≤ 1 * ‖ψ x‖ := mul_le_mul_of_nonneg_right hneg (norm_nonneg _)
    _ = ‖ψ x‖ := one_mul _

def toCircleAddChar {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ) : AddChar (AdeleRing (𝓞 F) F) Circle where
  toFun x := ⟨ψ x, mem_sphere_zero_iff_norm.2 (norm_apply_eq_one_of_isGlobalAddChar_impl F hψ x)⟩
  map_zero_eq_one' := by
    ext
    simp only [AddChar.map_zero_eq_one]
    rfl
  map_add_eq_mul' a b := by
    ext
    simp only [AddChar.map_add_eq_mul]
    rfl

theorem coe_toCircleAddChar_apply {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ) (x : (AdeleRing (𝓞 F) F)) :
    ((toCircleAddChar F hψ x : Circle) : ℂ) = ψ x := rfl

theorem exists_compAddChar_eq_of_isGlobalAddChar_impl {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ) :
    ∃ e : AddChar (AdeleRing (𝓞 F) F) Circle, Circle.coeHom.compAddChar e = ψ :=
  ⟨toCircleAddChar F hψ, by ext x; rfl⟩

#print axioms norm_apply_eq_one_of_isGlobalAddChar_impl
#print axioms exists_compAddChar_eq_of_isGlobalAddChar_impl

example : ∀ {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (_ : IsGlobalAddChar F ψ) (x : (AdeleRing (𝓞 F) F)), ‖ψ x‖ = 1 :=
  fun hψ x => norm_apply_eq_one_of_isGlobalAddChar_impl F hψ x
example : ∀ {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (_ : IsGlobalAddChar F ψ),
    ∃ e : AddChar (AdeleRing (𝓞 F) F) Circle, Circle.coeHom.compAddChar e = ψ :=
  fun hψ => exists_compAddChar_eq_of_isGlobalAddChar_impl F hψ

end NumberField.AdelicFourier

end

open _root_.NumberField
namespace NumberField
end NumberField
open _root_.P2MW.S_NumberField_AdelicFourier_norm_apply_eq_one_of_isGlobalAddChar.NumberField
open _root_.AutomorphicForm

theorem solution (F : Type) [Field F] [NumberField F]
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ) (x : AdeleRing (𝓞 F) F) :
    ‖ψ x‖ = 1 := by
  exact NumberField.AdelicFourier.norm_apply_eq_one_of_isGlobalAddChar_impl F hψ x
