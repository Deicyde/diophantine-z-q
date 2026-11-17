/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_NumberField_AdelicFourier_forall_addChar_finitePart_mul_eq_one_iff_mem_traceDual (git blob 5a80e3d0bfa30b290d144972eb8c786aab593297, sha256 34723957cfdc0229a222336723cd93a12b7985a364a31234d31a9e7277909a0b).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicFourier
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicBox
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.Algebra.Module.ZLattice.Covolume
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_NumberField_AdelicFourier_addChar_zero_finitePart_algebraMap_eq_fourierChar_neg_trace
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_NumberField_AdelicBox_integralFiniteAdeles_subset_closure_range_algebraMap_ringOfIntegers

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_NumberField_AdelicFourier_forall_addChar_finitePart_mul_eq_one_iff_mem_traceDual

open NumberField NumberField.AdelicFourier NumberField.AdelicBox AutomorphicForm IsDedekindDomain MeasureTheory
open scoped Classical FourierTransform nonZeroDivisors

noncomputable section

theorem solution
    (F : Type) [Field F] [NumberField F]
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    (hψ_inf : ∀ x : InfiniteAdeleRing F,
        ψ (x, 0) = (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
          (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ))
    (ξ : F) :
    (∀ z ∈ integralFiniteAdeles (𝓞 F) F,
        ψ (0, algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ * z) = 1)
      ↔ ξ ∈ (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F) : FractionalIdeal (𝓞 F)⁰ F) := by
  set ιξ := algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ
  have hιO : ∀ α : 𝓞 F, algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) α
      ∈ integralFiniteAdeles (𝓞 F) F := fun α v =>
    algebraMap_mem_adicCompletionIntegers (𝓞 F) F v α
  have hιcompat : ∀ α : 𝓞 F,
      algebraMap F (FiniteAdeleRing (𝓞 F) F) (α : F)
        = algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) α := fun α =>
    (IsScalarTower.algebraMap_apply (𝓞 F) F (FiniteAdeleRing (𝓞 F) F) α).symm

  have hfc : ∀ t : ℝ, (↑(Real.fourierChar t) : ℂ) = 1 ↔ ∃ n : ℤ, t = n := by
    intro t
    rw [show ((1 : ℂ) = ((1 : Circle) : ℂ)) from rfl, Circle.coe_inj,
      Real.fourierChar_apply', Circle.exp_eq_one]
    have h2π : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    constructor
    · rintro ⟨n, hn⟩
      refine ⟨n, mul_left_cancel₀ h2π ?_⟩
      linarith [hn]
    · rintro ⟨n, rfl⟩
      exact ⟨n, by ring⟩
  have h1ne : (1 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := one_ne_zero
  constructor
  · intro h
    rw [FractionalIdeal.mem_dual h1ne]
    intro a ha
    obtain ⟨α, hα⟩ := (FractionalIdeal.mem_one_iff _).mp ha
    subst hα
    rw [Algebra.traceForm_apply]
    have hval : ψ (0, ιξ * algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) α) = 1 := h _ (hιO α)
    rw [← hιcompat, ← map_mul,
      NumberField.AdelicFourier.addChar_zero_finitePart_algebraMap_eq_fourierChar_neg_trace
        F hψ hψ_inf (ξ * (α : F))] at hval
    obtain ⟨n, hn⟩ := (hfc _).mp hval
    refine ⟨-n, ?_⟩
    have : ((Algebra.trace ℚ F (ξ * (α : F)) : ℚ) : ℝ) = ((-n : ℤ) : ℝ) := by
      push_cast; linarith
    exact_mod_cast this.symm
  · intro hξ z hz
    have hχ_cont : Continuous (fun w : FiniteAdeleRing (𝓞 F) F => ψ (0, ιξ * w)) := by
      have : Continuous (fun w : FiniteAdeleRing (𝓞 F) F => ((0, ιξ * w) : AdeleRing (𝓞 F) F)) :=
        continuous_const.prodMk (continuous_const.mul continuous_id)
      exact hψ.continuous.comp this
    set K : Set (FiniteAdeleRing (𝓞 F) F) := {w | ψ (0, ιξ * w) = 1}
    have hK_closed : IsClosed K := isClosed_eq hχ_cont continuous_const
    have hιO_K : Set.range (algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F)) ⊆ K := by
      rintro _ ⟨α, rfl⟩
      show ψ (0, ιξ * algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) α) = 1
      rw [← hιcompat, ← map_mul,
        NumberField.AdelicFourier.addChar_zero_finitePart_algebraMap_eq_fourierChar_neg_trace
          F hψ hψ_inf (ξ * (α : F))]
      have htr : Algebra.trace ℚ F (ξ * (α : F)) ∈ (algebraMap ℤ ℚ).range := by
        have := (FractionalIdeal.mem_dual h1ne).mp hξ (α : F)
          ((FractionalIdeal.mem_one_iff _).mpr ⟨α, rfl⟩)
        rwa [Algebra.traceForm_apply] at this
      obtain ⟨n, hn⟩ := htr
      refine (hfc _).mpr ⟨-n, ?_⟩
      have : (algebraMap ℤ ℚ) n = (n : ℚ) := by simp [eq_intCast]
      rw [← hn, this]; push_cast; ring
    have hdense := integralFiniteAdeles_subset_closure_range_algebraMap_ringOfIntegers F
    exact hK_closed.closure_subset_iff.mpr hιO_K (hdense hz)
