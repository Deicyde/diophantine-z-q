/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_NumberField_AdelicFourier_forall_addChar_finitePart_mul_eq_one_iff_exists_mem_traceDual (git blob ae9d241e4e4e6461dafeb427ab72fdf84bfc9bca, sha256 e3bb7d1d5f7336296c98a6a117de2cb21c4a9281c037d655d3412d386a1091c0).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicFourier
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicBox
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_WhittakerCoefficient
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_NumberField_AdelicFourier_forall_addChar_finitePart_mul_eq_one_iff_mem_traceDual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_NumberField_AdelicFourier_forall_addChar_finitePart_mul_eq_one_iff_exists_mem_traceDual

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open _root_.NumberField
namespace NumberField
end NumberField
open _root_.P2MW.S_NumberField_AdelicFourier_forall_addChar_finitePart_mul_eq_one_iff_exists_mem_traceDual.NumberField
open _root_.NumberField.AdelicFourier
namespace NumberField.AdelicFourier
end NumberField.AdelicFourier
open _root_.P2MW.S_NumberField_AdelicFourier_forall_addChar_finitePart_mul_eq_one_iff_exists_mem_traceDual.NumberField.AdelicFourier
open _root_.NumberField.AdelicBox
open _root_.AutomorphicForm
open _root_.IsDedekindDomain
open _root_.MeasureTheory

open scoped Classical nonZeroDivisors

namespace NumberField
export _root_.NumberField (InfiniteAdeleRing mixedEmbedding mixedEmbedding.mixedSpace InfiniteAdeleRing.ringEquiv_mixedSpace AdeleRing)
namespace AdelicFourier
export _root_.NumberField.AdelicFourier (forall_addChar_finitePart_mul_eq_one_iff_mem_traceDual)
namespace Ws25ANN
open _root_.NumberField.AdelicFourier
open _root_.NumberField

variable (F : Type) [Field F] [NumberField F]

theorem mul_apply (u z : FiniteAdeleRing (𝓞 F) F) (v : HeightOneSpectrum (𝓞 F)) :
    (u * z) v = u v * z v := rfl

theorem neg_apply (u : FiniteAdeleRing (𝓞 F) F) (v : HeightOneSpectrum (𝓞 F)) :
    (-u) v = -(u v) := rfl

theorem mul_mem_integralFiniteAdeles {u z : FiniteAdeleRing (𝓞 F) F}
    (hu : u ∈ integralFiniteAdeles (𝓞 F) F) (hz : z ∈ integralFiniteAdeles (𝓞 F) F) :
    u * z ∈ integralFiniteAdeles (𝓞 F) F :=
  fun v => by rw [mul_apply]; exact mul_mem (hu v) (hz v)

theorem neg_mem_integralFiniteAdeles {u : FiniteAdeleRing (𝓞 F) F}
    (hu : u ∈ integralFiniteAdeles (𝓞 F) F) : -u ∈ integralFiniteAdeles (𝓞 F) F :=
  fun v => by rw [neg_apply]; exact neg_mem (hu v)

variable {F} in

theorem addChar_zero_add (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (a b : FiniteAdeleRing (𝓞 F) F) :
    ψ (0, a + b) = ψ (0, a) * ψ (0, b) := by
  rw [← AddChar.map_add_eq_mul]
  congr 1
  exact Prod.ext (add_zero (0 : InfiniteAdeleRing F)).symm rfl

theorem ann_impl {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    (hψ_inf : ∀ x : InfiniteAdeleRing F,
        ψ (x, 0) = (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
          (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ))
    (w : FiniteAdeleRing (𝓞 F) F) :
    (∀ z ∈ integralFiniteAdeles (𝓞 F) F, ψ (0, w * z) = 1)
      ↔ ∃ r : F, r ∈ (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F) : FractionalIdeal (𝓞 F)⁰ F)
          ∧ w - algebraMap F (FiniteAdeleRing (𝓞 F) F) r ∈ integralFiniteAdeles (𝓞 F) F := by

  have ker := fun ξ : F => forall_addChar_finitePart_mul_eq_one_iff_mem_traceDual F hψ hψ_inf ξ
  have h1 : (1 : F) ∈ (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F) :
      FractionalIdeal (𝓞 F)⁰ F) :=
    FractionalIdeal.one_le_dual_one (A := ℤ) (K := ℚ) (FractionalIdeal.one_mem_one _)
  have hO : ∀ z ∈ integralFiniteAdeles (𝓞 F) F, ψ (0, z) = 1 := fun z hz => by
    simpa only [map_one, one_mul] using (ker 1).mpr h1 z hz
  set ι := algebraMap F (FiniteAdeleRing (𝓞 F) F) with hι
  constructor
  · intro h
    obtain ⟨k, hk⟩ := exists_algebraMap_add_mem_integralFiniteAdeles (𝓞 F) F w
    refine ⟨-k, ?_, ?_⟩
    · refine (ker (-k)).mp fun z hz => ?_

      have hsplit : ι (-k) * z = w * z + (-(ι k + w)) * z := by rw [map_neg]; ring
      rw [hsplit, addChar_zero_add, h z hz, one_mul]
      exact hO _ (mul_mem_integralFiniteAdeles F (neg_mem_integralFiniteAdeles F hk) hz)
    · have : w - ι (-k) = ι k + w := by rw [map_neg, sub_neg_eq_add, add_comm]
      rw [this]; exact hk
  · rintro ⟨r, hr, hu⟩ z hz
    have hsplit : w * z = ι r * z + (w - ι r) * z := by ring
    rw [hsplit, addChar_zero_add, (ker r).mpr hr z hz, one_mul]
    exact hO _ (mul_mem_integralFiniteAdeles F hu hz)

end NumberField.AdelicFourier.Ws25ANN

end

open _root_.NumberField
namespace NumberField
end NumberField
open _root_.P2MW.S_NumberField_AdelicFourier_forall_addChar_finitePart_mul_eq_one_iff_exists_mem_traceDual.NumberField
open _root_.NumberField.AdelicFourier
namespace NumberField.AdelicFourier
end NumberField.AdelicFourier
open _root_.P2MW.S_NumberField_AdelicFourier_forall_addChar_finitePart_mul_eq_one_iff_exists_mem_traceDual.NumberField.AdelicFourier
open _root_.NumberField.AdelicBox
open _root_.AutomorphicForm
open _root_.IsDedekindDomain
open _root_.MeasureTheory
open scoped Classical FourierTransform nonZeroDivisors

theorem solution
    (F : Type) [Field F] [NumberField F]
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    (hψ_inf : ∀ x : InfiniteAdeleRing F,
        ψ (x, 0) = (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
          (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ))
    (w : FiniteAdeleRing (𝓞 F) F) :
    (∀ z ∈ integralFiniteAdeles (𝓞 F) F, ψ (0, w * z) = 1)
      ↔ ∃ r : F, r ∈ (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F) : FractionalIdeal (𝓞 F)⁰ F)
          ∧ w - algebraMap F (FiniteAdeleRing (𝓞 F) F) r ∈ integralFiniteAdeles (𝓞 F) F :=
  NumberField.AdelicFourier.Ws25ANN.ann_impl F hψ hψ_inf w
