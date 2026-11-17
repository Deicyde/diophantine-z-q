/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_NumberField_AdelicFourier_forall_addChar_finitePart_mul_eq_one_of_forall_iff_mem_integralFiniteAdeles (git blob 50243b8e87fcb4c6f2e31fff603273d4ddc33113, sha256 8312f634ec9a3c623d129ee4bf97ea14d6bd54ceef267297da030caecdfb0b4b).
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

namespace P2MW.S_NumberField_AdelicFourier_forall_addChar_finitePart_mul_eq_one_of_forall_iff_mem_integralFiniteAdeles

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open _root_.NumberField
namespace NumberField
end NumberField
open _root_.P2MW.S_NumberField_AdelicFourier_forall_addChar_finitePart_mul_eq_one_of_forall_iff_mem_integralFiniteAdeles.NumberField
open _root_.NumberField.AdelicFourier
namespace NumberField.AdelicFourier
end NumberField.AdelicFourier
open _root_.P2MW.S_NumberField_AdelicFourier_forall_addChar_finitePart_mul_eq_one_of_forall_iff_mem_integralFiniteAdeles.NumberField.AdelicFourier
open _root_.NumberField.AdelicBox
open _root_.AutomorphicForm
open _root_.IsDedekindDomain
open _root_.MeasureTheory

open scoped Classical FourierTransform nonZeroDivisors

namespace NumberField
export _root_.NumberField (InfiniteAdeleRing mixedEmbedding mixedEmbedding.mixedSpace InfiniteAdeleRing.ringEquiv_mixedSpace AdeleRing AdelicFourier.forall_addChar_finitePart_mul_eq_one_iff_mem_traceDual)
namespace AdelicFourier
export _root_.NumberField.AdelicFourier (forall_addChar_finitePart_mul_eq_one_iff_mem_traceDual)
namespace Ws25
namespace Biann
open _root_.NumberField.AdelicFourier
open _root_.NumberField

variable {F : Type} [Field F] [NumberField F]

theorem add_mem_integralFiniteAdeles {y z : FiniteAdeleRing (𝓞 F) F}
    (hy : y ∈ integralFiniteAdeles (𝓞 F) F) (hz : z ∈ integralFiniteAdeles (𝓞 F) F) :
    y + z ∈ integralFiniteAdeles (𝓞 F) F := fun v => add_mem (hy v) (hz v)

theorem mul_mem_integralFiniteAdeles {y z : FiniteAdeleRing (𝓞 F) F}
    (hy : y ∈ integralFiniteAdeles (𝓞 F) F) (hz : z ∈ integralFiniteAdeles (𝓞 F) F) :
    y * z ∈ integralFiniteAdeles (𝓞 F) F := fun v => mul_mem (hy v) (hz v)

theorem algebraMap_coe_mem_integralFiniteAdeles (q : 𝓞 F) :
    algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F q) ∈ integralFiniteAdeles (𝓞 F) F :=
  fun v => algebraMap_mem_adicCompletionIntegers (𝓞 F) F v q

def finitePart (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) : AddChar (FiniteAdeleRing (𝓞 F) F) ℂ :=
  ψ.compAddMonoidHom (AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))

@[scoped simp] theorem finitePart_apply (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (x : FiniteAdeleRing (𝓞 F) F) : finitePart ψ x = ψ (0, x) := rfl

theorem apply_zero_add (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (a b : FiniteAdeleRing (𝓞 F) F) :
    ψ (0, a + b) = ψ (0, a) * ψ (0, b) := by
  rw [← finitePart_apply, ← finitePart_apply, ← finitePart_apply, AddChar.map_add_eq_mul]

def annih (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) : Set (FiniteAdeleRing (𝓞 F) F) :=
  {w | ∀ z ∈ integralFiniteAdeles (𝓞 F) F, ψ (0, w * z) = 1}

theorem mem_annih {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} {w : FiniteAdeleRing (𝓞 F) F} :
    w ∈ annih ψ ↔ ∀ z ∈ integralFiniteAdeles (𝓞 F) F, ψ (0, w * z) = 1 := Iff.rfl

theorem mul_mem_annih {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} {w z : FiniteAdeleRing (𝓞 F) F}
    (hw : w ∈ annih ψ) (hz : z ∈ integralFiniteAdeles (𝓞 F) F) : w * z ∈ annih ψ :=
  fun z' hz' => by rw [mul_assoc]; exact hw _ (mul_mem_integralFiniteAdeles hz hz')

theorem apply_zero_mul_eq_one_of_mem {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ}
    {u w : FiniteAdeleRing (𝓞 F) F} (hu : u ∈ integralFiniteAdeles (𝓞 F) F)
    (hw : w ∈ annih ψ) : ψ (0, u * w) = 1 := by
  rw [mul_comm]; exact hw u hu

theorem mem_one_of_forall_mul_mem {I : FractionalIdeal (𝓞 F)⁰ F} (hI : I ≠ 0) {q : F}
    (hq : ∀ r ∈ I, q * r ∈ I) : q ∈ (1 : FractionalIdeal (𝓞 F)⁰ F) := by
  have hle : FractionalIdeal.spanSingleton (𝓞 F)⁰ q * I ≤ I :=
    FractionalIdeal.spanSingleton_mul_le_iff.mpr hq
  have hle' : FractionalIdeal.spanSingleton (𝓞 F)⁰ q ≤ 1 := by
    calc FractionalIdeal.spanSingleton (𝓞 F)⁰ q
        = FractionalIdeal.spanSingleton (𝓞 F)⁰ q * I * I⁻¹ := by
          rw [mul_assoc, mul_inv_cancel₀ hI, mul_one]
      _ ≤ I * I⁻¹ := by
          first
          | exact mul_le_mul' hle le_rfl
          | exact mul_le_mul_left hle _
          | exact mul_le_mul_left hle _
      _ = 1 := mul_inv_cancel₀ hI
  exact hle' (FractionalIdeal.mem_spanSingleton_self (S := (𝓞 F)⁰) q)

theorem forall_iff_mem
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    (hψ_inf : ∀ x : InfiniteAdeleRing F,
        ψ (x, 0) = (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
          (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ))
    (u : FiniteAdeleRing (𝓞 F) F) :
    (∀ w : FiniteAdeleRing (𝓞 F) F,
        (∀ z ∈ integralFiniteAdeles (𝓞 F) F, ψ (0, w * z) = 1) → ψ (0, u * w) = 1)
      ↔ u ∈ integralFiniteAdeles (𝓞 F) F := by

  have hdual := NumberField.AdelicFourier.forall_addChar_finitePart_mul_eq_one_iff_mem_traceDual
    F hψ hψ_inf
  set D : FractionalIdeal (𝓞 F)⁰ F :=
    FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F) with hD
  have hD0 : D ≠ 0 := FractionalIdeal.dual_ne_zero (A := ℤ) (K := ℚ) one_ne_zero
  constructor
  · intro h

    obtain ⟨k, hk⟩ := exists_algebraMap_add_mem_integralFiniteAdeles (𝓞 F) F u
    set q : F := -k with hq
    set u₀ := algebraMap F (FiniteAdeleRing (𝓞 F) F) k + u with hu₀
    have hu : u = algebraMap F (FiniteAdeleRing (𝓞 F) F) q + u₀ := by
      rw [hu₀, hq, map_neg]; abel

    have hqA : ∀ w ∈ annih ψ, ψ (0, algebraMap F (FiniteAdeleRing (𝓞 F) F) q * w) = 1 := by
      intro w hw
      have h1 : ψ (0, u * w) = 1 := h w hw
      rw [hu, add_mul, apply_zero_add, apply_zero_mul_eq_one_of_mem hk hw, mul_one] at h1
      exact h1

    have hqD : ∀ r ∈ D, q * r ∈ D := by
      intro r hr
      have hrA : algebraMap F (FiniteAdeleRing (𝓞 F) F) r ∈ annih ψ := (hdual r).mpr hr
      refine (hdual (q * r)).mp fun z hz => ?_
      have := hqA _ (mul_mem_annih hrA hz)
      rwa [← mul_assoc, ← map_mul] at this

    obtain ⟨q', hq'⟩ := (FractionalIdeal.mem_one_iff (S := (𝓞 F)⁰)).mp (mem_one_of_forall_mul_mem hD0 hqD)
    rw [hu, ← hq']
    exact add_mem_integralFiniteAdeles (algebraMap_coe_mem_integralFiniteAdeles q') hk
  · intro hu w hw
    exact apply_zero_mul_eq_one_of_mem hu hw

end NumberField.AdelicFourier.Ws25.Biann
open scoped _root_.P2MW.S_NumberField_AdelicFourier_forall_addChar_finitePart_mul_eq_one_of_forall_iff_mem_integralFiniteAdeles.NumberField _root_.P2MW.S_NumberField_AdelicFourier_forall_addChar_finitePart_mul_eq_one_of_forall_iff_mem_integralFiniteAdeles.NumberField.AdelicFourier _root_.P2MW.S_NumberField_AdelicFourier_forall_addChar_finitePart_mul_eq_one_of_forall_iff_mem_integralFiniteAdeles.NumberField.AdelicFourier.Ws25 _root_.P2MW.S_NumberField_AdelicFourier_forall_addChar_finitePart_mul_eq_one_of_forall_iff_mem_integralFiniteAdeles.NumberField.AdelicFourier.Ws25.Biann
open scoped _root_.P2MW.S_NumberField_AdelicFourier_forall_addChar_finitePart_mul_eq_one_of_forall_iff_mem_integralFiniteAdeles.NumberField _root_.P2MW.S_NumberField_AdelicFourier_forall_addChar_finitePart_mul_eq_one_of_forall_iff_mem_integralFiniteAdeles.NumberField.AdelicFourier _root_.P2MW.S_NumberField_AdelicFourier_forall_addChar_finitePart_mul_eq_one_of_forall_iff_mem_integralFiniteAdeles.NumberField.AdelicFourier.Ws25
open scoped _root_.P2MW.S_NumberField_AdelicFourier_forall_addChar_finitePart_mul_eq_one_of_forall_iff_mem_integralFiniteAdeles.NumberField _root_.P2MW.S_NumberField_AdelicFourier_forall_addChar_finitePart_mul_eq_one_of_forall_iff_mem_integralFiniteAdeles.NumberField.AdelicFourier
open scoped _root_.P2MW.S_NumberField_AdelicFourier_forall_addChar_finitePart_mul_eq_one_of_forall_iff_mem_integralFiniteAdeles.NumberField

open NumberField.AdelicFourier.Ws25.Biann in
theorem solution
    (F : Type) [Field F] [NumberField F]
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    (hψ_inf : ∀ x : InfiniteAdeleRing F,
        ψ (x, 0) = (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
          (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ))
    (u : FiniteAdeleRing (𝓞 F) F) :
    (∀ w : FiniteAdeleRing (𝓞 F) F,
        (∀ z ∈ integralFiniteAdeles (𝓞 F) F, ψ (0, w * z) = 1) → ψ (0, u * w) = 1)
      ↔ u ∈ integralFiniteAdeles (𝓞 F) F :=
  forall_iff_mem hψ hψ_inf u

end
open scoped _root_.P2MW.S_NumberField_AdelicFourier_forall_addChar_finitePart_mul_eq_one_of_forall_iff_mem_integralFiniteAdeles.NumberField _root_.P2MW.S_NumberField_AdelicFourier_forall_addChar_finitePart_mul_eq_one_of_forall_iff_mem_integralFiniteAdeles.NumberField.AdelicFourier _root_.P2MW.S_NumberField_AdelicFourier_forall_addChar_finitePart_mul_eq_one_of_forall_iff_mem_integralFiniteAdeles.NumberField.AdelicFourier.Ws25 _root_.P2MW.S_NumberField_AdelicFourier_forall_addChar_finitePart_mul_eq_one_of_forall_iff_mem_integralFiniteAdeles.NumberField.AdelicFourier.Ws25.Biann
