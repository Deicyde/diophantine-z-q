/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_NumberField_AdelicFourier_addChar_zero_finitePart_algebraMap_eq_fourierChar_neg_trace (git blob 52c284c2d6571863bce83a973bf083cf8ed3580d, sha256 b7bf25d9796ecce086bbe96eb82500e8879ee7fa6c01164f599ec9177c9fd9b9).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicFourier
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicBox
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.Algebra.Module.ZLattice.Covolume
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_NumberField_mixedEmbedding_trace_mixedEmbedding

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_NumberField_AdelicFourier_addChar_zero_finitePart_algebraMap_eq_fourierChar_neg_trace

open NumberField NumberField.AdelicFourier NumberField.AdelicBox AutomorphicForm IsDedekindDomain MeasureTheory
open scoped Classical FourierTransform nonZeroDivisors

noncomputable section

theorem solution
    (F : Type) [Field F] [NumberField F]
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    (hψ_inf : ∀ x : InfiniteAdeleRing F,
        ψ (x, 0) = (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
          (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ))
    (q : F) :
    ψ (0, algebraMap F (FiniteAdeleRing (𝓞 F) F) q)
      = (Real.fourierChar (-((Algebra.trace ℚ F q : ℚ) : ℝ)) : ℂ) := by

  have hιq : algebraMap F (AdeleRing (𝓞 F) F) q
      = (algebraMap F (InfiniteAdeleRing F) q, algebraMap F (FiniteAdeleRing (𝓞 F) F) q) := rfl

  have hsplit : ψ (algebraMap F (AdeleRing (𝓞 F) F) q)
      = ψ (algebraMap F (InfiniteAdeleRing F) q, 0)
        * ψ (0, algebraMap F (FiniteAdeleRing (𝓞 F) F) q) := by
    rw [hιq, ← AddChar.map_add_eq_mul]
    congr 1
    exact Prod.ext (add_zero _).symm (zero_add _).symm

  have hPI : ψ (algebraMap F (AdeleRing (𝓞 F) F) q) = 1 := hψ.principalInvariant q

  have harch : ψ (algebraMap F (InfiniteAdeleRing F) q, 0)
      = (Real.fourierChar ((Algebra.trace ℚ F q : ℚ) : ℝ) : ℂ) := by
    rw [hψ_inf, ← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp,
      NumberField.mixedEmbedding.trace_mixedEmbedding]
  rw [hPI, harch] at hsplit

  have hne : (Real.fourierChar ((Algebra.trace ℚ F q : ℚ) : ℝ) : ℂ) ≠ 0 :=
    Circle.coe_ne_zero _
  have hx : ψ (0, algebraMap F (FiniteAdeleRing (𝓞 F) F) q)
      = (Real.fourierChar ((Algebra.trace ℚ F q : ℚ) : ℝ) : ℂ)⁻¹ :=
    eq_inv_of_mul_eq_one_right hsplit.symm
  rw [hx, ← Circle.coe_inv, ← AddChar.map_neg_eq_inv]
