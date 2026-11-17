/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NumberField_AdelicHaar_exists_integral_glArch_mul_glFin_eq_mul_integral_mul_integral (git blob 5c440dcd77b9c9fb9cbdbd15f97b9921902ecf44, sha256 4379972da0d9ffe251f1b6d0043bd4d5ab4a20a09c7f84c74c80709053085720).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicLevel
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicHaar
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_NumberField_AdelicHaar_exists_integral_glArch_mul_glFin_eq_mul_integral_mul_integral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory NumberField.AdelicLevel NumberField.AdelicHaar
open scoped NNReal

theorem NumberField.AdelicHaar.exists_integral_glArch_mul_glFin_eq_mul_integral_mul_integral
    (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (GL (Fin 2) (InfiniteAdeleRing K))] [BorelSpace (GL (Fin 2) (InfiniteAdeleRing K))]
    [MeasurableSpace (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))] [BorelSpace (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))]
    (μa : Measure (GL (Fin 2) (InfiniteAdeleRing K))) [μa.IsHaarMeasure] [μa.Regular]
    (μf : Measure (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))) [μf.IsHaarMeasure] [μf.Regular] :
    ∃ c : ℝ≥0, 0 < c ∧ ∀ (Φ : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (Ψ : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ),
      (letI := glBorel (Fin 2) (𝓞 K) K
       ∫ x, Φ (glArch (𝓞 K) K x) * Ψ (glFin (𝓞 K) K x) ∂(adelicGLHaar (Fin 2) (𝓞 K) K))
        = (c : ℂ) * ((∫ a, Φ a ∂μa) * ∫ b, Ψ b ∂μf) := by
  revert K μa μf
  exact @_root_.P2MW.S_NumberField_AdelicHaar_exists_integral_glArch_mul_glFin_eq_mul_integral_mul_integral.solution
