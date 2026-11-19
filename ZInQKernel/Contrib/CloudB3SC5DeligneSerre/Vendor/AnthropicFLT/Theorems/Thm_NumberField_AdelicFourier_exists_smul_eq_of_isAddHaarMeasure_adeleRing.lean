/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NumberField_AdelicFourier_exists_smul_eq_of_isAddHaarMeasure_adeleRing (git blob e36009a138e06e4a1cf5db90447e2e7e550ef244, sha256 00a2ba4cccffc84a8d46aa0b0c562fef209fd2e1f2dc873669ffab3736a3a597).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicHaar
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_NumberField_AdelicFourier_exists_smul_eq_of_isAddHaarMeasure_adeleRing

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open NumberField
theorem NumberField.AdelicFourier.exists_smul_eq_of_isAddHaarMeasure_adeleRing (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ ν : MeasureTheory.Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure] :
    ∃ c : NNReal, 0 < c ∧ μ = c • ν := by
  revert F μ ν
  exact @_root_.P2MW.S_NumberField_AdelicFourier_exists_smul_eq_of_isAddHaarMeasure_adeleRing.solution
