/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_lintegral_rationalCentreUnipotentHaar_comp_heckeGen_mul_centralScalar_conj (git blob 443882d23e82314711b1a579e7252c0ad97302b2, sha256 839277efabea85c12dcc8c03795b74282457b44f537e1bc5eeb69877d7130ebd).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_RationalCentreUnipotentQuotient
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicLevel
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_lintegral_rationalCentreUnipotentHaar_comp_heckeGen_mul_centralScalar_conj

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel AutomorphicForm IsDedekindDomain
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

theorem AutomorphicForm.lintegral_rationalCentreUnipotentHaar_comp_heckeGen_mul_centralScalar_conj
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (u : (AdeleRing (𝓞 K) K)ˣ)
    (hb : ∀ y : AdelicGL2 (𝓞 K) K, y ∈ rationalCentreUnipotent K ↔
      (heckeGen (𝓞 K) K v * centralScalar (𝓞 K) K u) * y * (heckeGen (𝓞 K) K v * centralScalar (𝓞 K) K u)⁻¹ ∈
        rationalCentreUnipotent K)
    (F : rationalCentreUnipotent K → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ x, F ⟨(heckeGen (𝓞 K) K v * centralScalar (𝓞 K) K u) * (x : AdelicGL2 (𝓞 K) K) *
        (heckeGen (𝓞 K) K v * centralScalar (𝓞 K) K u)⁻¹, (hb (x : AdelicGL2 (𝓞 K) K)).mp x.2⟩
      ∂(rationalCentreUnipotentHaar K) =
      (Ideal.absNorm v.asIdeal : ℝ≥0∞) * ∫⁻ x, F x ∂(rationalCentreUnipotentHaar K) := by
  revert K v u hb F hF
  exact @_root_.P2MW.S_AutomorphicForm_lintegral_rationalCentreUnipotentHaar_comp_heckeGen_mul_centralScalar_conj.solution
