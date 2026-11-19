/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_integral_rationalTorusUnipotentQuotient_tsum_units_eq_integral_rationalCentreUnipotentQuotient (git blob be83b63d80feff506e6a67fb7f9aca3511c59573, sha256 547a3a5a0faa6f95bbbbe2e72df79db35c38761da714fdc8c43282637e01e836).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_RationalTorusUnipotentQuotient
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_BorelSubgroup
import Mathlib.MeasureTheory.Group.FundamentalDomain
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_integral_rationalTorusUnipotentQuotient_tsum_units_eq_integral_rationalCentreUnipotentQuotient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicLevel open AutomorphicForm hiding existsUnique_diagOne_inv_mul_mem_scalar_sup_unipotent_of_mem_borelSubgroup isFundamentalDomain_boxSheet_rationalCentreUnipotent isFundamentalDomain_boxSheet_rationalTorusUnipotent
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

theorem AutomorphicForm.integral_rationalTorusUnipotentQuotient_tsum_units_eq_integral_rationalCentreUnipotentQuotient
    (F : Type) [Field F] [NumberField F]
    (𝓕B : Set (AdelicGL2 (𝓞 F) F))
    (h𝓕B : IsFundamentalDomain ((borelSubgroup F).map (globalPoints (𝓞 F) F)) 𝓕B (adelicGLHaar (Fin 2) (𝓞 F) F))
    (k : AdelicGL2 (𝓞 F) F → ℂ) (hk : Measurable k)
    (hkH : ∀ h ∈ rationalCentreUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, k (h * g) = k g)
    (hfin : ∫⁻ g in 𝓕B, ∑' a : Fˣ, ‖k (globalPoints (𝓞 F) F (diagOne a) * g)‖ₑ
      ∂(adelicGLHaar (Fin 2) (𝓞 F) F) < ∞) :
    Integrable (fun q : RationalCentreUnipotentQuotient F => k q.out) (rationalCentreUnipotentQuotientMeasure F) ∧
    Integrable (fun q : RationalTorusUnipotentQuotient F => ∑' a : Fˣ, k (globalPoints (𝓞 F) F (diagOne a) * q.out))
      (rationalTorusUnipotentQuotientMeasure F) ∧
    ∫ q : RationalTorusUnipotentQuotient F, ∑' a : Fˣ, k (globalPoints (𝓞 F) F (diagOne a) * q.out)
        ∂(rationalTorusUnipotentQuotientMeasure F) =
      ∫ g in 𝓕B, ∑' a : Fˣ, k (globalPoints (𝓞 F) F (diagOne a) * g) ∂(adelicGLHaar (Fin 2) (𝓞 F) F) ∧
    ∫ g in 𝓕B, ∑' a : Fˣ, k (globalPoints (𝓞 F) F (diagOne a) * g) ∂(adelicGLHaar (Fin 2) (𝓞 F) F) =
      ∫ q : RationalCentreUnipotentQuotient F, k q.out ∂(rationalCentreUnipotentQuotientMeasure F) := by
  revert F 𝓕B h𝓕B k hk hkH hfin
  exact @_root_.P2MW.S_AutomorphicForm_integral_rationalTorusUnipotentQuotient_tsum_units_eq_integral_rationalCentreUnipotentQuotient.solution
