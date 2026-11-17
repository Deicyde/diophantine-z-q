/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_constantTerm_adelicBox_globalPoints_mul_of_mem_borelSubgroup (git blob f713970b8e026491e615872f12ed5078d39dda81, sha256 903325d368d4d15489231c849be5b52803e587002a3e8e92c576db605b33264b).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicBox
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ConstantTerm
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_AdelicLsXi
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_BorelSubgroup
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_constantTerm_adelicBox_globalPoints_mul_of_mem_borelSubgroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open NumberField
attribute [local instance] NumberField.AdelicHaar.adeleBorel
theorem AutomorphicForm.constantTerm_adelicBox_globalPoints_mul_of_mem_borelSubgroup
    (K : Type) [Field K] [NumberField K]
    {φ : AutomorphicForm.AdelicGL2 (𝓞 K) K → ℂ}
    (hφ : ∀ γ ∈ AutomorphicForm.borelSubgroup K, ∀ h : AutomorphicForm.AdelicGL2 (𝓞 K) K,
      φ (AutomorphicForm.globalPoints (𝓞 K) K γ * h) = φ h)
    {γ : Matrix.GeneralLinearGroup (Fin 2) K} (hγ : γ ∈ AutomorphicForm.borelSubgroup K)
    (g : AutomorphicForm.AdelicGL2 (𝓞 K) K) :
    AutomorphicForm.constantTerm
        (ProbabilityTheory.cond (AdelicHaar.adelicAddHaar (𝓞 K) K) (AdelicBox.adelicBox K))
        (fun x => AutomorphicForm.unipotentGL2 x) φ (AutomorphicForm.globalPoints (𝓞 K) K γ * g)
      = AutomorphicForm.constantTerm
          (ProbabilityTheory.cond (AdelicHaar.adelicAddHaar (𝓞 K) K) (AdelicBox.adelicBox K))
          (fun x => AutomorphicForm.unipotentGL2 x) φ g := by
  revert K φ hφ γ hγ g
  exact @_root_.P2MW.S_AutomorphicForm_constantTerm_adelicBox_globalPoints_mul_of_mem_borelSubgroup.solution
