/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_isFundamentalDomain_boxSheet_rationalTorusUnipotent (git blob dcecf87d1474e90247d7b6ac5af23c774cb2a7f2, sha256 766b6185049d1bfb47e6f7f6c149fcafaef67164ad6247dd9a87d997c5eb6e94).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_RationalTorusUnipotentQuotient
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_BorelSubgroup
import Mathlib.MeasureTheory.Group.FundamentalDomain
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_isFundamentalDomain_boxSheet_rationalTorusUnipotent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicLevel AutomorphicForm
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

theorem AutomorphicForm.isFundamentalDomain_boxSheet_rationalTorusUnipotent
    (K : Type) [Field K] [NumberField K] :
    let B : Subgroup (AdelicGL2 (𝓞 K) K) := (borelSubgroup K).map (globalPoints (𝓞 K) K)
    let T : Set (rationalTorusUnipotent K) :=
      (fun u : AdeleRing (𝓞 K) K => Subgroup.inclusion le_sup_right (toAdelicUnipotent K u)) '' adelicBox K
    B ≤ rationalTorusUnipotent K ∧ Countable B ∧ MeasurableSet T ∧
    IsFundamentalDomain (B.subgroupOf (rationalTorusUnipotent K)) T (rationalTorusUnipotentHaar K) ∧
    ∀ F : rationalTorusUnipotent K → ℝ≥0∞, Measurable F →
      ∫⁻ x in T, F x ∂(rationalTorusUnipotentHaar K) =
        ∫⁻ u in adelicBox K, F (Subgroup.inclusion le_sup_right (toAdelicUnipotent K u))
          ∂(((adelicAddHaar (𝓞 K) K) (adelicBox K))⁻¹ • adelicAddHaar (𝓞 K) K) := by
  revert K
  exact @_root_.P2MW.S_AutomorphicForm_isFundamentalDomain_boxSheet_rationalTorusUnipotent.solution
