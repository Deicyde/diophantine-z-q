/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_isFundamentalDomain_boxSheet_rationalCentreUnipotent (git blob a13631a05ce6fbc47ef0164bf987ef0a6e29ff0c, sha256 8d18e9d6da29173832354654beba59eef73c8c4d265e578e4ed09f98b1576710).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_RationalTorusUnipotentQuotient
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_BorelSubgroup
import Mathlib.MeasureTheory.Group.FundamentalDomain
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_isFundamentalDomain_boxSheet_rationalCentreUnipotent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicLevel AutomorphicForm
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

theorem AutomorphicForm.isFundamentalDomain_boxSheet_rationalCentreUnipotent
    (K : Type) [Field K] [NumberField K] :
    let P : Subgroup (AdelicGL2 (𝓞 K) K) :=
      rationalCentre K ⊔ ((globalPoints (𝓞 K) K).comp (unipotentGL2Hom (R := K))).range
    let T : Set (rationalCentreUnipotent K) :=
      (fun u : AdeleRing (𝓞 K) K => Subgroup.inclusion le_sup_right (toAdelicUnipotent K u)) '' adelicBox K
    P ≤ rationalCentreUnipotent K ∧ Countable P ∧ MeasurableSet T ∧
    IsFundamentalDomain (P.subgroupOf (rationalCentreUnipotent K)) T (rationalCentreUnipotentHaar K) ∧
    ∀ F : rationalCentreUnipotent K → ℝ≥0∞, Measurable F →
      ∫⁻ x in T, F x ∂(rationalCentreUnipotentHaar K) =
        ∫⁻ u in adelicBox K, F (Subgroup.inclusion le_sup_right (toAdelicUnipotent K u))
          ∂(((adelicAddHaar (𝓞 K) K) (adelicBox K))⁻¹ • adelicAddHaar (𝓞 K) K) := by
  revert K
  exact @_root_.P2MW.S_AutomorphicForm_isFundamentalDomain_boxSheet_rationalCentreUnipotent.solution
