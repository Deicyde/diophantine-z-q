/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_isFactorizableTestFn_comp_inv_mul (git blob 0cb81d3b6985a15c237e2f2e75ea55d95ebb0e25, sha256 8238d2ef793f5e66bb8e79cd4843d5de9bd7235840993c6d7ef7a3d3b184f1c1).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CuspidalConstituent
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_isFactorizableTestFn_comp_inv_mul

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open MeasureTheory NumberField AutomorphicForm AutomorphicForm.CuspidalConstituent
open scoped BigOperators

theorem AutomorphicForm.isFactorizableTestFn_comp_inv_mul
    (F : Type) [Field F] [NumberField F] (tys : ArchTypeFamily F)
    {f : AdelicGL2 (𝓞 F) F → ℂ} (hf : IsFactorizableTestFn F f) (hbf : IsArchBiFinite F tys f)
    {g : AdelicGL2 (𝓞 F) F} (hg : g ∈ finiteAdelicGL2Subgroup F)
    {k : AdelicGL2 (𝓞 F) F} (hk : k ∈ (⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range)) :
    IsFactorizableTestFn F (fun z => f ((g * k)⁻¹ * z)) ∧ IsArchBiFinite F tys (fun z => f ((g * k)⁻¹ * z)) := by
  revert F tys f hf hbf g hg k hk
  exact @_root_.P2MW.S_AutomorphicForm_isFactorizableTestFn_comp_inv_mul.solution
