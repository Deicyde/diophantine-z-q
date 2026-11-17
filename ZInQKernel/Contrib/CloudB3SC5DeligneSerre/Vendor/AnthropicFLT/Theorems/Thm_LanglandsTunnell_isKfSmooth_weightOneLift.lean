/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_LanglandsTunnell_isKfSmooth_weightOneLift (git blob a206552169553efa7a86f02a6733f15c7a819581, sha256 9aac90be3ec16c94667010a038a01434d76fced9144b308a8dd4fe0e55230e25).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_DihedralWeightOneLift
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_LanglandsTunnell_isKfSmooth_weightOneLift

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open NumberField AutomorphicForm UpperHalfPlane DihedralWeightOne
open scoped ModularForm MatrixGroups

theorem LanglandsTunnell.isKfSmooth_weightOneLift
    {n : ℕ} (hn : n ≠ 0) (f : ℍ → ℂ)
    (hf : ∀ ε : SL(2, ℤ), ε ∈ CongruenceSubgroup.Gamma1 n → f ∣[(1 : ℤ)] (ε : GL (Fin 2) ℝ) = f) :
    IsKfSmooth ℚ (weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f) := by
  revert n hn f hf
  exact @_root_.P2MW.S_LanglandsTunnell_isKfSmooth_weightOneLift.solution
