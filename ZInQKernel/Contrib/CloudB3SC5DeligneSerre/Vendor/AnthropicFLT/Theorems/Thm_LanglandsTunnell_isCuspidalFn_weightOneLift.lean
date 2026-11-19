/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_LanglandsTunnell_isCuspidalFn_weightOneLift (git blob c43b7bba373fee4d069d765126e949bf5c63eb86, sha256 025d9445d9a284e305fc3d2f4a91ded67723c221eed4c0c15fe3ee90af1843aa).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_DihedralWeightOneLift
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_LanglandsTunnell_isCuspidalFn_weightOneLift

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open NumberField AutomorphicForm UpperHalfPlane DihedralWeightOne
open scoped ModularForm MatrixGroups Manifold

theorem LanglandsTunnell.isCuspidalFn_weightOneLift
    {n : ℕ} (hn : n ≠ 0) (f : ℍ → ℂ)
    (hf_hol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hf : ∀ ε : SL(2, ℤ), ε ∈ CongruenceSubgroup.Gamma1 n → f ∣[(1 : ℤ)] (ε : GL (Fin 2) ℝ) = f)
    (C : ℝ) (hC : ∀ τ : ℍ, ‖f τ‖ ≤ C / τ.im ^ (((1 : ℤ) : ℝ) / 2))
    (hzero : ∀ δ : SL(2, ℤ), IsZeroAtImInfty (f ∣[(1 : ℤ)] (δ : GL (Fin 2) ℝ))) :
    @IsCuspidalFn _ (productionPinsCompact ℚ).nS _ _ (productionPinsCompact ℚ).ν unipotentGL2
      (weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f) := by
  revert n hn f hf_hol hf C hC hzero
  exact @_root_.P2MW.S_LanglandsTunnell_isCuspidalFn_weightOneLift.solution
