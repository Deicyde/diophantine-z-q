/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_PadicAlgCl_norm_apply_sub_self_eq_of_isPrimitiveRoot_of_mem_fixingSubgroup
Modified for the Z-in-Q kernel (2026-11-16, p-divisible Hodge-Tate port): local import paths
are relocated, the P2M.Util elaborators are replaced by standard Lean commands or explicit terms,
local notations are expanded in place, and the upstream lakefile options are set as `set_option`
lines after the imports; see ZInQKernel/Contrib/CloudB3SC3PDivHodge/PORTING.md. Any other change is marked `-- [port]`.
Original copyright/attribution notices: NOTICE.upstream and ATTRIBUTION.upstream.md in
ZInQKernel/Contrib/CloudB3SC3PDivHodge/Vendor/AnthropicFLT/; license: LICENSE in that directory.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W11Cyclotomic.TowerDefinition
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.P2M.Sol.S_PadicAlgCl_norm_apply_sub_self_eq_of_isPrimitiveRoot_of_mem_fixingSubgroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

theorem PadicAlgCl.norm_apply_sub_self_eq_of_isPrimitiveRoot_of_mem_fixingSubgroup
    (p : ℕ) [inst_t1 : Fact p.Prime] {n k : ℕ} (hkn : k < n) {ζ : PadicAlgCl p}
    (hζ : IsPrimitiveRoot ζ (p ^ n)) (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (hσ : σ ∈ (PadicAlgCl.cyclotomicTower p k).fixingSubgroup)
    (hσ' : σ ∉ (PadicAlgCl.cyclotomicTower p (k + 1)).fixingSubgroup) :
    ‖ζ - 1‖ = (p : ℝ) ^ (-(1 : ℝ) / ((p ^ n).totient : ℝ)) ∧
      ‖σ ζ - ζ‖ = (p : ℝ) ^ (-(1 : ℝ) / ((p ^ (n - k)).totient : ℝ)) :=
  @_root_.P2MW.S_PadicAlgCl_norm_apply_sub_self_eq_of_isPrimitiveRoot_of_mem_fixingSubgroup.solution p inst_t1 n k hkn ζ hζ σ hσ hσ'
