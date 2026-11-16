/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_PadicAlgCl_exists_forall_rpow_neg_lt_norm_algEquiv_sub_of_mem_sup_cyclotomicTower
Modified for the Z-in-Q kernel (2026-11-16, p-divisible Hodge-Tate port): local import paths
are relocated, the P2M.Util elaborators are replaced by standard Lean commands or explicit terms,
local notations are expanded in place, and the upstream lakefile options are set as `set_option`
lines after the imports; see ZInQKernel/Contrib/CloudB3SC3PDivHodge/PORTING.md. Any other change is marked `-- [port]`.
Original copyright/attribution notices: NOTICE.upstream and ATTRIBUTION.upstream.md in
ZInQKernel/Contrib/CloudB3SC3PDivHodge/Vendor/AnthropicFLT/; license: LICENSE in that directory.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W11Cyclotomic.TowerDefinition
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.P2M.Sol.S_PadicAlgCl_exists_forall_rpow_neg_lt_norm_algEquiv_sub_of_mem_sup_cyclotomicTower

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

theorem PadicAlgCl.exists_forall_rpow_neg_lt_norm_algEquiv_sub_of_mem_sup_cyclotomicTower
    (p : ℕ) [inst_t1 : Fact p.Prime] (M : IntermediateField ℚ_[p] (PadicAlgCl p)) [inst_t2 : FiniteDimensional ℚ_[p] M]
    [inst_t3 : Normal ℚ_[p] M] (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ a : PadicAlgCl p,
      a ∈ M ⊔ PadicAlgCl.cyclotomicTower p n → ‖a‖ ≤ 1 →
      PadicAlgCl.cyclotomicTower p n ≤ IntermediateField.adjoin ℚ_[p] {a} →
      (∀ c ∈ IntermediateField.adjoin ℚ_[p] {a}, ‖c‖ ≤ 1 →
        ∃ P : Polynomial ℚ_[p], (∀ i, ‖P.coeff i‖ ≤ 1) ∧ Polynomial.aeval a P = c) →
      ∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p,
        σ ∈ (PadicAlgCl.cyclotomicTower p n).fixingSubgroup → σ a ≠ a →
        (p : ℝ) ^ (-ε) < ‖σ a - a‖ :=
  @_root_.P2MW.S_PadicAlgCl_exists_forall_rpow_neg_lt_norm_algEquiv_sub_of_mem_sup_cyclotomicTower.solution p inst_t1 M inst_t2 inst_t3 ε hε
