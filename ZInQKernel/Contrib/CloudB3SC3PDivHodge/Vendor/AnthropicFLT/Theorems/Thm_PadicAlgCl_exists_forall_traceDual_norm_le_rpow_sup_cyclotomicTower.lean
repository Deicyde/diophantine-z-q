/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_PadicAlgCl_exists_forall_traceDual_norm_le_rpow_sup_cyclotomicTower
Modified for the Z-in-Q kernel (2026-11-16, p-divisible Hodge-Tate port): local import paths
are relocated, the P2M.Util elaborators are replaced by standard Lean commands or explicit terms,
local notations are expanded in place, and the upstream lakefile options are set as `set_option`
lines after the imports; see ZInQKernel/Contrib/CloudB3SC3PDivHodge/PORTING.md. Any other change is marked `-- [port]`.
Original copyright/attribution notices: NOTICE.upstream and ATTRIBUTION.upstream.md in
ZInQKernel/Contrib/CloudB3SC3PDivHodge/Vendor/AnthropicFLT/; license: LICENSE in that directory.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W11Cyclotomic.TowerDefinition
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.P2M.Sol.S_PadicAlgCl_exists_forall_traceDual_norm_le_rpow_sup_cyclotomicTower

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

theorem PadicAlgCl.exists_forall_traceDual_norm_le_rpow_sup_cyclotomicTower
    (p : ℕ) [inst_t1 : Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [inst_t2 : FiniteDimensional ℚ_[p] K]
    (M : IntermediateField ℚ_[p] (PadicAlgCl p)) [inst_t3 : FiniteDimensional ℚ_[p] M]
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ z : IntermediateField.extendScalars (F := K ⊔ PadicAlgCl.cyclotomicTower p n)
          (E := M ⊔ (K ⊔ PadicAlgCl.cyclotomicTower p n)) le_sup_right,
        (∀ w : IntermediateField.extendScalars (F := K ⊔ PadicAlgCl.cyclotomicTower p n)
            (E := M ⊔ (K ⊔ PadicAlgCl.cyclotomicTower p n)) le_sup_right,
          ‖(w : PadicAlgCl p)‖ ≤ 1 →
          ‖((Algebra.trace ↥(K ⊔ PadicAlgCl.cyclotomicTower p n)
              ↥(IntermediateField.extendScalars (F := K ⊔ PadicAlgCl.cyclotomicTower p n)
                (E := M ⊔ (K ⊔ PadicAlgCl.cyclotomicTower p n)) le_sup_right) (z * w) :
                ↥(K ⊔ PadicAlgCl.cyclotomicTower p n)) : PadicAlgCl p)‖ ≤ 1) →
        ‖(z : PadicAlgCl p)‖ ≤ (p : ℝ) ^ ε :=
  @_root_.P2MW.S_PadicAlgCl_exists_forall_traceDual_norm_le_rpow_sup_cyclotomicTower.solution p inst_t1 K inst_t2 M inst_t3 ε hε
