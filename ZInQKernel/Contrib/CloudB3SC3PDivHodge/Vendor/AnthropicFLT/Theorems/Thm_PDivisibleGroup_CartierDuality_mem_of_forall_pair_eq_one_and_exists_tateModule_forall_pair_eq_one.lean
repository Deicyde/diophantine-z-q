/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_PDivisibleGroup_CartierDuality_mem_of_forall_pair_eq_one_and_exists_tateModule_forall_pair_eq_one
Modified for the Z-in-Q kernel (2026-11-16, p-divisible Hodge-Tate port): local import paths
are relocated, the P2M.Util elaborators are replaced by standard Lean commands or explicit terms,
local notations are expanded in place, and the upstream lakefile options are set as `set_option`
lines after the imports; see ZInQKernel/Contrib/CloudB3SC3PDivHodge/PORTING.md. Any other change is marked `-- [port]`.
Original copyright/attribution notices: NOTICE.upstream and ATTRIBUTION.upstream.md in
ZInQKernel/Contrib/CloudB3SC3PDivHodge/Vendor/AnthropicFLT/; license: LICENSE in that directory.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.Definitions.Def_PDivisibleGroup_CartierDuality
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.P2M.Sol.S_PDivisibleGroup_CartierDuality_mem_of_forall_pair_eq_one_and_exists_tateModule_forall_pair_eq_one

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

theorem PDivisibleGroup.CartierDuality.mem_of_forall_pair_eq_one_and_exists_tateModule_forall_pair_eq_one
    {R : Type} [inst_t1 : CommRing R] {p h : ℕ} [inst_t2 : Fact p.Prime] {G G' : PDivisibleGroup R p h}
    (D : G.CartierDuality G') (K : Type) [inst_t3 : Field K] [inst_t4 : IsAlgClosed K] [inst_t5 : CharZero K] [inst_t6 : Algebra R K] :
    (∀ (w : ℕ) (H : Subgroup (G.Point K w)) (z : G.Point K w),
      (∀ ψ : G'.Point K w, (∀ z' ∈ H, D.pair K w z' ψ = 1) → D.pair K w z ψ = 1) → z ∈ H) ∧
    (∀ (H : ∀ w : ℕ, Subgroup (G.Point K w)),
      (∀ (w : ℕ) (z : G.Point K w), G.pointIncl K w z ∈ H (w + 1) → z ∈ H w) →
      ∀ ψ₁ : G'.Point K 1, (∀ z ∈ H 1, D.pair K 1 z ψ₁ = 1) →
        ∃ y : TateModule p (G'.Points K),
          (y : ℕ → G'.Points K) 1 = G'.pointsMkAdd K 1 (Additive.ofMul ψ₁) ∧
          ∀ (w : ℕ) (ψ : G'.Point K w),
            G'.pointsMkAdd K w (Additive.ofMul ψ) = (y : ℕ → G'.Points K) w →
            ∀ z ∈ H w, D.pair K w z ψ = 1) :=
  @_root_.P2MW.S_PDivisibleGroup_CartierDuality_mem_of_forall_pair_eq_one_and_exists_tateModule_forall_pair_eq_one.solution R inst_t1 p h inst_t2 G G' D K inst_t3 inst_t4 inst_t5 inst_t6
