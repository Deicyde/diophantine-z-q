/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_PDivisibleGroup_Hopf_convPow_apply_mul_eq_sum_of_apply_mul_eq
Modified for the Z-in-Q kernel (2026-11-16, p-divisible Hodge-Tate port): local import paths
are relocated, the P2M.Util elaborators are replaced by standard Lean commands or explicit terms,
local notations are expanded in place, and the upstream lakefile options are set as `set_option`
lines after the imports; see ZInQKernel/Contrib/CloudB3SC3PDivHodge/PORTING.md. Any other change is marked `-- [port]`.
Original copyright/attribution notices: NOTICE.upstream and ATTRIBUTION.upstream.md in
ZInQKernel/Contrib/CloudB3SC3PDivHodge/Vendor/AnthropicFLT/; license: LICENSE in that directory.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.P2M.Sol.S_PDivisibleGroup_Hopf_convPow_apply_mul_eq_sum_of_apply_mul_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

universe u v w

theorem PDivisibleGroup.Hopf.convPow_apply_mul_eq_sum_of_apply_mul_eq
    {R : Type u} [inst_t1 : CommSemiring R] {A : Type v} [inst_t2 : Semiring A] [inst_t3 : Bialgebra R A]
    {Λ : Type w} [inst_t4 : CommSemiring Λ] [inst_t5 : Algebra R Λ] (d : A →ₗ[R] Λ)
    (hd : ∀ a b : A, d (a * b) = Coalgebra.counit (R := R) a • d b + Coalgebra.counit (R := R) b • d a)
    (k : ℕ) (a b : A) :
    (WithConv.toConv d ^ k).ofConv (a * b) =
      ∑ j ∈ Finset.range (k + 1), ((k.choose j : ℕ) : Λ) *
        ((WithConv.toConv d ^ j).ofConv a * (WithConv.toConv d ^ (k - j)).ofConv b) :=
  @_root_.P2MW.S_PDivisibleGroup_Hopf_convPow_apply_mul_eq_sum_of_apply_mul_eq.solution R inst_t1 A inst_t2 inst_t3 Λ inst_t4 inst_t5 d hd k a b
