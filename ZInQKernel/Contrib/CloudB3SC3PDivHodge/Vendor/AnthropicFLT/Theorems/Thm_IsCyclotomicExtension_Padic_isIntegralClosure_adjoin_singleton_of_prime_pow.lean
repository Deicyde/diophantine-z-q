/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_IsCyclotomicExtension_Padic_isIntegralClosure_adjoin_singleton_of_prime_pow
Modified for the Z-in-Q kernel (2026-11-16, p-divisible Hodge-Tate port): local import paths
are relocated, the P2M.Util elaborators are replaced by standard Lean commands or explicit terms,
local notations are expanded in place, and the upstream lakefile options are set as `set_option`
lines after the imports; see ZInQKernel/Contrib/CloudB3SC3PDivHodge/PORTING.md. Any other change is marked `-- [port]`.
Original copyright/attribution notices: NOTICE.upstream and ATTRIBUTION.upstream.md in
ZInQKernel/Contrib/CloudB3SC3PDivHodge/Vendor/AnthropicFLT/; license: LICENSE in that directory.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.P2M.Sol.S_IsCyclotomicExtension_Padic_isIntegralClosure_adjoin_singleton_of_prime_pow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

theorem IsCyclotomicExtension.Padic.isIntegralClosure_adjoin_singleton_of_prime_pow
    (p : ℕ) [inst_t1 : Fact p.Prime] (k : ℕ) (K : Type*) [inst_t2 : Field K] [inst_t3 : Algebra ℚ_[p] K]
    [inst_t4 : Algebra ℤ_[p] K] [inst_t5 : IsScalarTower ℤ_[p] ℚ_[p] K] [inst_t6 : IsCyclotomicExtension {p ^ k} ℚ_[p] K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ (p ^ k)) :
    IsIntegralClosure (Algebra.adjoin ℤ_[p] ({ζ} : Set K)) ℤ_[p] K :=
  @_root_.P2MW.S_IsCyclotomicExtension_Padic_isIntegralClosure_adjoin_singleton_of_prime_pow.solution p inst_t1 k K inst_t2 inst_t3 inst_t4 inst_t5 inst_t6 ζ hζ
