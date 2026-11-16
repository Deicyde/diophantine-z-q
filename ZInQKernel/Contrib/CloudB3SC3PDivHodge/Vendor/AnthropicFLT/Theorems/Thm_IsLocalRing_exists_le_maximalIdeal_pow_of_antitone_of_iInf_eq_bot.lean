/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_IsLocalRing_exists_le_maximalIdeal_pow_of_antitone_of_iInf_eq_bot
Modified for the Z-in-Q kernel (2026-11-16, p-divisible Hodge-Tate port): local import paths
are relocated, the P2M.Util elaborators are replaced by standard Lean commands or explicit terms,
local notations are expanded in place, and the upstream lakefile options are set as `set_option`
lines after the imports; see ZInQKernel/Contrib/CloudB3SC3PDivHodge/PORTING.md. Any other change is marked `-- [port]`.
Original copyright/attribution notices: NOTICE.upstream and ATTRIBUTION.upstream.md in
ZInQKernel/Contrib/CloudB3SC3PDivHodge/Vendor/AnthropicFLT/; license: LICENSE in that directory.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.P2M.Sol.S_IsLocalRing_exists_le_maximalIdeal_pow_of_antitone_of_iInf_eq_bot

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

universe u

theorem IsLocalRing.exists_le_maximalIdeal_pow_of_antitone_of_iInf_eq_bot
    {A : Type u} [inst_t1 : CommRing A] [inst_t2 : IsNoetherianRing A] [inst_t3 : IsLocalRing A]
    [inst_t4 : IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (K : ℕ → Ideal A) (hK : Antitone K) (hinf : ⨅ w, K w = ⊥) (N : ℕ) :
    ∃ w : ℕ, K w ≤ IsLocalRing.maximalIdeal A ^ N :=
  @_root_.P2MW.S_IsLocalRing_exists_le_maximalIdeal_pow_of_antitone_of_iInf_eq_bot.solution A inst_t1 inst_t2 inst_t3 inst_t4 K hK hinf N
