/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_PDivisibleGroup_CartierDuality_bijective_tateModule_pairing_of_isAlgClosed
Modified for the Z-in-Q kernel (2026-11-16, p-divisible Hodge-Tate port): local import paths
are relocated, the P2M.Util elaborators are replaced by standard Lean commands or explicit terms,
local notations are expanded in place, and the upstream lakefile options are set as `set_option`
lines after the imports; see ZInQKernel/Contrib/CloudB3SC3PDivHodge/PORTING.md. Any other change is marked `-- [port]`.
Original copyright/attribution notices: NOTICE.upstream and ATTRIBUTION.upstream.md in
ZInQKernel/Contrib/CloudB3SC3PDivHodge/Vendor/AnthropicFLT/; license: LICENSE in that directory.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.Definitions.Def_PDivisibleGroup_CartierDuality
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.P2M.Sol.S_PDivisibleGroup_CartierDuality_bijective_tateModule_pairing_of_isAlgClosed

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

theorem PDivisibleGroup.CartierDuality.bijective_tateModule_pairing_of_isAlgClosed
    {R : Type} [inst_t1 : CommRing R] {p h : ℕ} [inst_t2 : Fact p.Prime] {G G' : PDivisibleGroup R p h}
    (D : G.CartierDuality G') (L : Type) [inst_t3 : Field L] [inst_t4 : IsAlgClosed L] [inst_t5 : CharZero L] [inst_t6 : Algebra R L]
    (B : TateModule p (G.Points L) →ₗ[ℤ_[p]] TateModule p (G'.Points L) →ₗ[ℤ_[p]] TateModule p (Additive Lˣ))
    (hB : ∀ (x : TateModule p (G.Points L)) (y : TateModule p (G'.Points L)) (v : ℕ)
      (f : G.Point L v) (ψ : G'.Point L v),
      G.pointsMkAdd L v (Additive.ofMul f) = (x : ℕ → G.Points L) v →
      G'.pointsMkAdd L v (Additive.ofMul ψ) = (y : ℕ → G'.Points L) v →
      ((Additive.toMul ((B x y : ℕ → Additive Lˣ) v) : Lˣ) : L) = D.pair L v f ψ) :
    Function.Bijective B.flip ∧ Function.Bijective B :=
  @_root_.P2MW.S_PDivisibleGroup_CartierDuality_bijective_tateModule_pairing_of_isAlgClosed.solution R inst_t1 p h inst_t2 G G' D L inst_t3 inst_t4 inst_t5 inst_t6 B hB
