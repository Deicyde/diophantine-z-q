/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_PDivisibleGroup_ker_cotangentMap_eq_smul_top_and_smul_top_eq_bot
Modified for the Z-in-Q kernel (2026-11-16, p-divisible Hodge-Tate port): local import paths
are relocated, the P2M.Util elaborators are replaced by standard Lean commands or explicit terms,
local notations are expanded in place, and the upstream lakefile options are set as `set_option`
lines after the imports; see ZInQKernel/Contrib/CloudB3SC3PDivHodge/PORTING.md. Any other change is marked `-- [port]`.
Original copyright/attribution notices: NOTICE.upstream and ATTRIBUTION.upstream.md in
ZInQKernel/Contrib/CloudB3SC3PDivHodge/Vendor/AnthropicFLT/; license: LICENSE in that directory.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.Definitions.Def_PDivisibleGroup_Dimension
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.P2M.Sol.S_PDivisibleGroup_ker_cotangentMap_eq_smul_top_and_smul_top_eq_bot

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

theorem PDivisibleGroup.ker_cotangentMap_eq_smul_top_and_smul_top_eq_bot
    {R : Type} [inst_t1 : CommRing R] {p h : ℕ} (G : PDivisibleGroup R p h) (v : ℕ) :
    LinearMap.ker (G.cotangentMap v) = Ideal.span {(p : R) ^ v} • ⊤ ∧
      Ideal.span {(p : R) ^ v} • (⊤ : Submodule R (G.Cotangent v)) = ⊥ :=
  @_root_.P2MW.S_PDivisibleGroup_ker_cotangentMap_eq_smul_top_and_smul_top_eq_bot.solution R inst_t1 p h G v
