/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_PDivisibleGroup_nonempty_basis_cotangentModule_of_hasDimension
Modified for the Z-in-Q kernel (2026-11-16, p-divisible Hodge-Tate port): local import paths
are relocated, the P2M.Util elaborators are replaced by standard Lean commands or explicit terms,
local notations are expanded in place, and the upstream lakefile options are set as `set_option`
lines after the imports; see ZInQKernel/Contrib/CloudB3SC3PDivHodge/PORTING.md. Any other change is marked `-- [port]`.
Original copyright/attribution notices: NOTICE.upstream and ATTRIBUTION.upstream.md in
ZInQKernel/Contrib/CloudB3SC3PDivHodge/Vendor/AnthropicFLT/; license: LICENSE in that directory.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.Definitions.Def_PDivisibleGroup_Dimension
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.P2M.Sol.S_PDivisibleGroup_nonempty_basis_cotangentModule_of_hasDimension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

theorem PDivisibleGroup.nonempty_basis_cotangentModule_of_hasDimension
    {R : Type} [inst_t1 : CommRing R] [inst_t2 : IsNoetherianRing R] (I : Ideal R) [inst_t3 : IsAdicComplete I R]
    {p h : ℕ} (hp : (p : R) ∈ I) (G : PDivisibleGroup R p h) {n : ℕ} (hn : G.HasDimension n) :
    Nonempty (Module.Basis (Fin n) R G.cotangentModule) ∧
      (∀ v, Function.Surjective (G.cotangentModuleProj v)) ∧
      ∀ v, LinearMap.ker (G.cotangentModuleProj v) =
        Ideal.span {(p : R) ^ v} • (⊤ : Submodule R G.cotangentModule) :=
  @_root_.P2MW.S_PDivisibleGroup_nonempty_basis_cotangentModule_of_hasDimension.solution R inst_t1 inst_t2 I inst_t3 p h hp G n hn
