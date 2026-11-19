/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularGroup_exists_mulEquiv_freeProduct_quotient_center (git blob 30c984b036ab1281a2b6478a3b255550d141e897, sha256 62ca84f2328a099e3f97ecdbf6b17517d344ef93b7cbc6f298c1ec0fb3d57cfc).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularGroup_exists_mulEquiv_freeProduct_quotient_center

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false
theorem ModularGroup.exists_mulEquiv_freeProduct_quotient_center :
    ∃ e : Monoid.CoprodI (fun i : Fin 2 => Multiplicative (ZMod (i.val + 2)))
        ≃* Matrix.SpecialLinearGroup (Fin 2) ℤ ⧸ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) ℤ),
      e (Monoid.CoprodI.of (M := fun i : Fin 2 => Multiplicative (ZMod (i.val + 2))) (i := 0)
          (Multiplicative.ofAdd 1)) = QuotientGroup.mk ModularGroup.S ∧
      e (Monoid.CoprodI.of (M := fun i : Fin 2 => Multiplicative (ZMod (i.val + 2))) (i := 1)
          (Multiplicative.ofAdd 1)) = QuotientGroup.mk (ModularGroup.S * ModularGroup.T) := @_root_.P2MW.S_ModularGroup_exists_mulEquiv_freeProduct_quotient_center.solution
