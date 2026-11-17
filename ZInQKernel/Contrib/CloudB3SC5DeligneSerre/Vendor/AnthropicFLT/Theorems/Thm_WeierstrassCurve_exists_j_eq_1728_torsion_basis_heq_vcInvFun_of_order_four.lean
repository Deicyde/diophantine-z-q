/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_WeierstrassCurve_exists_j_eq_1728_torsion_basis_heq_vcInvFun_of_order_four (git blob 60a82df82a679ba4f6e668e387881479152acc87, sha256 dbe278ea90a2f9e89bc9e8724c1ff3639871082811f4acee531104a883fcc9c5).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_WeierstrassCurve_exists_j_eq_1728_torsion_basis_heq_vcInvFun_of_order_four

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open WeierstrassCurve WeierstrassCurve.Affine

theorem WeierstrassCurve.exists_j_eq_1728_torsion_basis_heq_vcInvFun_of_order_four
    (K : Type*) [Field K] [DecidableEq K] [IsAlgClosed K] (M : ℕ) [NeZero M] (hM : (M : K) ≠ 0) :
    ∃ (E₀ : WeierstrassCurve K) (_ : E₀.IsElliptic) (σ : WeierstrassCurve.VariableChange K)
      (P Q : E₀.toAffine.Point),
      E₀.j = 1728 ∧ σ • E₀ = E₀ ∧ M • P = 0 ∧ M • Q = 0 ∧
      (∀ T : E₀.toAffine.Point, M • T = 0 →
        ∃! c : ZMod M × ZMod M, T = c.1.val • P + c.2.val • Q) ∧
      HEq (Point.vcInvFun σ E₀.toAffine P) Q ∧
      HEq (Point.vcInvFun σ E₀.toAffine Q) (-P) := by
  revert K M hM
  exact @_root_.P2MW.S_WeierstrassCurve_exists_j_eq_1728_torsion_basis_heq_vcInvFun_of_order_four.solution
