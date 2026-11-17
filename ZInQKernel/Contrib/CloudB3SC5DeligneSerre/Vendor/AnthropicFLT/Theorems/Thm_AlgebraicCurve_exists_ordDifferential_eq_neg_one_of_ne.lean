/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_exists_ordDifferential_eq_neg_one_of_ne (git blob e767af3a5b4292ca37d6efa5b662339cfee3897d, sha256 7c51f28814b1f6282b72bd99028e7abd477eaabafcf78f7cd3522f518d5663bb).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CanonicalDivisor
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_RiemannRochRows
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_exists_ordDifferential_eq_neg_one_of_ne

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.exists_ordDifferential_eq_neg_one_of_ne {K F : Type*} [Field K] [Field F]
    [Algebra K F] [IsAlgClosed K] [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)]
    [∀ w : Place K F, w.DCoordGenerates] [Nontrivial (Ω[F⁄K])]
    (hRR : FunctionFieldRiemannRoch K F) {P Q : Place K F} (hPQ : P ≠ Q) :
    ∃ ω : Ω[F⁄K], ω ≠ 0 ∧ P.ordDifferential ω = -1 ∧ Q.ordDifferential ω = -1 ∧
      ∀ v : Place K F, v ≠ P → v ≠ Q → 0 ≤ v.ordDifferential ω := by
  revert K F hRR P Q hPQ
  exact @_root_.P2MW.S_AlgebraicCurve_exists_ordDifferential_eq_neg_one_of_ne.solution
