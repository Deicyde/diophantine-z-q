/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_WeierstrassCurve_stepCurve_stepSubgroup_eq_of_prime_ne_two
Modified for the Z-in-Q kernel (2026-11-15, task flt-cqj2): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_WeierstrassCurve_CyclicQuotientJ
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_WeierstrassCurve_VeluQuotientMap
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_WeierstrassCurve_VeluPointMap
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.P2M.Sol.S_WeierstrassCurve_stepCurve_stepSubgroup_eq_of_prime_ne_two

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open WeierstrassCurve

universe u in

theorem WeierstrassCurve.stepCurve_stepSubgroup_eq_of_prime_ne_two
    {L : Type u} [Field L] [DecidableEq L] (E : WeierstrassCurve L)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (H : AddSubgroup E.toAffine.Point) [IsAddCyclic H] [Finite H]
    (Q : E.toAffine.Point) (hQH : Q ∈ H) (hQ : addOrderOf Q = ℓ)
    (φ : E.toAffine.Point →+ (E.veluQuotient (E.oddOrderSummingSet Q (ℓ / 2))).toAffine.Point)
    (hφker : φ.ker = AddSubgroup.zmultiples Q)
    (hφ : ∀ (x y : L) (h : E.toAffine.Nonsingular x y),
      (.some x y h : E.toAffine.Point) ∉ AddSubgroup.zmultiples Q →
        ∃ h', φ (.some x y h) = .some (E.veluX (E.oddOrderSummingSet Q (ℓ / 2)) x)
          (E.veluY (E.oddOrderSummingSet Q (ℓ / 2)) x y) h') :
    (⟨E.stepCurve H ℓ, E.stepSubgroup H ℓ⟩ : Σ V : WeierstrassCurve L, AddSubgroup V.toAffine.Point) =
      ⟨E.veluQuotient (E.oddOrderSummingSet Q (ℓ / 2)), H.map φ⟩ := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_stepCurve_stepSubgroup_eq_of_prime_ne_two.solution
