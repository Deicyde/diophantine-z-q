/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_WeierstrassCurve_transcendental_j_perturb
Modified for the Z-in-Q kernel (2026-11-15, task flt-cqj2): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.P2M.Sol.S_WeierstrassCurve_transcendental_j_perturb

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open Polynomial WeierstrassCurve
theorem WeierstrassCurve.transcendental_j_perturb
    {R : Type*} [CommRing R] [IsDomain R] [CharZero R] {L : Type*} [Field L] [CharZero L]
    (φ : R →+* L) (t : L) (ht : ∀ P : Polynomial R, P ≠ 0 → P.eval₂ φ t ≠ 0)
    (W : WeierstrassCurve R) :
    ∃ hΔ : (⟨φ W.a₁, φ W.a₂, φ W.a₃, φ W.a₄ + t, φ W.a₆ + t ^ 2⟩ : WeierstrassCurve L).Δ ≠ 0,
      Transcendental ℚ (@WeierstrassCurve.j L _
        (⟨φ W.a₁, φ W.a₂, φ W.a₃, φ W.a₄ + t, φ W.a₆ + t ^ 2⟩ : WeierstrassCurve L)
        ⟨isUnit_iff_ne_zero.mpr hΔ⟩) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_transcendental_j_perturb.solution
