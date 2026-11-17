/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_exists_heckeEquivariant_parabolicHoms_to_dual_tateModule_jH (git blob 8ecde5ce3e33ef75bc503ed0f818fb2c85960b45, sha256 ee7e9b5449775974672aca96a0442005ff9718639d9f8a8f1c1f96cf4ab997a5).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_XHOperators
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PeriodMap
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_exists_heckeEquivariant_parabolicHoms_to_dual_tateModule_jH

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


theorem ModularCurve.exists_heckeEquivariant_parabolicHoms_to_dual_tateModule_jH
    (M p : ℕ) [NeZero M] [Fact p.Prime] (H : Subgroup (ZMod M)ˣ) (S : Set ℕ)
    (hin : ModularCurve.HeckeDiamondInputsHAll M H) :
    ∃ Φ : CohCarrier.H1 M H ℤ_[p] →ₗ[ℤ_[p]]
        (TateModule p (ModularCurve.JH M H) →ₗ[ℤ_[p]] ℤ_[p]),
      (∀ (g : CohCarrier.Gen M S) (v : CohCarrier.H1 M H ℤ_[p]),
        v ∈ ModularCurve.Period.parabolicHoms ℤ_[p] (CohCarrier.GammaH M H) ℤ_[p] →
          Φ (CohCarrier.opFamily M H S ℤ_[p] g v) = (Φ v) ∘ₗ ModularCurve.tateGenOpH M H S p g) ∧
      (ModularCurve.Period.parabolicHoms ℤ_[p] (CohCarrier.GammaH M H) ℤ_[p]).map Φ = ⊤ ∧
      (∀ v ∈ ModularCurve.Period.parabolicHoms ℤ_[p] (CohCarrier.GammaH M H) ℤ_[p], Φ v = 0 → v = 0) := by
  revert M p H S hin
  exact @_root_.P2MW.S_ModularCurve_exists_heckeEquivariant_parabolicHoms_to_dual_tateModule_jH.solution
