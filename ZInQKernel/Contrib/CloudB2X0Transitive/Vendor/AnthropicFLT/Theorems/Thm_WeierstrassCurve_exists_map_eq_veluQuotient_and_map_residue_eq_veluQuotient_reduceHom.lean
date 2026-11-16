/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_WeierstrassCurve_exists_map_eq_veluQuotient_and_map_residue_eq_veluQuotient_reduceHom
Modified for the Z-in-Q kernel (2026-11-15, task flt-cqj2): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_WeierstrassCurve_Velu
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_WeierstrassCurve_OddOrderSummingSet
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_WeierstrassCurve_ReduceHom
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.P2M.Sol.S_WeierstrassCurve_exists_map_eq_veluQuotient_and_map_residue_eq_veluQuotient_reduceHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open WeierstrassCurve IsLocalRing

theorem WeierstrassCurve.exists_map_eq_veluQuotient_and_map_residue_eq_veluQuotient_reduceHom
    {L : Type*} [Field L] [DecidableEq L] (A : ValuationSubring L) [DecidableEq (ResidueField A)]
    (W : WeierstrassCurve A) (hΔ : (W.map (residue A)).Δ ≠ 0)
    {ℓ : ℕ} (hℓ : (ℓ : ResidueField A) ≠ 0)
    (Q : (W.map A.subtype).toAffine.Point) (hQ : addOrderOf Q = ℓ) {n : ℕ} (hn : n < ℓ) :
    ∃ V : WeierstrassCurve A,
      V.map A.subtype = (W.map A.subtype).veluQuotient ((W.map A.subtype).oddOrderSummingSet Q n) ∧
      V.map (residue A) =
        (W.map (residue A)).veluQuotient ((W.map (residue A)).oddOrderSummingSet (reduceHom hΔ Q) n) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_map_eq_veluQuotient_and_map_residue_eq_veluQuotient_reduceHom.solution
