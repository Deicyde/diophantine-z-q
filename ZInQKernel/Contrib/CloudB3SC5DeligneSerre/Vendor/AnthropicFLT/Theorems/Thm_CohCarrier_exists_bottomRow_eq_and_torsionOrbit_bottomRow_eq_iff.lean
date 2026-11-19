/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_CohCarrier_exists_bottomRow_eq_and_torsionOrbit_bottomRow_eq_iff (git blob 57c6d8c6ab84dfe1c812903ac5b997b0c65e691b, sha256 4073c0052fc55356ed4501cdd308e8ba9377c18fbba156a32a609d011005a1c6).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CohCarrier_Level
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_CohCarrier_exists_bottomRow_eq_and_torsionOrbit_bottomRow_eq_iff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open scoped MatrixGroups

theorem CohCarrier.exists_bottomRow_eq_and_torsionOrbit_bottomRow_eq_iff
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    (∀ v : ZMod M × ZMod M, addOrderOf v = M →
      ∃ a : SL(2, ℤ), ((a 1 0 : ℤ) : ZMod M) = v.1 ∧ ((a 1 1 : ℤ) : ZMod M) = v.2) ∧
    (∀ a : SL(2, ℤ), addOrderOf ((((a 1 0 : ℤ) : ZMod M), ((a 1 1 : ℤ) : ZMod M)) : ZMod M × ZMod M) = M) ∧
    (∀ a b : SL(2, ℤ),
      {w : ZMod M × ZMod M | ∃ u : (ZMod M)ˣ, u ∈ H ⊔ Subgroup.zpowers (-1) ∧
          w = (u : ZMod M).val • ((((a 1 0 : ℤ) : ZMod M), ((a 1 1 : ℤ) : ZMod M)) : ZMod M × ZMod M)} =
        {w : ZMod M × ZMod M | ∃ u : (ZMod M)ˣ, u ∈ H ⊔ Subgroup.zpowers (-1) ∧
          w = (u : ZMod M).val • ((((b 1 0 : ℤ) : ZMod M), ((b 1 1 : ℤ) : ZMod M)) : ZMod M × ZMod M)} ↔
      b * a⁻¹ ∈ CohCarrier.GammaH M H ⊔ Subgroup.zpowers (-1)) := by
  revert M H
  exact @_root_.P2MW.S_CohCarrier_exists_bottomRow_eq_and_torsionOrbit_bottomRow_eq_iff.solution
