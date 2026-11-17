/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_periodLatticeOf_gammaH_heckeDiamondStable (git blob 876cb84d5a5c87542e0ea617d7cc133a9ab370a8, sha256 26736381f692361a7f46217eec68ac6a03505082a12171afac7d4b7a4a95d372).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PeriodOf
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_periodLatticeOf_gammaH_heckeDiamondStable

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.periodLatticeOf_gammaH_heckeDiamondStable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M), ∀ v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H),
        (CuspForm.heckeTLinH 2 hℓ hℓM).dualMap v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H)) ∧
      (∀ (q : ℕ), q.Prime → q ∣ M → ∀ v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H),
        (CuspForm.heckeULinH 2 q).dualMap v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H)) ∧
      (∀ (d : (ZMod M)ˣ), ∀ v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H),
        (CuspForm.diamondLinH 2 d).dualMap v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H)) := by
  revert M H
  exact @_root_.P2MW.S_ModularCurve_periodLatticeOf_gammaH_heckeDiamondStable.solution
