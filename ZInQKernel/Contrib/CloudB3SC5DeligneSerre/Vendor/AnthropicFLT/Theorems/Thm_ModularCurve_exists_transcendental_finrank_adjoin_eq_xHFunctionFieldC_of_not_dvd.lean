/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_exists_transcendental_finrank_adjoin_eq_xHFunctionFieldC_of_not_dvd (git blob 99056cf186aec6dcd9ed09b6f7b38cccbb1bef94, sha256 29928d769444a5e40b6e727ef08554a1ada36b89da38651a9f2cd50f85cb40c4).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_XH
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_EllipticCurve_FrobeniusTrace
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_exists_transcendental_finrank_adjoin_eq_xHFunctionFieldC_of_not_dvd

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open AlgebraicCurve ModularCurve

set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.exists_transcendental_finrank_adjoin_eq_xHFunctionFieldC_of_not_dvd
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ} [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ) :
    ∃ (y : LaurentSeries A)
      (hy : ModularCurve.coeffMap A.subtype y ∈ ModularCurve.xHFunctionFieldBar M H)
      (hyk : ModularCurve.coeffMap (IsLocalRing.residue A) y ∈
        ModularCurve.xHFunctionFieldC (IsLocalRing.ResidueField A) M H),
      Transcendental (IsLocalRing.ResidueField A)
          (⟨_, hyk⟩ : ModularCurve.xHFunctionFieldC (IsLocalRing.ResidueField A) M H) ∧
        0 < Module.finrank
          (IntermediateField.adjoin (IsLocalRing.ResidueField A)
            ({(⟨_, hyk⟩ : ModularCurve.xHFunctionFieldC (IsLocalRing.ResidueField A) M H)} :
              Set (ModularCurve.xHFunctionFieldC (IsLocalRing.ResidueField A) M H)))
          (ModularCurve.xHFunctionFieldC (IsLocalRing.ResidueField A) M H) ∧
        Module.finrank
            (IntermediateField.adjoin (AlgebraicClosure ℚ)
              ({(⟨_, hy⟩ : ModularCurve.xHFunctionFieldBar M H)} :
                Set (ModularCurve.xHFunctionFieldBar M H)))
            (ModularCurve.xHFunctionFieldBar M H) =
          Module.finrank
            (IntermediateField.adjoin (IsLocalRing.ResidueField A)
              ({(⟨_, hyk⟩ : ModularCurve.xHFunctionFieldC (IsLocalRing.ResidueField A) M H)} :
                Set (ModularCurve.xHFunctionFieldC (IsLocalRing.ResidueField A) M H)))
            (ModularCurve.xHFunctionFieldC (IsLocalRing.ResidueField A) M H) := by
  revert M H ℓ hℓM A hA
  exact @_root_.P2MW.S_ModularCurve_exists_transcendental_finrank_adjoin_eq_xHFunctionFieldC_of_not_dvd.solution
