/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_pow_eq_of_residue_eq_pow_of_finrank_eq_of_krullDimLE_one (git blob aa75813d76c34a57636c4e9dc530e383fc93f046, sha256 f9df8c4b3d32da540407c135466cc361d28d1671300d1b300ff30d8ceb454a5e).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_RegularProlongation
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_RegularProlongation_exists_pow_eq_of_residue_eq_pow_of_finrank_eq_of_krullDimLE_one

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open AlgebraicCurve

theorem AlgebraicCurve.RegularProlongation.exists_pow_eq_of_residue_eq_pow_of_finrank_eq_of_krullDimLE_one
    {L : Type*} [Field L] [IsAlgClosed L] [CharZero L] (A : ValuationSubring L)
    [Ring.KrullDimLE 1 A]
    {F : Type*} [Field F] [Algebra L F]
    (hF : ∃ x : F, Transcendental L x ∧
      FiniteDimensional (IntermediateField.adjoin L ({x} : Set F)) F)
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar)
    (hgood : genusFF (IsLocalRing.ResidueField A) Fbar = genusFF L F)
    (hreg : ∃ x : R.integers, Transcendental (IsLocalRing.ResidueField A) (R.residue x) ∧
      0 < Module.finrank
        (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar ∧
      Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
        Module.finrank
          (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    {q : ℕ} [Fact q.Prime] (hq : (q : IsLocalRing.ResidueField A) ≠ 0)
    (f : R.integers) (hdvd : ∀ P : Place L F, (q : ℤ) ∣ P.ord (f : F))
    (w : Fbar) (hw0 : w ≠ 0) (hw : w ^ q = R.residue f) :
    ∃ h : F, h ^ q = (f : F) := by
  revert L A F hF Fbar R hgood hreg q hq f hdvd w hw0 hw
  exact @_root_.P2MW.S_AlgebraicCurve_RegularProlongation_exists_pow_eq_of_residue_eq_pow_of_finrank_eq_of_krullDimLE_one.solution
