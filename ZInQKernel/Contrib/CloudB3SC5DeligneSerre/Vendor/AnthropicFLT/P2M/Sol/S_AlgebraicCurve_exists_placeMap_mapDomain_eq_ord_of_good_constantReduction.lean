/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_exists_placeMap_mapDomain_eq_ord_of_good_constantReduction (git blob f52d0b1ca864f370a8f8443cf01ae43ff702a2c9, sha256 7673befc75d202e097d9b2720625be3f1d1ebf3785ca8c7784a1f130d41ccd7c).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Repartitions
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_RegularProlongation
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_RegularProlongation_residue_integralClosure_surjective_of_genusFF_eq
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_placeMap_mapDomain_eq_ord_of_residue_integralClosure_surjective

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicCurve_exists_placeMap_mapDomain_eq_ord_of_good_constantReduction

open AlgebraicCurve

theorem solution
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F] [IsCurveOver L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    [IsCurveOver (IsLocalRing.ResidueField A) Fbar]
    (O : ValuationSubring F) (res : O →+* Fbar)
    (hOA : ∀ c : L, algebraMap L F c ∈ O ↔ c ∈ A)
    (hsurj : Function.Surjective res)
    (hker : RingHom.ker res = IsLocalRing.maximalIdeal O)
    (hconst : ∀ a : A, res ⟨algebraMap L F a, (hOA a).mpr a.2⟩ =
      algebraMap (IsLocalRing.ResidueField A) Fbar (IsLocalRing.residue A a))
    (he : ∀ f : F, f ≠ 0 → ∃ c : L, ∃ h : c • f ∈ O, res ⟨c • f, h⟩ ≠ 0)
    (hreg : ∃ x : O, Transcendental (IsLocalRing.ResidueField A) (res x) ∧
      0 < Module.finrank
        (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({res x} : Set Fbar)) Fbar ∧
      Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
        Module.finrank
          (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({res x} : Set Fbar)) Fbar)
    (hgood : genusFF (IsLocalRing.ResidueField A) Fbar = genusFF L F) :
    ∃ r : Place L F → Place (IsLocalRing.ResidueField A) Fbar,
      ∀ f : O, res f ≠ 0 → ∀ D : Divisor L F, (∀ P, D P = P.ord (f : F)) →
        ∀ Q, Finsupp.mapDomain r D Q = Q.ord (res f) := by

  let R : RegularProlongation A F Fbar :=
    { integers := O
      residue := res
      algebraMap_mem_iff := hOA
      residue_surjective := hsurj
      ker_residue := hker
      residue_algebraMap := hconst
      exists_smul_mem := he }
  obtain ⟨x, hx, hfin, hdeg⟩ := hreg

  have hchart :
      (∀ h : Fbar, IsIntegral (Algebra.adjoin (IsLocalRing.ResidueField A) {R.residue x}) h →
        ∃ f : R.integers, IsIntegral (Algebra.adjoin L {(x : F)}) (f : F) ∧ R.residue f = h) ∧
      (∀ h : Fbar, IsIntegral (Algebra.adjoin (IsLocalRing.ResidueField A) {(R.residue x)⁻¹}) h →
        ∃ f : R.integers, IsIntegral (Algebra.adjoin L {(x : F)⁻¹}) (f : F) ∧ R.residue f = h) :=
    RegularProlongation.residue_integralClosure_surjective_of_genusFF_eq
      A R x hx hfin hdeg hgood

  exact
    RegularProlongation.exists_placeMap_mapDomain_eq_ord_of_residue_integralClosure_surjective
      A R x hx hfin hdeg hchart
