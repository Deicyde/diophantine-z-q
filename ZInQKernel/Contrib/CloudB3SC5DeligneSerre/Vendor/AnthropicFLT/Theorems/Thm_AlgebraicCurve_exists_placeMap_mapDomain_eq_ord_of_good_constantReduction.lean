/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_exists_placeMap_mapDomain_eq_ord_of_good_constantReduction (git blob 7b97802d5a6f51abd463d94601f9c0ebde1aaaea, sha256 21c3c8e8352fedeccc4cf11632b6e77984fc08368f437e906d04530d5e4d9fcc).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Repartitions
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_exists_placeMap_mapDomain_eq_ord_of_good_constantReduction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open AlgebraicCurve

theorem AlgebraicCurve.exists_placeMap_mapDomain_eq_ord_of_good_constantReduction
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
  revert L A F Fbar O res hOA hsurj hker hconst he hreg hgood
  exact @_root_.P2MW.S_AlgebraicCurve_exists_placeMap_mapDomain_eq_ord_of_good_constantReduction.solution
