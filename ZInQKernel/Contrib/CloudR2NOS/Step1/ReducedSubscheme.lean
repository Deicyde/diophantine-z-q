/-
H5 lane C3 STEP-F11 fix edition (2026-11-17). Source only. The change relative to its base is recorded in the C3 fix ledger.
-/
/-
H5 lane3 Step 1: `IsReducedSubschemeVanishingIdeal` (ConstructorParts.lean) PROVED from Mathlib.
2026-11-17. New file. SOURCE-ONLY, UNCOMPILED. Universe u.

The proof:
* the subscheme is covered by `Spec (Γ(X, U) ⧸ I(U))` for affine opens `U` (Mathlib
  `IdealSheafData.subschemeCover`);
* for `I = vanishingIdeal Z`, `I(U)` is a prime-spectrum vanishing ideal (`vanishingIdeal_ideal`),
  hence radical (`PrimeSpectrum.isRadical_vanishingIdeal`);
* so each quotient is reduced (`Ideal.isRadical_iff_quotient_reduced`), each piece is reduced
  (`Spec` instance), and the subscheme is reduced (`IsReduced.of_openCover`).
-/
import ZInQKernel.Contrib.CloudR2NOS.Step1.GrpObjOfMono

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace ZInQ.Contrib.CloudR2NOS.Step1

theorem isReducedSubschemeVanishingIdeal : IsReducedSubschemeVanishingIdeal.{u} := by
  intro X Z
  refine @IsReduced.of_openCover _
    (Scheme.IdealSheafData.vanishingIdeal Z).subschemeCover.openCover (fun U => ?_)
  -- STEP-F11: the cover is indexed by the affine opens; name the index at that type, so that
  -- `ideal`, the coercion to an open, and `Γ(X, _)` all elaborate.
  let V : X.affineOpens := U
  have hrad : ((Scheme.IdealSheafData.vanishingIdeal Z).ideal V).IsRadical := by
    rw [Scheme.IdealSheafData.vanishingIdeal_ideal]
    exact PrimeSpectrum.isRadical_vanishingIdeal _
  haveI : _root_.IsReduced (Γ(X, V.1) ⧸ (Scheme.IdealSheafData.vanishingIdeal Z).ideal V) :=
    (Ideal.isRadical_iff_quotient_reduced _).mp hrad
  exact (inferInstance : IsReduced (Spec (CommRingCat.of
    (Γ(X, V.1) ⧸ (Scheme.IdealSheafData.vanishingIdeal Z).ideal V))))

/-- The constructor with all of its own obligations discharged; it rests only on C5's
`GeomReducedOverAlgClosed`. -/
theorem reducedSubgroupOfClosedSubset_final (hGR : GeomReducedOverAlgClosed.{u}) :
    ReducedSubgroupOfClosedSubset.{u} :=
  reducedSubgroupOfClosedSubset isReducedSubschemeVanishingIdeal grpObjOfCompatibleMono hGR

end ZInQ.Contrib.CloudR2NOS.Step1
