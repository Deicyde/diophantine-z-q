/-
Copyright (c) 2026 H5 contributors. Apache-2.0.
Native universe-u producer for the EXACT C2 A5 interface, SOURCE ONLY,
UNCOMPILED. Original A, original affine U and its actual identity point stay
unchanged. No line, embedding, FBS, ample/QP, model or regularity Fact is input.

The actual held native W07 regular-UFD theorem has an extra IsRegularRing
hypothesis; it does NOT alone prove the generic A1 RegularLocalUFD. Here that
hypothesis is genuinely DERIVED on every original stalk: A2 proves all
stalks regular, and the native scheme-localization argument identifies prime
localizations of a stalk with the SAME scheme's stalks. Native UFD then
applies, and the native affine-complement theorem constructs a W07 ideal
whose native IsInvertible/support are exactly the consumer's fields.

This is reuse of actual native W07/Mathlib constructors, not the received
Stacks criterion or a Stacks/native predicate bridge. Native third-party
Apache-2.0 LICENSE/NOTICE and c4254cce source headers stay unchanged.
Current default-limit import/namespace/CI/BI/Std3/native acceptance remains
separate. The independent generic A1, A3, A4 and B2.d2 obligations remain.
-/
import I0SmoothFieldStalkRegular
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Regular
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.IdealSheaf.AffineComplement

set_option autoImplicit false
noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open scoped CategoryTheory.MonObj

namespace H5OriginalDVR.Lane5.I0Native

/-- EXACT C2 A5; all application hypotheses are actual consequences of AV. -/
theorem sameAbVarAffineComplement :
    H5OriginalDVR.Lane2.Step2DelegatedInterfaces.SameAbVarAffineComplement.{u} := by
  intro K _ _ A _ U hU hη
  letI : IsProper A.X.hom := PkgI2.IsAbelianVariety.proper
  letI : Smooth A.X.hom := PkgI2.IsAbelianVariety.smooth
  letI : GeometricallyIntegral A.X.hom := PkgI2.IsAbelianVariety.geomIntegral
  letI : IsLocallyNoetherian A.X.left :=
    LocallyOfFiniteType.isLocallyNoetherian A.X.hom
  letI : CompactSpace A.X.left :=
    QuasiCompact.compactSpace_of_compactSpace A.X.hom
  letI : IsNoetherian A.X.left := {}
  letI : A.X.left.IsSeparated := by
    constructor
    rw [← terminal.comp_from A.X.hom]
    infer_instance
  letI : IsIntegral A.X.left :=
    GeometricallyIntegral.isIntegral_of_subsingleton A.X.hom
  letI : AlgebraicGeometry.IsRegular A.X.left :=
    ⟨fun x => smoothFieldStalkRegular A.X.hom x⟩
  have hUFD : ∀ x : A.X.left,
      UniqueFactorizationMonoid (A.X.left.presheaf.stalk x) :=
    fun x => AlgebraicGeometry.IsRegular.uniqueFactorizationMonoid_stalk x
  have hne : (U : Set A.X.left).Nonempty :=
    ⟨(η[A.X]).left (IsLocalRing.closedPoint K), hη⟩
  exact AlgebraicGeometry.Scheme.exists_isInvertible_support_eq_compl
    A.X.left hUFD hU hne

end H5OriginalDVR.Lane5.I0Native
