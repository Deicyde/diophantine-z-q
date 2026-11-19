import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: P2M/Sol/S_AlgebraicGeometry_Scheme_Hom_exists_basis_kaehlerDifferential_map_of_isAffineOpen_le.lean
Original Git blob: e24eb0e04cba613b5a8ed4636090661034ecf6ad
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
* Explicitly closed 1 scopes originally left open at EOF.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Definitions.Def_AlgebraicGeometry_KaehlerModule
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "AlgebraicGeometry CategoryTheory"
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

namespace P2MW.S_AlgebraicGeometry_Scheme_Hom_exists_basis_kaehlerDifferential_map_of_isAffineOpen_le
h77_bridge_namespace

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u v

theorem solution
    {B : Type u} [CommRing B] {X : Scheme.{u}} (gX : X ⟶ Spec (CommRingCat.of B))
    {W W' : X.Opens} (hW : IsAffineOpen W) (hW' : IsAffineOpen W') (hle : W' ≤ W) {ι : Type v} :
    letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gX) W; letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gX) W'
    letI : Algebra Γ(X, W) Γ(X, W') := (X.presheaf.map (homOfLE hle).op).hom.toAlgebra
    ∀ [IsScalarTower B Γ(X, W) Γ(X, W')] (b : Module.Basis ι Γ(X, W) (Ω[Γ(X, W)⁄B])),
      ∃ b' : Module.Basis ι Γ(X, W') (Ω[Γ(X, W')⁄B]),
        ∀ i, b' i = KaehlerDifferential.map B B Γ(X, W) Γ(X, W') (b i) := by
  letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gX) W; letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gX) W'
  letI : Algebra Γ(X, W) Γ(X, W') := (X.presheaf.map (homOfLE hle).op).hom.toAlgebra
  intro _inst b

  have hEt : RingHom.Etale (X.presheaf.map (homOfLE hle).op).hom := by
    have h := HasRingHomProperty.appLE (P := @Etale) (Q := @RingHom.Etale) (𝟙 X) inferInstance
      ⟨W, hW⟩ ⟨W', hW'⟩ (by simpa using hle)
    simp [Scheme.Hom.appLE] at h
    exact h
  haveI : Algebra.FormallyEtale Γ(X, W) Γ(X, W') := hEt.formallyEtale
  let e := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale B Γ(X, W) Γ(X, W')
  refine ⟨(Algebra.TensorProduct.basis Γ(X, W') b).map e, fun i => ?_⟩
  rw [Module.Basis.map_apply, Algebra.TensorProduct.basis_apply,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply, KaehlerDifferential.mapBaseChange_tmul, one_smul]


end P2MW.S_AlgebraicGeometry_Scheme_Hom_exists_basis_kaehlerDifferential_map_of_isAffineOpen_le
end ZInQ.Contrib.CloudR2NeronExistence.Henselian
