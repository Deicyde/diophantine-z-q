/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop_fiberToSpecResidueField
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop_fiberToSpecResidueField

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace FibreIdentGC3

theorem bijective_of_bijective_comp_iso {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) [IsIso g]
    (h : Function.Bijective (f ≫ g)) : Function.Bijective f := by
  haveI : IsIso (f ≫ g) := (ConcreteCategory.isIso_iff_bijective _).mpr h
  haveI : IsIso f := IsIso.of_isIso_comp_right f g
  exact ConcreteCategory.bijective_of_isIso f

theorem bijective_of_iso_comp_bijective {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) [IsIso f]
    (h : Function.Bijective (f ≫ g)) : Function.Bijective g := by
  haveI : IsIso (f ≫ g) := (ConcreteCategory.isIso_iff_bijective _).mpr h
  haveI : IsIso g := IsIso.of_isIso_comp_left f g
  exact ConcreteCategory.bijective_of_isIso g

theorem bijective_comp_of_bijective {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) [IsIso g]
    (h : Function.Bijective f) : Function.Bijective (f ≫ g) := by
  haveI : IsIso f := (ConcreteCategory.isIso_iff_bijective _).mpr h
  exact ConcreteCategory.bijective_of_isIso (f ≫ g)

theorem bijective_iso_comp_of_bijective {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) [IsIso f]
    (h : Function.Bijective g) : Function.Bijective (f ≫ g) := by
  haveI : IsIso g := (ConcreteCategory.isIso_iff_bijective _).mpr h
  exact ConcreteCategory.bijective_of_isIso (f ≫ g)

theorem bijective_appTop_of_iso_over {P P' S : Scheme.{u}} (e : P ≅ P') (s : P ⟶ S) (s' : P' ⟶ S)
    (he : e.hom ≫ s' = s) (h : Function.Bijective s'.appTop) : Function.Bijective s.appTop := by
  rw [← he, Scheme.Hom.comp_appTop]
  haveI : IsIso e.hom.appTop := (inferInstance : IsIso (e.hom.app ⊤))
  exact bijective_comp_of_bijective _ _ h

end FibreIdentGC3

theorem solution
    {X Y : Scheme.{u}} (q : X ⟶ Y) [QuasiCompact q] [QuasiSeparated q]
    {K : Type u} [Field K] (k : Spec (CommRingCat.of K) ⟶ Y)
    (h : Function.Bijective (q.fiberToSpecResidueField (k.base (IsLocalRing.closedPoint K))).appTop) :
    Function.Bijective (pullback.snd q k).appTop := by
  set y := k.base (IsLocalRing.closedPoint K) with hy

  let φ : Y.residueField y ⟶ CommRingCat.of K := Y.descResidueField (Scheme.stalkClosedPointTo k)
  have hk : Spec.map φ ≫ Y.fromSpecResidueField y = k :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K Y k

  haveI : QuasiSeparatedSpace ↥(q.fiber y) :=
    haveI : QuasiSeparated (q.fiberToSpecResidueField y) := MorphismProperty.pullback_snd _ _ inferInstance
    HasAffineProperty.iff_of_isAffine (P := @QuasiSeparated) (f := q.fiberToSpecResidueField y) |>.mp inferInstance

  have h0 : Function.Bijective ((Scheme.ΓSpecIso (Y.residueField y)).inv ≫ (q.fiberToSpecResidueField y).appTop) :=
    FibreIdentGC3.bijective_iso_comp_of_bijective _ _ h

  letI : Algebra (Y.residueField y) K := φ.hom.toAlgebra
  have h1 := AlgebraicGeometry.bijective_appTop_pullback_snd_of_bijective_appTop
    (k := Y.residueField y) (q.fiberToSpecResidueField y) h0 K

  have hφ : CommRingCat.ofHom (algebraMap (Y.residueField y) K) = φ := rfl
  rw [hφ] at h1
  have h2 : Function.Bijective (pullback.snd (q.fiberToSpecResidueField y) (Spec.map φ)).appTop :=
    FibreIdentGC3.bijective_of_iso_comp_bijective _ _ h1

  let e : pullback (q.fiberToSpecResidueField y) (Spec.map φ) ≅ pullback q k :=
    pullbackLeftPullbackSndIso q (Y.fromSpecResidueField y) (Spec.map φ) ≪≫ pullback.congrHom rfl hk
  have he : e.hom ≫ pullback.snd q k = pullback.snd (q.fiberToSpecResidueField y) (Spec.map φ) := by
    simp only [e, Iso.trans_hom, pullback.congrHom_hom, Category.assoc]
    erw [pullback.lift_snd, Category.comp_id, pullbackLeftPullbackSndIso_hom_snd]
    rfl
  exact FibreIdentGC3.bijective_appTop_of_iso_over e.symm _ _ (by rw [Iso.symm_hom, Iso.inv_comp_eq, he]) h2
