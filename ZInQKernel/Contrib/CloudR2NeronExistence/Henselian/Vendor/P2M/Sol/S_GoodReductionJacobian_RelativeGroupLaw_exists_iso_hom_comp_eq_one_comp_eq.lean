import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_exists_iso_hom_comp_eq_one_comp_eq.lean
Original Git blob: 09cb2f5e892720a289f71eb836b7d438330373f9
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
* Explicitly closed 1 scopes originally left open at EOF.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "AlgebraicGeometry CategoryTheory"
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_iso_hom_comp_eq_one_comp_eq
h77_bridge_namespace

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

noncomputable section

namespace TranslateAutGC3
h77_bridge_namespace

variable {k : Type u} [CommRing k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)} (L : RelativeGroupLaw k f)

abbrev idPt (f : G ⟶ Spec (CommRingCat.of k)) : SchemeHomOver f f := ⟨𝟙 G, Category.id_comp f⟩

def const (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) :
    SchemeHomOver t f :=
  schemeHomOverComp t (Category.comp_id t) a

@[scoped simp] theorem const_coe (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of k)) : (const a t).1 = t ≫ a.1 := rfl

theorem comp_const (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) {T T' : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of k)) (t' : T' ⟶ Spec (CommRingCat.of k)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') :
    schemeHomOverComp ψ hψ (const a t) = const a t' := by
  apply Subtype.ext
  show ψ ≫ (t ≫ a.1) = t' ≫ a.1
  rw [← Category.assoc, hψ]

def rt (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) : G ⟶ G :=
  (L.mul f (idPt f) (const a f)).1

theorem rt_over (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) : rt L a ≫ f = f :=
  (L.mul f (idPt f) (const a f)).2

theorem comp_rt (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t f) :
    P.1 ≫ rt L a = (L.mul t P (const a t)).1 := by
  have hP : schemeHomOverComp P.1 P.2 (idPt f) = P := Subtype.ext (Category.comp_id _)
  have := L.mul_natural f t P.1 P.2 (idPt f) (const a f)
  rw [hP, comp_const] at this
  rw [← this]
  rfl

theorem rt_mul (a b : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :
    rt L a ≫ rt L b = rt L (L.mul (𝟙 _) a b) := by
  have h1 : rt L a ≫ rt L b = (L.mul f (L.mul f (idPt f) (const a f)) (const b f)).1 := by
    rw [← comp_rt L b f]; rfl
  rw [h1, L.mul_assoc]
  have h2 : L.mul f (const a f) (const b f) = const (L.mul (𝟙 _) a b) f := by
    simp only [const]
    rw [← L.mul_natural (𝟙 _) f f (Category.comp_id f)]
  rw [h2]; rfl

theorem rt_one : rt L (L.one (𝟙 _)) = 𝟙 G := by
  have : const (L.one (𝟙 (Spec (CommRingCat.of k)))) f = L.one f := L.one_natural (𝟙 _) f f (Category.comp_id f)
  show (L.mul f (idPt f) (const (L.one (𝟙 _)) f)).1 = 𝟙 G
  rw [this, L.mul_one]

def rtIso (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) : G ≅ G where
  hom := rt L a
  inv := rt L (L.inv (𝟙 _) a)
  hom_inv_id := by rw [rt_mul, L.mul_inv_cancel, rt_one]
  inv_hom_id := by rw [rt_mul, L.inv_mul_cancel, rt_one]

scoped instance (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) : IsIso (rt L a) := (rtIso L a).isIso_hom

end TranslateAutGC3
h77_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_iso_hom_comp_eq_one_comp_eq.TranslateAutGC3"

end
h77_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_iso_hom_comp_eq_one_comp_eq.TranslateAutGC3"

theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} {g : X ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R g)
    (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) g) :
    ∃ τ : X ≅ X, τ.hom ≫ g = g ∧ (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ τ.hom = a.1 := by
  refine ⟨TranslateAutGC3.rtIso L a, TranslateAutGC3.rt_over L a, ?_⟩
  show (L.one (𝟙 _)).1 ≫ TranslateAutGC3.rt L a = a.1
  rw [TranslateAutGC3.comp_rt, L.one_mul]
  show 𝟙 _ ≫ a.1 = a.1
  rw [Category.id_comp]


end P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_iso_hom_comp_eq_one_comp_eq
end ZInQ.Contrib.CloudR2NeronExistence.Henselian
