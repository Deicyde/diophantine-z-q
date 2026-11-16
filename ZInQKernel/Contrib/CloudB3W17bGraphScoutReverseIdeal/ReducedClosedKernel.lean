/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in LICENSE in this directory.

The reduced-subscheme proof is selected/adapted from chrisflav/oka at
9a9fc315498d58484ac1abc9668548212eb7c1ff,
Oka/AlgebraicGeometry/Modules/Support.lean, lines 260–270.
The point-density and kernel-subgroup constructions below are new composites
of the native APIs and the frozen reduced-support lift.
-/
import ZInQKernel.Contrib.CloudB3W17bGraphScout.ReducedSupportLift
import ZInQKernel.OneProof.H.TailP

/-!
A reduced closed subscheme whose ACTUAL complex points are the kernel of a
point-group homomorphism acquires an ACTUAL algebraic group structure.
Reducedness of its product is an explicit remaining pure-algebraic obligation;
no GrpObj is assumed on the extracted closed subscheme.
-/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open TopologicalSpace

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace ZInQ.Contrib.CloudB3W17bGraphScoutReverseIdeal

abbrev SchemeCPoints (X : Over (Spec (.of ℂ))) := Over.mk (𝟙 (Spec (.of ℂ))) ⟶ X

abbrev reducedClosedOver (P : Over (Spec (.of ℂ))) (Z : Closeds P.left) :
    Over (Spec (.of ℂ)) :=
  Over.mk ((Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫ P.hom)

abbrev reducedClosedι (P : Over (Spec (.of ℂ))) (Z : Closeds P.left) :
    reducedClosedOver P Z ⟶ P :=
  Over.homMk (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι rfl

/-- The reduced induced closed structure really is reduced. -/
theorem vanishingSubscheme_isReduced {Y : Scheme} (Z : Closeds Y) :
    IsReduced (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := by
  letI (U : Y.affineOpens) :
      _root_.IsReduced (Γ(Y, U) ⧸ (Scheme.IdealSheafData.vanishingIdeal Z).ideal U) := by
    rw [Scheme.IdealSheafData.vanishingIdeal_ideal]
    exact (Ideal.isRadical_iff_quotient_reduced _).mp (PrimeSpectrum.isRadical_vanishingIdeal _)
  letI (U : Y.affineOpens) :
      IsReduced ((Scheme.IdealSheafData.vanishingIdeal Z).subschemeCover.openCover.X U) :=
    inferInstanceAs (IsReduced (Spec (.of
      (Γ(Y, U) ⧸ (Scheme.IdealSheafData.vanishingIdeal Z).ideal U))))
  exact IsReduced.of_openCover (X := _)
    (Scheme.IdealSheafData.vanishingIdeal Z).subschemeCover.openCover

instance reducedClosedOver_isReduced (P : Over (Spec (.of ℂ))) (Z : Closeds P.left) :
    IsReduced (reducedClosedOver P Z).left := vanishingSubscheme_isReduced Z

instance reducedClosedι_isClosedImmersion (P : Over (Spec (.of ℂ))) (Z : Closeds P.left) :
    IsClosedImmersion (reducedClosedι P Z).left := inferInstanceAs
      (IsClosedImmersion (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι)

instance reducedClosedOver_locallyOfFiniteType (P : Over (Spec (.of ℂ)))
    [LocallyOfFiniteType P.hom] (Z : Closeds P.left) :
    LocallyOfFiniteType (reducedClosedOver P Z).hom := by
  change LocallyOfFiniteType ((Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫ P.hom)
  infer_instance

lemma reducedClosedι_apply_mem (P : Over (Spec (.of ℂ))) (Z : Closeds P.left)
    (z : (reducedClosedOver P Z).left) : (reducedClosedι P Z).left z ∈ Z := by
  have h : (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι z ∈
      Set.range (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι := ⟨z, rfl⟩
  rw [Scheme.IdealSheafData.range_subschemeι] at h
  change (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι z ∈ (Z : Set P.left)
  simpa only [Scheme.IdealSheafData.coe_support_vanishingIdeal] using h

/-- Complex closed points control range containment in an ALREADY Zariski-closed subset. -/
theorem range_subset_of_complexPoints
    {W P : Over (Spec (.of ℂ))} [LocallyOfFiniteType W.hom]
    (Z : Closeds P.left) (f : W ⟶ P)
    (hf : ∀ t : SchemeCPoints W, f.left (t.left (IsLocalRing.closedPoint ℂ)) ∈ Z) :
    Set.range f.left ⊆ (Z : Set P.left) := by
  haveI : JacobsonSpace W.left := LocallyOfFiniteType.jacobsonSpace W.hom
  have hc : IsClosed (f.left ⁻¹' (Z : Set P.left)) := Z.2.preimage f.left.continuous
  have hpts : closedPoints W.left ⊆ f.left ⁻¹' (Z : Set P.left) := by
    intro w hw
    let t : SchemeCPoints W :=
      Over.homMk (pointOfClosedPoint W.hom w hw) (pointOfClosedPoint_comp W.hom w hw)
    have ht : t.left (IsLocalRing.closedPoint ℂ) = w :=
      pointOfClosedPoint_apply W.hom w hw (IsLocalRing.closedPoint ℂ)
    change f.left w ∈ Z
    simpa only [ht] using hf t
  have hall : closure (closedPoints W.left) ⊆ f.left ⁻¹' (Z : Set P.left) :=
    hc.closure_subset_iff.mpr hpts
  rw [closure_closedPoints] at hall
  rintro _ ⟨w, rfl⟩
  exact hall (Set.mem_univ w)

/-- The actual OVER-scheme lift, from actual complex-point containment and source reducedness. -/
theorem exists_overLift_reducedClosed_of_complexPoints
    {W P : Over (Spec (.of ℂ))} [LocallyOfFiniteType W.hom] [IsReduced W.left]
    (Z : Closeds P.left) (f : W ⟶ P)
    (hf : ∀ t : SchemeCPoints W, f.left (t.left (IsLocalRing.closedPoint ℂ)) ∈ Z) :
    ∃ g : W ⟶ reducedClosedOver P Z, g ≫ reducedClosedι P Z = f := by
  obtain ⟨g, hg⟩ :=
    ZInQ.Contrib.CloudB3W17bGraphScout.exists_lift_reducedClosed_of_range_subset Z f.left
      (range_subset_of_complexPoints Z f hf)
  refine ⟨Over.homMk g ?_, ?_⟩
  · change g ≫ (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫ P.hom = W.hom
    rw [← Category.assoc, hg]
    exact f.w
  · ext1
    exact hg

lemma point_eq_image_mem {W P : Over (Spec (.of ℂ))} (Z : Closeds P.left)
    (f : W ⟶ P) (t : SchemeCPoints W) (w : SchemeCPoints (reducedClosedOver P Z))
    (hw : w ≫ reducedClosedι P Z = t ≫ f) :
    f.left (t.left (IsLocalRing.closedPoint ℂ)) ∈ Z := by
  have he := congrArg (fun q : SchemeCPoints P => q.left (IsLocalRing.closedPoint ℂ)) hw
  change (reducedClosedι P Z).left (w.left (IsLocalRing.closedPoint ℂ)) =
    f.left (t.left (IsLocalRing.closedPoint ℂ)) at he
  rw [← he]
  exact reducedClosedι_apply_mem P Z _

/-- Membership of an actual complex point in the closed support is equivalent to an
actual lift through its reduced closed subscheme. No analytic model of Γ is needed. -/
theorem complexPoint_mem_iff_lift_reducedClosed
    (P : Over (Spec (.of ℂ))) (Z : Closeds P.left) (u : SchemeCPoints P) :
    u.left (IsLocalRing.closedPoint ℂ) ∈ Z ↔
      ∃ t : SchemeCPoints (reducedClosedOver P Z), t ≫ reducedClosedι P Z = u := by
  constructor
  · intro hu
    haveI : LocallyOfFiniteType (Over.mk (𝟙 (Spec (.of ℂ)))).hom := by
      change LocallyOfFiniteType (𝟙 (Spec (.of ℂ)))
      infer_instance
    haveI : IsReduced (Over.mk (𝟙 (Spec (.of ℂ)))).left :=
      inferInstanceAs (IsReduced (Spec (.of ℂ)))
    exact exists_overLift_reducedClosed_of_complexPoints Z u (by
      intro t
      have ht : t = 𝟙 (Over.mk (𝟙 (Spec (.of ℂ)))) := toUnit_unique _ _
      rw [ht]
      change u.left (IsLocalRing.closedPoint ℂ) ∈ Z
      exact hu)
  · rintro ⟨t, ht⟩
    have he := congrArg (fun q : SchemeCPoints P => q.left (IsLocalRing.closedPoint ℂ)) ht
    change (reducedClosedι P Z).left (t.left (IsLocalRing.closedPoint ℂ)) =
      u.left (IsLocalRing.closedPoint ℂ) at he
    rw [← he]
    exact reducedClosedι_apply_mem P Z _

/-- Unit, multiplication and inverse are CONSTRUCTED as actual algebraic morphisms from
kernel stability of actual complex points. Product reducedness is explicit, not inferred
from a group structure that has not yet been built. -/
theorem exists_groupFactors_of_pointKernel
    (P : Over (Spec (.of ℂ))) [GrpObj P] [LocallyOfFiniteType P.hom] (Z : Closeds P.left)
    {K : Type*} [Group K] (H : SchemeCPoints P →* K)
    (hker : ∀ u : SchemeCPoints P, H u = 1 ↔
      ∃ t : SchemeCPoints (reducedClosedOver P Z), t ≫ reducedClosedι P Z = u)
    [IsReduced ((reducedClosedOver P Z ⊗ reducedClosedOver P Z).left)] :
    ∃ (m : reducedClosedOver P Z ⊗ reducedClosedOver P Z ⟶ reducedClosedOver P Z)
      (e : 𝟙_ (Over (Spec (.of ℂ))) ⟶ reducedClosedOver P Z)
      (v : reducedClosedOver P Z ⟶ reducedClosedOver P Z),
      m ≫ reducedClosedι P Z = fst _ _ ≫ reducedClosedι P Z * snd _ _ ≫ reducedClosedι P Z ∧
      e ≫ reducedClosedι P Z = η[P] ∧ v ≫ reducedClosedι P Z = (reducedClosedι P Z)⁻¹ := by
  let G := reducedClosedOver P Z
  let j := reducedClosedι P Z
  haveI : LocallyOfFiniteType G.hom := by
    dsimp only [G]
    infer_instance
  haveI : LocallyOfFiniteType (G ⊗ G).hom := by
    change LocallyOfFiniteType (pullback.fst G.hom G.hom ≫ G.hom)
    infer_instance
  let mp : G ⊗ G ⟶ P := fst G G ≫ j * snd G G ≫ j
  obtain ⟨m, hm⟩ := exists_overLift_reducedClosed_of_complexPoints Z mp (by
    intro t
    have ha : H (t ≫ fst G G ≫ j) = 1 := by
      have hh : H ((t ≫ fst G G) ≫ j) = 1 := (hker _).mpr ⟨t ≫ fst G G, rfl⟩
      simpa only [Category.assoc] using hh
    have hb : H (t ≫ snd G G ≫ j) = 1 := by
      have hh : H ((t ≫ snd G G) ≫ j) = 1 := (hker _).mpr ⟨t ≫ snd G G, rfl⟩
      simpa only [Category.assoc] using hh
    have hmul : H (t ≫ mp) = 1 := by
      simp only [mp, MonObj.comp_mul, map_mul]
      rw [ha, hb, _root_.one_mul]
    obtain ⟨w, hw⟩ := (hker _).mp hmul
    exact point_eq_image_mem Z mp t w hw)
  obtain ⟨e, he⟩ := (hker 1).mp (map_one H)
  have hunit : (1 : SchemeCPoints P) = η[P] := by
    rw [Hom.one_def, show toUnit (Over.mk (𝟙 (Spec (.of ℂ)))) =
      𝟙 (Over.mk (𝟙 (Spec (.of ℂ)))) from toUnit_unique _ _, Category.id_comp]
  obtain ⟨v, hv⟩ := exists_overLift_reducedClosed_of_complexPoints Z j⁻¹ (by
    intro t
    have ha : H (t ≫ j) = 1 := (hker _).mpr ⟨t, rfl⟩
    have hinv : H (t ≫ j⁻¹) = 1 := by
      rw [GrpObj.comp_inv, map_inv, ha, inv_one]
    obtain ⟨w, hw⟩ := (hker _).mp hinv
    exact point_eq_image_mem Z j⁻¹ t w hw)
  exact ⟨m, e, v, hm, he.trans hunit, hv⟩

/-- An ACTUAL group object on the reduced closed kernel, without assuming one there. -/
@[reducible] def reducedClosedKernelGrp
    (P : Over (Spec (.of ℂ))) [GrpObj P] [LocallyOfFiniteType P.hom] (Z : Closeds P.left)
    {K : Type*} [Group K] (H : SchemeCPoints P →* K)
    (hker : ∀ u : SchemeCPoints P, H u = 1 ↔
      ∃ t : SchemeCPoints (reducedClosedOver P Z), t ≫ reducedClosedι P Z = u)
    [IsReduced ((reducedClosedOver P Z ⊗ reducedClosedOver P Z).left)] :
    GrpObj (reducedClosedOver P Z) :=
  let h := exists_groupFactors_of_pointKernel P Z H hker
  let m := h.choose
  let e := h.choose_spec.choose
  let v := h.choose_spec.choose_spec.choose
  let eqs := h.choose_spec.choose_spec.choose_spec
  AVGlue.grpObjOfMono (reducedClosedι P Z) m eqs.1 e eqs.2.1 v eqs.2.2

/-- The actual closed inclusion is a group homomorphism for the constructed structure. -/
theorem isMonHom_reducedClosedKernelGrp
    (P : Over (Spec (.of ℂ))) [GrpObj P] [LocallyOfFiniteType P.hom] (Z : Closeds P.left)
    {K : Type*} [Group K] (H : SchemeCPoints P →* K)
    (hker : ∀ u : SchemeCPoints P, H u = 1 ↔
      ∃ t : SchemeCPoints (reducedClosedOver P Z), t ≫ reducedClosedι P Z = u)
    [IsReduced ((reducedClosedOver P Z ⊗ reducedClosedOver P Z).left)] :
    letI := reducedClosedKernelGrp P Z H hker
    IsMonHom (reducedClosedι P Z) := by
  let h := exists_groupFactors_of_pointKernel P Z H hker
  exact AVGlue.isMonHom_grpObjOfMono (reducedClosedι P Z) h.choose
    h.choose_spec.choose_spec.choose_spec.1 h.choose_spec.choose
    h.choose_spec.choose_spec.choose_spec.2.1 h.choose_spec.choose_spec.choose
    h.choose_spec.choose_spec.choose_spec.2.2

/-- Direct extraction consumer: the actual closed support is the point-kernel of H.
It constructs the group object, rather than assuming group structure or point lifting. -/
@[reducible] def reducedClosedSupportKernelGrp
    (P : Over (Spec (.of ℂ))) [GrpObj P] [LocallyOfFiniteType P.hom] (Z : Closeds P.left)
    {K : Type*} [Group K] (H : SchemeCPoints P →* K)
    (hker : ∀ u : SchemeCPoints P, H u = 1 ↔ u.left (IsLocalRing.closedPoint ℂ) ∈ Z)
    [IsReduced ((reducedClosedOver P Z ⊗ reducedClosedOver P Z).left)] :
    GrpObj (reducedClosedOver P Z) :=
  reducedClosedKernelGrp P Z H (fun u =>
    (hker u).trans (complexPoint_mem_iff_lift_reducedClosed P Z u))

/-- The actual closed inclusion for the direct support-kernel consumer is a homomorphism. -/
theorem isMonHom_reducedClosedSupportKernelGrp
    (P : Over (Spec (.of ℂ))) [GrpObj P] [LocallyOfFiniteType P.hom] (Z : Closeds P.left)
    {K : Type*} [Group K] (H : SchemeCPoints P →* K)
    (hker : ∀ u : SchemeCPoints P, H u = 1 ↔ u.left (IsLocalRing.closedPoint ℂ) ∈ Z)
    [IsReduced ((reducedClosedOver P Z ⊗ reducedClosedOver P Z).left)] :
    letI := reducedClosedSupportKernelGrp P Z H hker
    IsMonHom (reducedClosedι P Z) :=
  isMonHom_reducedClosedKernelGrp P Z H (fun u =>
    (hker u).trans (complexPoint_mem_iff_lift_reducedClosed P Z u))

end ZInQ.Contrib.CloudB3W17bGraphScoutReverseIdeal
