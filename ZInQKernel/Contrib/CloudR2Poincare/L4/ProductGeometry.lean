import ZInQKernel.Contrib.CloudR2Poincare.L4.KernelGeometry

/-!
# The actual product fibre over a rational identity section

H-72 round 2, lane L4. Everything here is Mathlib-only and uses the actual scheme
pullbacks underlying the Cartesian tensor in `Over (Spec k)`.

SOURCE / CHANGE NOTICE: the four-line proof that a stalk-surjective morphism
induces a bijection of residue fields is adapted from AxiomMath/Stacks
`c496df0d9beea9deaeabcea8492605f9a0a2313b`,
`StacksFrontier/AlgebraicGeometry/F6Rank128/FiberResidueField.lean:73–79`.
Apache-2.0; see the accompanying `LICENSE.Stacks`.
-/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

noncomputable section

namespace ZInQ.Contrib.CloudR2Poincare.L4

set_option linter.style.haveILetI false

universe u

/-- A morphism surjective on stalks induces an isomorphism of residue fields. -/
theorem residueFieldMap_isIso_of_surjectiveOnStalks {X Y : Scheme.{u}}
    (i : Y ⟶ X) [SurjectiveOnStalks i] (y : Y) : IsIso (i.residueFieldMap y) := by
  have hb : Function.Bijective (i.residueFieldMap y).hom := by
    refine ⟨(i.residueFieldMap y).hom.injective, ?_⟩
    have h := (Y.residue_surjective y).comp (i.stalkMap_surjective y)
    change Function.Surjective (i.stalkMap y ≫ Y.residue y).hom at h
    rw [← Scheme.residue_residueFieldMap i y, CommRingCat.hom_comp, RingHom.coe_comp] at h
    exact h.of_comp
  let e := RingEquiv.ofBijective (i.residueFieldMap y).hom hb
  exact e.toCommRingCatIso.isIso_hom

/-- The spectrum of a field is canonically the spectrum of its residue field at any point. -/
theorem isIso_fromSpecResidueField_spec {k : Type u} [Field k] (x : Spec (.of k)) :
    IsIso ((Spec (.of k)).fromSpecResidueField x) := by
  haveI : IsClosedImmersion ((Spec (.of k)).fromSpecResidueField x) :=
    isClosed_singleton_iff_isClosedImmersion.mp (isClosed_discrete _)
  haveI : Surjective ((Spec (.of k)).fromSpecResidueField x) :=
    ⟨fun y => ⟨IsLocalRing.closedPoint ((Spec (.of k)).residueField x), Subsingleton.elim _ _⟩⟩
  exact isIso_of_isClosedImmersion_of_surjective _

/-- The domain of a closed rational point agrees with the spectrum of the residue field of its image. -/
def rationalPointResidueIso {k : Type u} [Field k] {X : Scheme.{u}}
    (i : Spec (.of k) ⟶ X) [IsClosedImmersion i] (x : Spec (.of k)) :
    Spec (X.residueField (i x)) ≅ Spec (.of k) :=
  haveI := residueFieldMap_isIso_of_surjectiveOnStalks i x
  haveI := isIso_fromSpecResidueField_spec x
  (asIso (Spec.map (i.residueFieldMap x))).symm ≪≫
    asIso ((Spec (.of k)).fromSpecResidueField x)

@[reassoc]
lemma rationalPointResidueIso_hom_i {k : Type u} [Field k] {X : Scheme.{u}}
    (i : Spec (.of k) ⟶ X) [IsClosedImmersion i] (x : Spec (.of k)) :
    (rationalPointResidueIso i x).hom ≫ i = X.fromSpecResidueField (i x) := by
  haveI := residueFieldMap_isIso_of_surjectiveOnStalks i x
  haveI := isIso_fromSpecResidueField_spec x
  change inv (Spec.map (i.residueFieldMap x)) ≫
    (Spec (.of k)).fromSpecResidueField x ≫ i = _
  rw [IsIso.inv_comp_eq]
  exact (Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField i x).symm

variable {k : Type u} [Field k]

/-- Pulling a product projection back along a section gives the other factor. -/
def sectionPullbackIso {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (i : S ⟶ X) (hi : i ≫ f = 𝟙 S) :
    pullback (pullback.fst f g) i ≅ Y :=
  pullbackSymmetry _ _ ≪≫ pullbackRightPullbackFstIso f g i ≪≫
    pullback.congrHom hi rfl ≪≫ asIso (pullback.snd (𝟙 S) g)

lemma sectionPullbackIso_hom {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (i : S ⟶ X) (hi : i ≫ f = 𝟙 S) :
    (sectionPullbackIso f g i hi).hom =
      pullback.fst (pullback.fst f g) i ≫ pullback.snd f g := by
  simp [sectionPullbackIso, pullback.congrHom]

/-- The scheme-theoretic fibre of a product projection over a rational section is the other factor. -/
def sectionFibreIso {k : Type u} [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    (i : Spec (.of k) ⟶ X) [IsClosedImmersion i] (hi : i ≫ f = 𝟙 _) (x : Spec (.of k)) :
    (pullback.fst f g).fiber (i x) ≅ Y :=
  let e := rationalPointResidueIso i x
  let m := pullback.map (pullback.fst f g) (X.fromSpecResidueField (i x))
    (pullback.fst f g) i (𝟙 _) e.hom (𝟙 _)
    (by simp) (by simpa using (rationalPointResidueIso_hom_i i x).symm)
  have hm : IsIso m := pullback.map_isIso _ _ _ _ _ _ _ _ _
  @asIso _ _ _ _ m hm ≪≫ sectionPullbackIso f g i hi

lemma sectionFibreIso_hom {k : Type u} [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    (i : Spec (.of k) ⟶ X) [IsClosedImmersion i] (hi : i ≫ f = 𝟙 _) (x : Spec (.of k)) :
    (sectionFibreIso f g i hi x).hom =
      (pullback.fst f g).fiberι (i x) ≫ pullback.snd f g := by
  dsimp only [Scheme.Hom.fiber, sectionFibreIso, Iso.trans_hom, asIso]
  rw [sectionPullbackIso_hom]
  simp [pullback.map, Scheme.Hom.fiberι]

/-- The actual product fibre over the group identity point is the second factor. -/
def productUnitFibreIso (B Z : Over (Spec (.of k))) [GrpObj B] [IsSeparated B.hom]
    (x : Spec (.of k)) :
    ((fst B Z).left).fiber ((η[B]).left x) ≅ Z.left :=
  haveI := isClosedImmersion_eta B
  sectionFibreIso B.hom Z.hom (η[B]).left (by simpa using Over.w (η[B])) x

lemma productUnitFibreIso_hom (B Z : Over (Spec (.of k))) [GrpObj B] [IsSeparated B.hom]
    (x : Spec (.of k)) :
    (productUnitFibreIso B Z x).hom =
      ((fst B Z).left).fiberι ((η[B]).left x) ≫ (snd B Z).left := by
  haveI := isClosedImmersion_eta B
  exact sectionFibreIso_hom B.hom Z.hom (η[B]).left (by simpa using Over.w (η[B])) x

/-- The actual product point specified by the two identity sections. -/
def productUnitPoint (B Z : Over (Spec (.of k))) [GrpObj B] [GrpObj Z]
    (x : Spec (.of k)) : (B ⊗ Z).left := (lift η[B] η[Z]).left x

lemma productUnitPoint_fst (B Z : Over (Spec (.of k))) [GrpObj B] [GrpObj Z]
    (x : Spec (.of k)) : (fst B Z).left (productUnitPoint B Z x) = (η[B]).left x := by
  have he := congrArg Over.Hom.left (lift_fst (η[B]) (η[Z]))
  simp only [Over.comp_left] at he
  exact congrArg (fun h => h x) he

lemma productUnitPoint_snd (B Z : Over (Spec (.of k))) [GrpObj B] [GrpObj Z]
    (x : Spec (.of k)) : (snd B Z).left (productUnitPoint B Z x) = (η[Z]).left x := by
  have he := congrArg Over.Hom.left (lift_snd (η[B]) (η[Z]))
  simp only [Over.comp_left] at he
  exact congrArg (fun h => h x) he

lemma isClosed_unitPoint (B : Over (Spec (.of k))) [GrpObj B] [IsSeparated B.hom]
    (x : Spec (.of k)) : IsClosed ({(η[B]).left x} : Set B.left) := by
  haveI := isClosedImmersion_eta B
  haveI : T1Space (𝟙_ (Over (Spec (.of k)))).left :=
    inferInstanceAs (T1Space (Spec (.of k)))
  rw [← Set.image_singleton]
  exact (η[B]).left.isClosedMap _ isClosed_singleton

/-- Naming a fibre point by its ambient point agrees with the canonical `asFiber` name. -/
lemma ringKrullDim_stalk_fiberHomeo_symm {X Y : Scheme.{u}} (f : X ⟶ Y)
    (x : X) (y : Y) (h : f x = y) :
    ringKrullDim ((f.fiber y).presheaf.stalk ((f.fiberHomeo y).symm ⟨x, h⟩)) =
      ringKrullDim ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) := by
  subst y
  rfl

/-- The dimension of a local ring never exceeds the dimension of its ambient scheme. -/
theorem ringKrullDim_stalk_le_topologicalKrullDim (X : Scheme.{u}) (x : X) :
    ringKrullDim (X.presheaf.stalk x) ≤ topologicalKrullDim X := by
  calc
    ringKrullDim (X.presheaf.stalk x) = topologicalKrullDim (Spec (X.presheaf.stalk x)) :=
      (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _).symm
    _ ≤ topologicalKrullDim X :=
      (X.fromSpecStalk x).isEmbedding.isInducing.topologicalKrullDim_le

end ZInQ.Contrib.CloudR2Poincare.L4
