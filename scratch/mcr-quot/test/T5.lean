import Mathlib

open CategoryTheory AlgebraicGeometry Limits

namespace T5

noncomputable abbrev ptOf {K : Type} [Field K] {X : Scheme.{0}} (p : Spec (CommRingCat.of K) ⟶ X) : X :=
  (Scheme.SpecToEquivOfField K X p).1

/-- The residue field map of a closed immersion is an isomorphism. -/
theorem isIso_residueFieldMap_of_isClosedImmersion {X Y : Scheme.{0}} (f : X ⟶ Y)
    [IsClosedImmersion f] (x : X) : IsIso (f.residueFieldMap x) := by
  have hs : Function.Surjective (f.residueFieldMap x) := by
    intro a
    obtain ⟨b, rfl⟩ := X.residue_surjective x a
    obtain ⟨c, rfl⟩ := f.stalkMap_surjective x b
    refine ⟨Y.residue (f x) c, ?_⟩
    rw [← ConcreteCategory.comp_apply, Scheme.residue_residueFieldMap]
    rfl
  have hb : Function.Bijective (f.residueFieldMap x) := ⟨(f.residueFieldMap x).hom.injective, hs⟩
  exact (ConcreteCategory.isIso_iff_bijective _).2 hb

/-- A field point whose point lies in the range of a closed immersion factors through it. -/
theorem exists_factor_of_mem_range {X Y : Scheme.{0}} (f : X ⟶ Y) [IsClosedImmersion f]
    {K : Type} [Field K] (t : Spec (CommRingCat.of K) ⟶ Y) (ht : ptOf t ∈ Set.range f) :
    ∃ t' : Spec (CommRingCat.of K) ⟶ X, t' ≫ f = t := by
  obtain ⟨e, he⟩ := ht
  have := isIso_residueFieldMap_of_isClosedImmersion f e
  set xf := Scheme.SpecToEquivOfField K Y t with hxf
  have ht' : t = Spec.map xf.2 ≫ Y.fromSpecResidueField xf.1 :=
    ((Scheme.SpecToEquivOfField K Y).symm_apply_apply t).symm
  have h1 : Y.fromSpecResidueField (f e) =
      Spec.map (inv (f.residueFieldMap e)) ≫ X.fromSpecResidueField e ≫ f := by
    rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← Category.assoc,
      ← Spec.map_comp, IsIso.hom_inv_id, Spec.map_id, Category.id_comp]
  refine ⟨Spec.map xf.2 ≫ Spec.map (Y.residueFieldCongr he).hom ≫
    Spec.map (inv (f.residueFieldMap e)) ≫ X.fromSpecResidueField e, ?_⟩
  refine Eq.trans ?_ ht'.symm
  simp only [Category.assoc]
  rw [← h1, Scheme.residueFieldCongr_fromSpecResidueField]

/-- **(C1c) core**: an automorphism `h` over `S` of a separated `S`-scheme fixing a field point
`y` fixes every field point whose point lies in the closure of the point of `y`. -/
theorem fixes_closure {S : Scheme.{0}} (X : Over S) [IsSeparated X.hom] (h : X.left ≅ X.left)
    (hh : h.hom ≫ X.hom = X.hom) {K₀ : Type} [Field K₀] (y : Spec (CommRingCat.of K₀) ⟶ X.left)
    (hy : y ≫ h.hom = y) {K : Type} [Field K] (t : Spec (CommRingCat.of K) ⟶ X.left)
    (ht : ptOf t ∈ closure {ptOf y}) : t ≫ h.hom = t := by
  let f : X ⟶ X := Over.homMk h.hom hh
  let g : X ⟶ X := 𝟙 X
  let ι := (equalizer.ι f g).left
  have hι : ι ≫ h.hom = ι := by
    have := congrArg CommaMorphism.left (equalizer.condition f g)
    simpa [f, g, ι] using this
  have hcl : IsClosed (Set.range ι) := ι.isClosedEmbedding.isClosed_range
  have hyr : ptOf y ∈ Set.range ι := by
    let y' : Over.mk (y ≫ X.hom) ⟶ X := Over.homMk y rfl
    have hc : y' ≫ f = y' ≫ g := by
      ext1; simpa [f, g, y'] using hy
    refine ⟨(equalizer.lift y' hc).left (IsLocalRing.closedPoint K₀), ?_⟩
    show ((equalizer.lift y' hc).left ≫ (equalizer.ι f g).left) _ = _
    rw [← Over.comp_left, equalizer.lift_ι]
    rfl
  have htr : ptOf t ∈ Set.range ι :=
    (closure_minimal (Set.singleton_subset_iff.2 hyr) hcl) ht
  obtain ⟨t', rfl⟩ := exists_factor_of_mem_range ι t htr
  rw [Category.assoc, hι]

end T5
