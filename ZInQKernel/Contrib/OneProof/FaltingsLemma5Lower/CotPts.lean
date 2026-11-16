import ZInQKernel.Contrib.OneProof.FaltingsLemma5Lower.Ker

/-! faltings5-lower, part 8: points of a group model through the local ring `𝒪_{𝒢,ξ}` at the origin
`ξ` of the generic fibre. A local ring map `ρ : 𝒪_{𝒢,ξ} → Λ` gives the point `Spec ρ ≫ (Spec 𝒪_{𝒢,ξ} → 𝒢)`
(`ptAt`); this is injective in `ρ`, natural for homomorphisms of group models, and the trivial points
come from the evaluation `ε : 𝒪_{𝒢,ξ} → K` along the unit section. -/

set_option linter.style.haveILetI false

namespace GapHeight

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField ZInQ.DefFaltings

section CotPts

variable {K : Type} [Field K] [NumberField K] {A B : PkgI3.AbVar K}

/-- The point of `𝒢` attached to a ring map out of `𝒪_{𝒢,ξ}`. -/
noncomputable def ptAt (𝒢 : GroupModel A K) {Λ : CommRingCat.{0}} (ρ : 𝒢.genStalk ⟶ Λ) :
    Spec Λ ⟶ 𝒢.G.left :=
  Spec.map ρ ≫ 𝒢.G.left.fromSpecStalk 𝒢.genericUnit

theorem ptAt_injective (𝒢 : GroupModel A K) {Λ : CommRingCat.{0}} [IsLocalRing Λ]
    {ρ ρ' : 𝒢.genStalk ⟶ Λ} [IsLocalHom ρ.hom] [IsLocalHom ρ'.hom] (h : ptAt 𝒢 ρ = ptAt 𝒢 ρ') :
    ρ = ρ' := by
  have h1 := (SpecToEquivOfLocalRing 𝒢.G.left Λ).symm.injective
    (a₁ := ⟨𝒢.genericUnit, ρ, inferInstance⟩) (a₂ := ⟨𝒢.genericUnit, ρ', inferInstance⟩) h
  have h2 := (Sigma.mk.inj_iff.mp h1).2
  exact congrArg Subtype.val (eq_of_heq h2)

theorem ptAt_comp (𝒢 : GroupModel A K) (𝒩 : GroupModel B K) (f : 𝒢.G ⟶ 𝒩.G) [IsMonHom f]
    {Λ : CommRingCat.{0}} (ρ : 𝒢.genStalk ⟶ Λ) :
    ptAt 𝒢 ρ ≫ f.left = ptAt 𝒩 (genMap 𝒢 𝒩 f ≫ ρ) := by
  have e1 : Spec.map (𝒩.G.left.presheaf.stalkSpecializes
      (Inseparable.of_eq (map_genericUnit' 𝒢 𝒩 f)).specializes) ≫
        𝒩.G.left.fromSpecStalk 𝒩.genericUnit = 𝒩.G.left.fromSpecStalk (f.left 𝒢.genericUnit) :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk _
  have e2 : Spec.map (f.left.stalkMap 𝒢.genericUnit) ≫
      𝒩.G.left.fromSpecStalk (f.left 𝒢.genericUnit) =
        𝒢.G.left.fromSpecStalk 𝒢.genericUnit ≫ f.left :=
    Scheme.SpecMap_stalkMap_fromSpecStalk f.left
  unfold ptAt genMap
  rw [Spec.map_comp, Spec.map_comp]
  simp only [Category.assoc]
  rw [e1, e2]

theorem ptAt_specMap (𝒢 : GroupModel A K) {Λ Λ' : CommRingCat.{0}} (ρ : 𝒢.genStalk ⟶ Λ)
    (σ : Λ ⟶ Λ') : Spec.map σ ≫ ptAt 𝒢 ρ = ptAt 𝒢 (ρ ≫ σ) := by
  unfold ptAt
  rw [Spec.map_comp, Category.assoc]

/-- The structure map `𝓞_K → 𝒪_{𝒢,ξ}` as a morphism of rings. -/
noncomputable def sm (𝒢 : GroupModel A K) : CommRingCat.of (𝓞 K) ⟶ 𝒢.genStalk :=
  (Scheme.ΓSpecIso (CommRingCat.of (𝓞 K))).inv ≫ 𝒢.G.hom.appTop ≫
    𝒢.G.left.presheaf.germ ⊤ 𝒢.genericUnit trivial

theorem sm_hom (𝒢 : GroupModel A K) : (sm 𝒢).hom = 𝒢.structMap := rfl

/-- `Spec 𝒪_{𝒢,ξ} → 𝒢 → Spec 𝓞_K` is `Spec` of the structure map. -/
theorem fromSpecStalk_hom (𝒢 : GroupModel A K) :
    𝒢.G.left.fromSpecStalk 𝒢.genericUnit ≫ 𝒢.G.hom = Spec.map (sm 𝒢) := by
  apply ext_of_isAffine
  rw [Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop]
  have h := Scheme.ΓSpecIso_inv_naturality (sm 𝒢)
  have h' : (Spec.map (sm 𝒢)).appTop =
      (Scheme.ΓSpecIso (CommRingCat.of (𝓞 K))).hom ≫ sm 𝒢 ≫ (Scheme.ΓSpecIso 𝒢.genStalk).inv := by
    rw [h, Iso.hom_inv_id_assoc]
  rw [h']
  unfold sm
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  have hm : (Spec 𝒢.genStalk).presheaf.map
      (homOfLE (le_top : 𝒢.G.left.fromSpecStalk 𝒢.genericUnit ⁻¹ᵁ ⊤ ≤ ⊤)).op = 𝟙 _ := by
    rw [show (homOfLE (le_top : 𝒢.G.left.fromSpecStalk 𝒢.genericUnit ⁻¹ᵁ ⊤ ≤ ⊤)).op =
      𝟙 _ from Subsingleton.elim _ _]
    exact CategoryTheory.Functor.map_id _ _
  erw [hm, Category.comp_id]

theorem ptAt_hom (𝒢 : GroupModel A K) {Λ : CommRingCat.{0}} (ρ : 𝒢.genStalk ⟶ Λ) :
    ptAt 𝒢 ρ ≫ 𝒢.G.hom = Spec.map (sm 𝒢 ≫ ρ) := by
  unfold ptAt
  rw [Category.assoc, fromSpecStalk_hom, ← Spec.map_comp]

theorem jK_closedPoint :
    (jK K) (IsLocalRing.closedPoint (CommRingCat.of K)) = genericPt K := by
  have : IsLocalRing.closedPoint (CommRingCat.of K) = (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K) :=
    Subsingleton.elim _ _
  rw [this]
  exact ZInQ.DefFaltings.HodgeLattice.toGeneric_pt (L := K)

theorem unit_closedPoint (𝒢 : GroupModel A K) :
    (jK K ≫ 𝒢.unitSection) (IsLocalRing.closedPoint (CommRingCat.of K)) = 𝒢.genericUnit := by
  change 𝒢.unitSection ((jK K) (IsLocalRing.closedPoint (CommRingCat.of K))) = _
  rw [jK_closedPoint]
  rfl

/-- **The evaluation at the origin** `ε : 𝒪_{𝒢,ξ} → K` (along the unit section). -/
noncomputable def εMap (𝒢 : GroupModel A K) : 𝒢.genStalk ⟶ CommRingCat.of K :=
  𝒢.G.left.presheaf.stalkSpecializes (Inseparable.of_eq (unit_closedPoint 𝒢)).specializes ≫
    Scheme.stalkClosedPointTo (jK K ≫ 𝒢.unitSection)

instance (𝒢 : GroupModel A K) : IsLocalHom (εMap 𝒢).hom := by
  unfold εMap
  haveI : IsIso (𝒢.G.left.presheaf.stalkSpecializes
      (Inseparable.of_eq (unit_closedPoint 𝒢)).specializes) :=
    Iso.isIso_hom (𝒢.G.left.presheaf.stalkCongr (Inseparable.of_eq (unit_closedPoint 𝒢)).symm)
  rw [CommRingCat.hom_comp]
  infer_instance

theorem ptAt_εMap (𝒢 : GroupModel A K) : ptAt 𝒢 (εMap 𝒢) = jK K ≫ 𝒢.unitSection := by
  unfold ptAt εMap
  rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk]

/-- `ε` restricts to `𝓞_K → K` on the structure map. -/
theorem structMap_εMap (𝒢 : GroupModel A K) :
    sm 𝒢 ≫ εMap 𝒢 = CommRingCat.ofHom (algebraMap (𝓞 K) K) := by
  apply Spec.map_injective
  rw [← ptAt_hom, ptAt_εMap, Category.assoc, ZInQ.DefFaltings.HodgeLattice.unitSection_comp,
    Category.comp_id]

/-- `ε` is natural for homomorphisms of group models. -/
theorem genMap_εMap (𝒢 : GroupModel A K) (𝒩 : GroupModel B K) (f : 𝒢.G ⟶ 𝒩.G) [IsMonHom f] :
    genMap 𝒢 𝒩 f ≫ εMap 𝒢 = εMap 𝒩 := by
  haveI : IsLocalHom (genMap 𝒢 𝒩 f ≫ εMap 𝒢).hom := by
    haveI := isIso_stalkSpecializes_genMap 𝒢 𝒩 f
    unfold genMap
    rw [CommRingCat.hom_comp, CommRingCat.hom_comp]
    infer_instance
  apply ptAt_injective 𝒩
  rw [← ptAt_comp, ptAt_εMap, ptAt_εMap, Category.assoc, unitSection_comp]

/-- The trivial point with values in a `K`-scheme. -/
theorem one_left_N (𝒢 : GroupModel A K) (T : Over (Spec (CommRingCat.of K))) :
    (1 : (Over.map (jK K)).obj T ⟶ 𝒢.G).left = T.hom ≫ jK K ≫ 𝒢.unitSection := by
  rw [Hom.one_def, Over.comp_left]
  rfl

end CotPts

end GapHeight
