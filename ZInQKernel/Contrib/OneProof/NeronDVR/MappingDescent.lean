import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.P2M.Sol.S_AlgebraicGeometry_IsSeparated_descendsAlong_surjective_inf_flat_inf_quasiCompact
import ZInQKernel.Contrib.OneProof.NeronBaseChangeStrictHenselization

/-!
# Descent of an extension of a generic-fibre morphism

An extension to an fpqc cover over the source of a smooth test scheme is unique
on the overlaps when the target is separated. The fpqc sheaf property then
descends it to the test scheme. This is the descent of the mapping property
after a model has been descended.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace NeronDVR

/-- If a generic morphism extends after an fpqc cover of its source, it already extends
over the source. Scheme-theoretic dominance and flatness give agreement on the overlap. -/
theorem exists_extension_of_fpqc {S T : Scheme.{0}} (j : T ⟶ S)
    [IsSchemeTheoreticallyDominant j] [QuasiCompact j]
    {Y Y' X : Over S} (p : Y' ⟶ Y)
    [Flat Y.hom] [Flat p.left] [Surjective p.left] [QuasiCompact p.left] [IsSeparated X.hom]
    (f : (Over.pullback j).obj Y ⟶ (Over.pullback j).obj X)
    (g' : Y' ⟶ X) (h : (Over.pullback j).map g' = (Over.pullback j).map p ≫ f) :
    ∃ g : Y ⟶ X, (Over.pullback j).map g = f := by
  let W := Over.mk (pullback.fst p.left p.left ≫ Y'.hom)
  let p₁ : W ⟶ Y' := Over.homMk (pullback.fst p.left p.left) rfl
  let p₂ : W ⟶ Y' := Over.homMk (pullback.snd p.left p.left) (by
    change pullback.snd p.left p.left ≫ Y'.hom = pullback.fst p.left p.left ≫ Y'.hom
    rw [← Over.w p, pullback.condition_assoc])
  have : Flat Y'.hom := by rw [← Over.w p]; infer_instance
  have : Flat W.hom := show Flat (pullback.fst p.left p.left ≫ Y'.hom) from inferInstance
  have hp : p₁ ≫ p = p₂ ≫ p := by
    ext1
    exact pullback.condition
  have hcomp : p₁ ≫ g' = p₂ ≫ g' := by
    apply ZInQ.Contrib.NeronC.pullback_map_injective j W X
    simp only [Functor.map_comp, h, ← Category.assoc]
    rw [← Functor.map_comp, ← Functor.map_comp, hp]
  have hdesc : ∀ {Z : Scheme.{0}} (a b : Z ⟶ Y'.left),
      a ≫ p.left = b ≫ p.left → a ≫ g'.left = b ≫ g'.left := by
    intro Z a b hab
    let q := pullback.lift a b hab
    have hcomp' := congrArg CommaMorphism.left hcomp
    simpa [p₁, p₂, q] using congrArg (q ≫ ·) hcomp'
  let g := EffectiveEpi.desc p.left g'.left hdesc
  have hg : p.left ≫ g = g'.left := EffectiveEpi.fac p.left g'.left hdesc
  have hw : g ≫ X.hom = Y.hom := by
    rw [← cancel_epi p.left, ← Category.assoc, hg, Over.w g', Over.w p]
  let G : Y ⟶ X := Over.homMk g hw
  have hG : p ≫ G = g' := by
    ext1
    exact hg
  have hpb := NeronSH.isPullback_pullback_map_left j p
  have : Flat ((Over.pullback j).map p).left := MorphismProperty.of_isPullback hpb.flip inferInstance
  have : Surjective ((Over.pullback j).map p).left :=
    MorphismProperty.of_isPullback hpb.flip inferInstance
  have : QuasiCompact ((Over.pullback j).map p).left :=
    MorphismProperty.of_isPullback hpb.flip inferInstance
  refine ⟨G, ?_⟩
  have heq : (Over.pullback j).map p ≫ (Over.pullback j).map G =
      (Over.pullback j).map p ≫ f := by
    rw [← Functor.map_comp, hG, h]
  ext1
  exact (cancel_epi ((Over.pullback j).map p).left).mp (congrArg CommaMorphism.left heq)

/-- The Néron mapping property of a smooth separated model can be checked after an
fpqc base change. The square on the generic loci is Cartesian. -/
theorem mapping_property_of_fpqc {S S' T T' : Scheme.{0}} (j : T ⟶ S) (s : S' ⟶ S)
    (j' : T' ⟶ S') (t : T' ⟶ T) (hpb : IsPullback j' t s j)
    [IsSchemeTheoreticallyDominant j] [QuasiCompact j]
    [Flat s] [Surjective s] [QuasiCompact s]
    (X : Over S) [IsSeparated X.hom]
    (hX : ∀ (Z : Over S') [Smooth Z.hom],
      Function.Surjective fun e : Z ⟶ (Over.pullback s).obj X => (Over.pullback j').map e)
    (Y : Over S) [Smooth Y.hom] :
    Function.Bijective fun f : Y ⟶ X => (Over.pullback j).map f := by
  refine ⟨ZInQ.Contrib.NeronC.pullback_map_injective j Y X, ?_⟩
  intro f
  let Y' := (Over.pullback s).obj Y
  let X' := (Over.pullback s).obj X
  let Y₀ : Over S := Over.mk (pullback.fst Y.hom s ≫ Y.hom)
  let p : Y₀ ⟶ Y := Over.homMk (pullback.fst Y.hom s) rfl
  have : Flat p.left := show Flat (pullback.fst Y.hom s) from inferInstance
  have : Surjective p.left := show Surjective (pullback.fst Y.hom s) from inferInstance
  have : QuasiCompact p.left := show QuasiCompact (pullback.fst Y.hom s) from inferInstance
  have : Smooth Y'.hom := show Smooth (pullback.snd Y.hom s) from inferInstance
  let a : pullback Y'.hom j' ⟶ pullback Y.hom j :=
    pullback.lift (pullback.fst Y'.hom j' ≫ pullback.fst Y.hom s)
      (pullback.snd Y'.hom j' ≫ t) (by
        simp only [Category.assoc, pullback.condition]
        change (pullback.fst Y'.hom j' ≫ Y'.hom) ≫ s = pullback.snd Y'.hom j' ≫ t ≫ j
        rw [pullback.condition, Category.assoc, hpb.w])
  have hf : f.left ≫ pullback.snd X.hom j = pullback.snd Y.hom j := Over.w f
  let b : pullback Y'.hom j' ⟶ X'.left :=
    pullback.lift (a ≫ f.left ≫ pullback.fst X.hom j) (pullback.snd Y'.hom j' ≫ j') (by
      simp only [Category.assoc, pullback.condition]
      rw [← Category.assoc f.left, hf]
      simp [a, hpb.w])
  let f' : (Over.pullback j').obj Y' ⟶ (Over.pullback j').obj X' :=
    let h : b ≫ X'.hom = pullback.snd Y'.hom j' ≫ j' := pullback.lift_snd _ _ _
    Over.homMk (pullback.lift b (pullback.snd Y'.hom j') h) (pullback.lift_snd _ _ _)
  obtain ⟨g, hg⟩ := hX Y' f'
  have hg₁ : pullback.fst Y'.hom j' ≫ g.left = b := by
    have hgMap : ((Over.pullback j').map g).left ≫ pullback.fst X'.hom j' =
        pullback.fst Y'.hom j' ≫ g.left := pullback.lift_fst _ _ _
    have hfMap : f'.left ≫ pullback.fst X'.hom j' = b := pullback.lift_fst _ _ _
    exact hgMap.symm.trans ((congrArg (fun k => CommaMorphism.left k ≫ pullback.fst X'.hom j')
      hg).trans hfMap)
  have hg₂ : g.left ≫ pullback.snd X.hom s = pullback.snd Y.hom s := Over.w g
  let G : Y₀ ⟶ X := Over.homMk (g.left ≫ pullback.fst X.hom s) (by
    simp only [Category.assoc, pullback.condition]
    rw [← Category.assoc, hg₂]
    exact pullback.condition.symm)
  apply exists_extension_of_fpqc j p f G
  let q : pullback Y₀.hom j ⟶ T' :=
    hpb.lift (pullback.fst Y₀.hom j ≫ pullback.snd Y.hom s) (pullback.snd Y₀.hom j) (by
      simp only [Category.assoc, ← pullback.condition (f := Y.hom) (g := s)]
      exact pullback.condition)
  have hq₁ : q ≫ j' = pullback.fst Y₀.hom j ≫ Y'.hom := hpb.lift_fst _ _ _
  have hq₂ : q ≫ t = pullback.snd Y₀.hom j := hpb.lift_snd _ _ _
  let r : pullback Y₀.hom j ⟶ pullback Y'.hom j' :=
    pullback.lift (pullback.fst Y₀.hom j) q hq₁.symm
  have hr : r ≫ a = ((Over.pullback j).map p).left := by
    apply pullback.hom_ext <;> simp [r, a, p, hq₂, Over.pullback_map_left]
  ext1
  apply pullback.hom_ext
  · simp only [Over.comp_left, Over.pullback_map_left, pullback.lift_fst, Category.assoc]
    change pullback.fst Y₀.hom j ≫ g.left ≫ pullback.fst X.hom s =
      ((Over.pullback j).map p).left ≫ f.left ≫ pullback.fst X.hom j
    have hr₁ : r ≫ pullback.fst Y'.hom j' = pullback.fst Y₀.hom j := pullback.lift_fst _ _ _
    have hb₁ : b ≫ pullback.fst X.hom s = a ≫ f.left ≫ pullback.fst X.hom j :=
      pullback.lift_fst _ _ _
    calc
      _ = r ≫ b ≫ pullback.fst X.hom s := by
        rw [← hr₁, Category.assoc, ← Category.assoc (pullback.fst Y'.hom j'), hg₁]
      _ = _ := by rw [hb₁, ← Category.assoc r a, hr]
  · simp only [Over.comp_left, Over.pullback_map_left, pullback.lift_snd, Category.assoc, hf]

/-- Over an affine base, the entire Néron model predicate reflects along an fpqc base
change with Cartesian generic-fibre square. -/
theorem isNeronModelOver_of_fpqc
    {R R' K K' : Type} [CommRing R] [IsDomain R] [CommRing R']
    [Field K] [Field K'] [Algebra R K] [IsFractionRing R K] [Algebra R' K']
    (s : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
    (t : Spec (CommRingCat.of K') ⟶ Spec (CommRingCat.of K))
    (h : IsPullback (Spec.map (CommRingCat.ofHom (algebraMap R' K'))) t s
      (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    [Flat s] [Surjective s] [QuasiCompact s]
    (X : Over (Spec (CommRingCat.of R)))
    (hX : CToPrinted.IsNeronModelOver R' K' ((Over.pullback s).obj X)) :
    CToPrinted.IsNeronModelOver R K X := by
  let j := Spec.map (CommRingCat.ofHom (algebraMap R K))
  have : IsSchemeTheoreticallyDominant j :=
    ZInQ.Contrib.NeronC.isSchemeTheoreticallyDominant_spec_map _ (IsFractionRing.injective R K)
  obtain ⟨hsm, hsep, _, hqc, hext⟩ := hX
  let Q : MorphismProperty Scheme.{0} := @Surjective ⊓ @Flat ⊓ @QuasiCompact
  have hs : Q s := ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  have : Smooth X.hom := MorphismProperty.of_pullback_snd_of_descendsAlong
    (P := @Smooth) hs hsm
  have : MorphismProperty.DescendsAlong (@IsSeparated : MorphismProperty Scheme.{0}) Q :=
    ZInQ.Contrib.CloudR2NeronExistence.Henselian.P2MW.S_AlgebraicGeometry_IsSeparated_descendsAlong_surjective_inf_flat_inf_quasiCompact.solution
  have : IsSeparated X.hom := MorphismProperty.of_pullback_snd_of_descendsAlong
    (P := @IsSeparated) hs hsep
  have : QuasiCompact (pullback.snd X.hom s) := hqc
  have : CompactSpace ↥(pullback X.hom s) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd X.hom s)
  have : CompactSpace X.left := by
    constructor
    have hc := isCompact_univ.image (pullback.fst X.hom s).continuous
    simpa only [Set.image_univ, Set.range_eq_univ.mpr (pullback.fst X.hom s).surjective] using hc
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, fun Y _ => ?_⟩
  exact mapping_property_of_fpqc j s _ t h X (fun Z _ => (hext Z).surjective) Y

end NeronDVR
