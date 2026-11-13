import ZInQKernel.HDecomp.Faltings.Leaves

/-! # h5-glue: `NeronModelMinimal` from one height-transport glue statement

* `isMonHom_of_map`: a morphism `f` whose image under a (strong) monoidal functor is a monoid
  morphism is a monoid morphism, provided the functor is injective on morphisms `𝟙 → Y` and
  `X ⊗ X → Y`.
* `GroupModel.IsNeronModel.lift_isMonHom`: the Néron comparison map `𝒢 → 𝒩` is a homomorphism
  of group schemes, and its generic fibre is an isomorphism.
* `neronModelMinimal_of_heightAntitone`: `NeronModelMinimal` follows from the glue
  `HeightAntitone` (a homomorphism of group models that is an isomorphism on generic fibres does
  not increase the height). -/

namespace ZInQ.H5Glue

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings
open PkgI3 (AbVar)
open scoped Obj

section Abstract

variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
  (F : C ⥤ D) [F.Monoidal]

/-- A strong monoidal functor that is injective on `Hom(𝟙, Y)` and `Hom(X ⊗ X, Y)` reflects
monoid morphisms `X → Y`. -/
theorem isMonHom_of_map {X Y : C} [MonObj X] [MonObj Y] (f : X ⟶ Y) [IsMonHom (F.map f)]
    (h1 : ∀ g g' : 𝟙_ C ⟶ Y, F.map g = F.map g' → g = g')
    (h2 : ∀ g g' : X ⊗ X ⟶ Y, F.map g = F.map g' → g = g') : IsMonHom f where
  one_hom := by
    apply h1
    rw [← cancel_epi (Functor.LaxMonoidal.ε F), F.map_comp, ← Category.assoc]
    exact IsMonHom.one_hom (f := F.map f)
  mul_hom := by
    apply h2
    rw [← cancel_epi (Functor.LaxMonoidal.μ F X X), F.map_comp, ← Category.assoc]
    have hm := IsMonHom.mul_hom (f := F.map f)
    refine hm.trans ?_
    rw [F.map_comp, Functor.obj.μ_def, ← Functor.LaxMonoidal.μ_natural_assoc]

end Abstract

section Neron

variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]

/-- `Spec L → Spec 𝓞_L`. -/
noncomputable abbrev jL (L : Type) [Field L] [NumberField L] :
    Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of (𝓞 L)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) L))

instance smooth_tensor (𝒢 : GroupModel A L) : Smooth (𝒢.G ⊗ 𝒢.G).hom := by
  show Smooth (pullback.fst 𝒢.G.hom 𝒢.G.hom ≫ 𝒢.G.hom); infer_instance

instance smooth_unit : Smooth (𝟙_ (Over (Spec (CommRingCat.of (𝓞 L))))).hom := by
  dsimp; infer_instance

/-- The comparison map `𝒢 → 𝒩` to a Néron model (unique with `F(f) ≫ gen_𝒩 = gen_𝒢`). -/
theorem neron_lift {𝒩 : GroupModel A L} (h𝒩 : 𝒩.IsNeronModel)
    (𝒢 : GroupModel A L) :
    ∃ f : 𝒢.G ⟶ 𝒩.G, (Over.pullback (jL L)).map f ≫ 𝒩.gen.hom = 𝒢.gen.hom :=
  (h𝒩 𝒢.G).2 𝒢.gen.hom

/-- Injectivity of `F = Over.pullback (jL L)` on maps from a smooth scheme into a Néron model. -/
theorem neron_map_injective {𝒩 : GroupModel A L} (h𝒩 : 𝒩.IsNeronModel)
    {Y : Over (Spec (CommRingCat.of (𝓞 L)))} [Smooth Y.hom] (g g' : Y ⟶ 𝒩.G)
    (h : (Over.pullback (jL L)).map g = (Over.pullback (jL L)).map g') : g = g' :=
  (h𝒩 Y).1 (by simp only [h])

/-- **The Néron comparison map is a homomorphism of group schemes**, and an isomorphism on
generic fibres. -/
theorem neron_lift_isMonHom {𝒩 : GroupModel A L} (h𝒩 : 𝒩.IsNeronModel)
    (𝒢 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G)
    (hf : (Over.pullback (jL L)).map f ≫ 𝒩.gen.hom = 𝒢.gen.hom) :
    IsMonHom f ∧ IsIso ((Over.pullback (jL L)).map f) := by
  let F := Over.pullback (jL L)
  let e₁ : F.obj 𝒢.G ≅ (A.baseChange L).X := 𝒢.gen
  let e₂ : F.obj 𝒩.G ≅ (A.baseChange L).X := 𝒩.gen
  have g1 : IsMonHom e₁.hom := 𝒢.gen_hom
  have g2 : IsMonHom e₂.hom := 𝒩.gen_hom
  have hiso : F.map f = e₁.hom ≫ e₂.inv := by
    rw [Iso.eq_comp_inv]; exact hf
  refine ⟨?_, by rw [hiso]; infer_instance⟩
  have : IsMonHom (F.map f) := by rw [hiso]; infer_instance
  exact isMonHom_of_map F f (fun g g' => neron_map_injective h𝒩 g g')
    (fun g g' => neron_map_injective h𝒩 g g')

/-- **Glue (stated): heights decrease along generic isomorphisms.** If `f : 𝒢 → 𝒩` is a
homomorphism of group models of `A_L` that is an isomorphism on generic fibres, then
`h(𝒩) ≤ h(𝒢)`: `f*` identifies `ω_{A_L}` for both models and maps `ω_𝒩` into `ω_𝒢` (so
`⋀^g ω_𝒩 ⊆ ⋀^g ω_𝒢` and `HodgeData.modelHeight_le_of_le` applies), and `Φ ↦ f ∘ Φ` transports
analytic uniformizations with the same Jacobian determinants. -/
def HeightAntitone : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G), IsMonHom f →
    IsIso ((Over.pullback (jL L)).map f) → 𝒩.height ≤ 𝒢.height

/-- **`NeronModelMinimal` from `HeightAntitone`.** -/
theorem neronModelMinimal_of_heightAntitone (h : HeightAntitone) : NeronModelMinimal := by
  intro K _ A L _ _ _ 𝒩 𝒢 h𝒩
  obtain ⟨f, hf⟩ := neron_lift h𝒩 𝒢
  obtain ⟨hm, hi⟩ := neron_lift_isMonHom h𝒩 𝒢 f hf
  exact h K A L 𝒢 𝒩 f hm hi

end Neron

end ZInQ.H5Glue

#print axioms ZInQ.H5Glue.isMonHom_of_map
#print axioms ZInQ.H5Glue.neron_lift_isMonHom
#print axioms ZInQ.H5Glue.neronModelMinimal_of_heightAntitone
