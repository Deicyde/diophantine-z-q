import ZInQKernel.Contrib.OneProof.NeronGoodModelIso

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

namespace DedekindFree

section Descent

variable {S S' : Scheme.{0}} (p : S' ⟶ S) [Flat p] [Surjective p] [QuasiCompact p]

instance effEpi_fst (X : Over S) : EffectiveEpi (pullback.fst X.hom p) := inferInstance

/-- Base change along a faithfully flat quasi-compact `p` is injective on morphisms. -/
theorem map_injective (X Y : Over S) :
    Function.Injective (fun f : X ⟶ Y => (Over.pullback p).map f) := by
  intro f g h
  simp only at h
  have e1 : ((Over.pullback p).map f).left ≫ pullback.fst Y.hom p = pullback.fst X.hom p ≫ f.left := by simp
  have e2 : ((Over.pullback p).map g).left ≫ pullback.fst Y.hom p = pullback.fst X.hom p ≫ g.left := by simp
  ext1
  rw [← cancel_epi (pullback.fst X.hom p), ← e1, ← e2, h]

/-- **Descent of morphisms along a faithfully flat quasi-compact `p`** (Stacks 023Q, Mathlib's `EffectiveEpi`). -/
theorem descend (X Y : Over S) (b : (Over.pullback p).obj X ⟶ (Over.pullback p).obj Y)
    (hb : ∀ (W : Scheme.{0}) (a₁ a₂ : W ⟶ ((Over.pullback p).obj X).left),
      a₁ ≫ pullback.fst X.hom p = a₂ ≫ pullback.fst X.hom p →
        a₁ ≫ b.left ≫ pullback.fst Y.hom p = a₂ ≫ b.left ≫ pullback.fst Y.hom p) :
    ∃ f : X ⟶ Y, (Over.pullback p).map f = b := by
  let fl : X.left ⟶ Y.left :=
    EffectiveEpi.desc (pullback.fst X.hom p) (b.left ≫ pullback.fst Y.hom p) (fun a₁ a₂ h => hb _ a₁ a₂ h)
  have hfl : pullback.fst X.hom p ≫ fl = b.left ≫ pullback.fst Y.hom p := EffectiveEpi.fac _ _ _
  have hw : fl ≫ Y.hom = X.hom := by
    have := Over.w b
    simp only [Over.pullback_obj_hom] at this
    rw [← cancel_epi (pullback.fst X.hom p), reassoc_of% hfl, pullback.condition,
      ← Category.assoc, this, pullback.condition]
  refine ⟨Over.homMk fl hw, ?_⟩
  ext1
  apply pullback.hom_ext
  · simp [hfl]
  · have := Over.w b
    simp only [Over.pullback_obj_hom] at this
    simp [this]

end Descent


section GrpDescent

open Functor.OplaxMonoidal

variable {S S' : Scheme.{0}} (p : S' ⟶ S) [Flat p] [Surjective p] [QuasiCompact p]
  (F : Over S) [GrpObj ((Over.pullback p).obj F)]
  (μd : F ⊗ F ⟶ F) (hμ : (Over.pullback p).map μd = δ (Over.pullback p) F F ≫ μ[(Over.pullback p).obj F])
  (ιd : F ⟶ F) (hι : (Over.pullback p).map ιd = ι[(Over.pullback p).obj F])
  (ηd : 𝟙_ (Over S) ⟶ F) (hη : (Over.pullback p).map ηd = Functor.OplaxMonoidal.η (Over.pullback p) ≫ η[(Over.pullback p).obj F])

include hμ in
theorem map_mul' {T : Over S} (f g : T ⟶ F) :
    (Over.pullback p).map (lift f g ≫ μd) = (Over.pullback p).map f * (Over.pullback p).map g := by
  rw [Functor.map_comp, hμ, Hom.mul_def, lift_δ_assoc]

include hη in
theorem map_one' {T : Over S} :
    (Over.pullback p).map (toUnit T ≫ ηd) = 1 := by
  rw [Functor.map_comp, hη, Hom.one_def, ← Category.assoc]
  congr 1
  exact toUnit_unique _ _

include hι in
theorem map_inv' {T : Over S} (f : T ⟶ F) :
    (Over.pullback p).map (f ≫ ιd) = ((Over.pullback p).map f)⁻¹ := by
  rw [Functor.map_comp, hι, Hom.inv_def]

set_option warn.classDefReducibility false in
/-- The group structure on `T ⟶ F` transported along the injective `(Over.pullback p).map`. -/
def homGroup (T : Over S) : Group (T ⟶ F) :=
  letI : Mul (T ⟶ F) := ⟨fun f g => lift f g ≫ μd⟩
  letI : One (T ⟶ F) := ⟨toUnit T ≫ ηd⟩
  letI : Inv (T ⟶ F) := ⟨fun f => f ≫ ιd⟩
  have hm : ∀ f g : T ⟶ F, (Over.pullback p).map (f * g) = (Over.pullback p).map f * (Over.pullback p).map g :=
    fun f g => map_mul' p F μd hμ f g
  have h1 : (Over.pullback p).map (1 : T ⟶ F) = 1 := map_one' p F ηd hη
  have hi : ∀ f : T ⟶ F, (Over.pullback p).map f⁻¹ = ((Over.pullback p).map f)⁻¹ :=
    fun f => map_inv' p F ιd hι f
  Group.ofLeftAxioms
    (fun a b c => map_injective p T F (by simp only [hm, _root_.mul_assoc]))
    (fun a => map_injective p T F (by simp only [hm, h1, _root_.one_mul]))
    (fun a => map_injective p T F (by simp only [hm, hi, h1, _root_.inv_mul_cancel]))

/-- The presheaf of groups `T ↦ (T ⟶ F)`. -/
def homFunctor : (Over S)ᵒᵖ ⥤ GrpCat.{0} where
  obj T := @GrpCat.of (T.unop ⟶ F) (homGroup p F μd hμ ιd hι ηd hη T.unop)
  map {T T'} φ := by
    letI := homGroup p F μd hμ ιd hι ηd hη T.unop
    letI := homGroup p F μd hμ ιd hι ηd hη T'.unop
    exact GrpCat.ofHom
      { toFun := fun f => φ.unop ≫ f
        map_one' := by
          change φ.unop ≫ (toUnit _ ≫ ηd) = toUnit _ ≫ ηd
          rw [← Category.assoc, toUnit_unique (φ.unop ≫ toUnit _) (toUnit _)]
        map_mul' := fun f g => by
          change φ.unop ≫ (lift f g ≫ μd) = lift (φ.unop ≫ f) (φ.unop ≫ g) ≫ μd
          rw [← Category.assoc, comp_lift] }
  map_id T := GrpCat.ext fun f => Category.id_comp f
  map_comp φ ψ := GrpCat.ext fun f =>
    show (ψ.unop ≫ φ.unop) ≫ f = ψ.unop ≫ (φ.unop ≫ f) from Category.assoc _ _ _

/-- **The descended group law.** -/
@[instance_reducible]
def grpObjOfDescent : GrpObj F :=
  GrpObj.ofRepresentableBy F (homFunctor p F μd hμ ιd hι ηd hη)
    { homEquiv := Equiv.refl _
      homEquiv_comp := fun f g => by rfl }

theorem grpObjOfDescent_one :
    (grpObjOfDescent p F μd hμ ιd hι ηd hη).one = ηd := by
  change toUnit _ ≫ ηd = ηd
  rw [toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]

end GrpDescent

end DedekindFree
