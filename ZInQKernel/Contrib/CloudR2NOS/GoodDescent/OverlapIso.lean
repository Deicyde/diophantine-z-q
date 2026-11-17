/-
Copyright (c) 2026 H5/NOS Round-2 Lane5 contributors.
Released under Apache 2.0 license as described in the project LICENSE.
New actual overlap ISOMORPHISM, constructed from the proved global transport
and its cocycle. No overlap iso, hdesc or effective quotient is supplied.
This is the underlying scheme iso; effectivity and descended group/proper
scheme are not claimed by this file.
-/
import ZInQKernel.Contrib.CloudR2NOS.GoodDescent.SchemeDatum

set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2NOS.GoodDescent.GenericModel
variable {X U S : Scheme.{u}} {f : X ⟶ U} {p : U ⟶ S} {V : S.Opens}
  (M : GenericModel f p V) [Etale p] (s : S) [Mono (p.fiberToSpecResidueField s)]
  (hV : ∀ z : S, z ∉ V → z = s)

private theorem transportMap_congr {T : Scheme.{u}} {x x' : T ⟶ X} {v v' : T ⟶ U}
    (hx : x = x') (hv : v = v')
    (h : (x ≫ f) ≫ p = v ≫ p) (h' : (x' ≫ f) ≫ p = v' ≫ p) :
    M.transportMap s hV x v h = M.transportMap s hV x' v' h' := by
  cases hx
  cases hv
  rfl

private theorem comparison_condition {R : Scheme.{u}} (u₁ u₂ : R ⟶ U)
    (h : u₁ ≫ p = u₂ ≫ p) :
    (pullback.fst f u₁ ≫ f) ≫ p = (pullback.snd f u₁ ≫ u₂) ≫ p := by
  rw [pullback.condition, Category.assoc, Category.assoc, h]

/-- Construct the actual universal overlap map by transporting the
    universal point and then using the pullback universal property. -/
def comparisonMap {R : Scheme.{u}} (u₁ u₂ : R ⟶ U)
    (h : u₁ ≫ p = u₂ ≫ p) : pullback f u₁ ⟶ pullback f u₂ :=
  pullback.lift (M.transportMap s hV (pullback.fst f u₁) (pullback.snd f u₁ ≫ u₂)
    (comparison_condition u₁ u₂ h)) (pullback.snd f u₁)
    (M.transportMap_base s hV _ _ _)

@[reassoc (attr := simp)]
theorem comparisonMap_fst {R : Scheme.{u}} (u₁ u₂ : R ⟶ U)
    (h : u₁ ≫ p = u₂ ≫ p) :
    M.comparisonMap s hV u₁ u₂ h ≫ pullback.fst f u₂ =
      M.transportMap s hV (pullback.fst f u₁) (pullback.snd f u₁ ≫ u₂)
        (comparison_condition u₁ u₂ h) := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem comparisonMap_snd {R : Scheme.{u}} (u₁ u₂ : R ⟶ U)
    (h : u₁ ≫ p = u₂ ≫ p) :
    M.comparisonMap s hV u₁ u₂ h ≫ pullback.snd f u₂ = pullback.snd f u₁ :=
  pullback.lift_snd _ _ _

/-- The actual universal comparison morphisms satisfy the triple-overlap
    cocycle, before making any effectiveness assumption. -/
theorem comparisonMap_comp {R : Scheme.{u}} (u₁ u₂ u₃ : R ⟶ U)
    (h₁₂ : u₁ ≫ p = u₂ ≫ p) (h₂₃ : u₂ ≫ p = u₃ ≫ p) :
    M.comparisonMap s hV u₁ u₂ h₁₂ ≫ M.comparisonMap s hV u₂ u₃ h₂₃ =
      M.comparisonMap s hV u₁ u₃ (h₁₂.trans h₂₃) := by
  let a₁ := pullback.fst f u₁
  let b₁ := pullback.snd f u₁
  let a₂ := pullback.fst f u₂
  let b₂ := pullback.snd f u₂
  let c := M.comparisonMap s hV u₁ u₂ h₁₂
  let h₂ := comparison_condition (f := f) u₁ u₂ h₁₂
  let h₃ := comparison_condition (f := f) u₁ u₃ (h₁₂.trans h₂₃)
  let t := M.transportMap s hV a₁ (b₁ ≫ u₂) h₂
  have hc₁ : c ≫ a₂ = t := M.comparisonMap_fst s hV u₁ u₂ h₁₂
  have hc₂ : c ≫ (b₂ ≫ u₃) = b₁ ≫ u₃ := M.comparisonMap_snd_assoc s hV u₁ u₂ h₁₂ u₃
  have h₂₃t : (t ≫ f) ≫ p = (b₁ ≫ u₃) ≫ p := by
    rw [M.transportMap_base, Category.assoc, Category.assoc, h₂₃]
  have h' : ((c ≫ a₂) ≫ f) ≫ p = (c ≫ (b₂ ≫ u₃)) ≫ p := by
    rw [hc₁, hc₂]
    exact h₂₃t
  apply pullback.hom_ext
  · change (c ≫ M.comparisonMap s hV u₂ u₃ h₂₃) ≫ pullback.fst f u₃ =
        M.comparisonMap s hV u₁ u₃ (h₁₂.trans h₂₃) ≫ pullback.fst f u₃
    rw [Category.assoc, M.comparisonMap_fst, M.comparisonMap_fst]
    have hn := M.transportMap_natural s hV a₂ (b₂ ≫ u₃)
      (comparison_condition u₂ u₃ h₂₃) c h'
    calc
      c ≫ M.transportMap s hV a₂ (b₂ ≫ u₃) (comparison_condition u₂ u₃ h₂₃) =
          M.transportMap s hV (c ≫ a₂) (c ≫ (b₂ ≫ u₃)) h' := hn.symm
      _ = M.transportMap s hV t (b₁ ≫ u₃) h₂₃t :=
        M.transportMap_congr s hV hc₁ hc₂ h' h₂₃t
      _ = M.transportMap s hV a₁ (b₁ ≫ u₃) h₃ :=
        M.transportMap_cocycle s hV a₁ (b₁ ≫ u₂) (b₁ ≫ u₃) h₂ h₃ h₂₃t
  · simp only [Category.assoc, M.comparisonMap_snd, M.comparisonMap_snd_assoc]

/-- The comparison made in the reverse direction is actually the inverse. -/
theorem comparisonMap_comp_inverse {R : Scheme.{u}} (u₁ u₂ : R ⟶ U)
    (h : u₁ ≫ p = u₂ ≫ p) :
    M.comparisonMap s hV u₁ u₂ h ≫ M.comparisonMap s hV u₂ u₁ h.symm = 𝟙 _ := by
  let a₁ := pullback.fst f u₁
  let b₁ := pullback.snd f u₁
  let a₂ := pullback.fst f u₂
  let b₂ := pullback.snd f u₂
  let c := M.comparisonMap s hV u₁ u₂ h
  let h₂ := comparison_condition (f := f) u₁ u₂ h
  let t := M.transportMap s hV a₁ (b₁ ≫ u₂) h₂
  have hc₁ : c ≫ a₂ = t := M.comparisonMap_fst s hV u₁ u₂ h
  have hc₂ : c ≫ (b₂ ≫ u₁) = b₁ ≫ u₁ := M.comparisonMap_snd_assoc s hV u₁ u₂ h u₁
  have h₃ : (a₁ ≫ f) ≫ p = (b₁ ≫ u₁) ≫ p := by rw [pullback.condition]
  have h₂₃ : (t ≫ f) ≫ p = (b₁ ≫ u₁) ≫ p := by
    rw [M.transportMap_base, Category.assoc, Category.assoc, ← h]
  have h' : ((c ≫ a₂) ≫ f) ≫ p = (c ≫ (b₂ ≫ u₁)) ≫ p := by
    rw [hc₁, hc₂]
    exact h₂₃
  apply pullback.hom_ext
  · change (c ≫ M.comparisonMap s hV u₂ u₁ h.symm) ≫ a₁ = (𝟙 _) ≫ a₁
    rw [Category.assoc, M.comparisonMap_fst, Category.id_comp]
    have hn := M.transportMap_natural s hV a₂ (b₂ ≫ u₁)
      (comparison_condition u₂ u₁ h.symm) c h'
    calc
      c ≫ M.transportMap s hV a₂ (b₂ ≫ u₁) (comparison_condition u₂ u₁ h.symm) =
          M.transportMap s hV (c ≫ a₂) (c ≫ (b₂ ≫ u₁)) h' := hn.symm
      _ = M.transportMap s hV t (b₁ ≫ u₁) h₂₃ :=
        M.transportMap_congr s hV hc₁ hc₂ h' h₂₃
      _ = M.transportMap s hV a₁ (b₁ ≫ u₁) h₃ :=
        M.transportMap_cocycle s hV a₁ (b₁ ≫ u₂) (b₁ ≫ u₁) h₂ h₃ h₂₃
      _ = a₁ := M.transportMap_identity s hV a₁ (b₁ ≫ u₁) h₃ (pullback.condition)
  · simp only [Category.assoc, M.comparisonMap_snd, M.comparisonMap_snd_assoc,
      Category.id_comp]

/-- Actual overlap isomorphism over the overlap base; all its maps are
    constructed from the original generic identification. -/
def overlapIso {R : Scheme.{u}} (u₁ u₂ : R ⟶ U) (h : u₁ ≫ p = u₂ ≫ p) :
    (Over.pullback u₁).obj (Over.mk f) ≅ (Over.pullback u₂).obj (Over.mk f) where
  hom := Over.homMk (M.comparisonMap s hV u₁ u₂ h) (M.comparisonMap_snd s hV u₁ u₂ h)
  inv := Over.homMk (M.comparisonMap s hV u₂ u₁ h.symm) (M.comparisonMap_snd s hV u₂ u₁ h.symm)
  hom_inv_id := by
    apply Over.OverMorphism.ext
    exact M.comparisonMap_comp_inverse s hV u₁ u₂ h
  inv_hom_id := by
    apply Over.OverMorphism.ext
    exact M.comparisonMap_comp_inverse s hV u₂ u₁ h.symm

/-- Specialize to the actual self-overlap `U ×_S U`. -/
def selfOverlapIso :
    (Over.pullback (pullback.fst p p)).obj (Over.mk f) ≅
      (Over.pullback (pullback.snd p p)).obj (Over.mk f) :=
  M.overlapIso s hV (pullback.fst p p) (pullback.snd p p) (pullback.condition)

#print axioms comparisonMap_comp_inverse
#print axioms overlapIso
#print axioms selfOverlapIso

end ZInQ.Contrib.CloudR2NOS.GoodDescent.GenericModel
