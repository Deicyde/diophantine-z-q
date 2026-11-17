/-
Copyright (c) 2026 H5/NOS Round-2 Lane5 contributors.
Released under Apache 2.0 license as described in the project LICENSE.

Actual triple scheme nerve for the level-free effective Proj descent.
All maps and cocycle equalities are constructed from the proved overlap
transport. No hdesc, cocycle, effective quotient or properness is an input.
-/
import ZInQKernel.Contrib.CloudR2NOS.GoodDescent.Effective.TensorSquare

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

namespace ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective.TensorNerve
open TensorCofaces

variable {R : Type u} [CommRing R] (R' : Type u) [CommRing R'] [Algebra R R']
  (V : (Base R).Opens) (G : Grp (Over (Cover R'))) (A : Grp (Over V.toScheme))
  (e : (Over.pullback ((baseMap R R') ⁻¹ᵁ V).ι).mapGrp.obj G ≅
    (Over.pullback ((baseMap R R') ∣_ V)).mapGrp.obj A)
  [Etale (baseMap R R')] (c : Base R)
  [Mono ((baseMap R R').fiberToSpecResidueField c)]
  (hV : ∀ z : Base R, z ∉ V → z = c)

abbrev model3 : Scheme.{u} := pullback G.X.hom (face12 R R' ≫ left R R')
abbrev structure3 : model3 (R := R) R' G ⟶ Triple R R' := pullback.snd G.X.hom (face12 R R' ≫ left R R')
abbrev projection3 : model3 (R := R) R' G ⟶ G.X.left := pullback.fst G.X.hom (face12 R R' ≫ left R R')

def chart12 : model3 (R := R) R' G ⟶ model2 (R := R) R' G :=
  pullback.lift (projection3 (R := R) R' G) (structure3 (R := R) R' G ≫ face12 R R')
    (by simpa only [Category.assoc] using pullback.condition (f := G.X.hom) (g := face12 R R' ≫ left R R'))

def chart13 : model3 (R := R) R' G ⟶ model2 (R := R) R' G :=
  pullback.lift (projection3 (R := R) R' G) (structure3 (R := R) R' G ≫ face13 R R')
    (by rw [Category.assoc, ← face12_left R R']; exact pullback.condition)

private theorem toSecond_condition :
    (projection3 (R := R) R' G ≫ G.X.hom) ≫ baseMap R R' =
      (structure3 (R := R) R' G ≫ face23 R R' ≫ left R R') ≫ baseMap R R' := by
  rw [pullback.condition, Category.assoc, Category.assoc, left_base R R',
    ← Category.assoc (face12 R R'), face12_right R R', Category.assoc]
  simp only [structure3, Category.assoc]

/-- The 23 projection uses the actual group-compatible overlap transport;
    unlike the 12/13 projections it changes the model point to chart 2. -/
def chart23 : model3 (R := R) R' G ⟶ model2 (R := R) R' G :=
  pullback.lift
    ((genericModelOfGroupIso (baseMap R R') V G A e).transportMap c hV (projection3 (R := R) R' G)
      (structure3 (R := R) R' G ≫ face23 R R' ≫ left R R') (toSecond_condition (R := R) R' G))
    (structure3 (R := R) R' G ≫ face23 R R')
    ((genericModelOfGroupIso (baseMap R R') V G A e).transportMap_base c hV _ _ _)

@[reassoc (attr := simp)]
theorem chart12_first : chart12 (R := R) R' G ≫ projection1 (R := R) R' G = projection3 (R := R) R' G := pullback.lift_fst _ _ _
@[reassoc (attr := simp)]
theorem chart12_base : chart12 (R := R) R' G ≫ structure2 (R := R) R' G = structure3 (R := R) R' G ≫ face12 R R' := pullback.lift_snd _ _ _
@[reassoc (attr := simp)]
theorem chart13_first : chart13 (R := R) R' G ≫ projection1 (R := R) R' G = projection3 (R := R) R' G := pullback.lift_fst _ _ _
@[reassoc (attr := simp)]
theorem chart13_base : chart13 (R := R) R' G ≫ structure2 (R := R) R' G = structure3 (R := R) R' G ≫ face13 R R' := pullback.lift_snd _ _ _
@[reassoc (attr := simp)]
theorem chart23_first : chart23 R' V G A e c hV ≫ projection1 (R := R) R' G =
    (genericModelOfGroupIso (baseMap R R') V G A e).transportMap c hV (projection3 (R := R) R' G)
      (structure3 (R := R) R' G ≫ face23 R R' ≫ left R R') (toSecond_condition (R := R) R' G) := pullback.lift_fst _ _ _
@[reassoc (attr := simp)]
theorem chart23_base : chart23 R' V G A e c hV ≫ structure2 (R := R) R' G =
    structure3 (R := R) R' G ≫ face23 R R' := pullback.lift_snd _ _ _

theorem cartesian12 : IsPullback (chart12 (R := R) R' G) (structure3 (R := R) R' G) (structure2 (R := R) R' G) (face12 R R') := by
  have hp : IsPullback (chart12 (R := R) R' G ≫ projection1 (R := R) R' G) (structure3 (R := R) R' G)
      G.X.hom (face12 R R' ≫ left R R') := by
    rw [chart12_first]
    exact IsPullback.of_hasPullback G.X.hom (face12 R R' ≫ left R R')
  exact hp.of_right (chart12_base (R := R) R' G) (cartesian1 (R := R) R' G)

theorem cartesian13 : IsPullback (chart13 (R := R) R' G) (structure3 (R := R) R' G) (structure2 (R := R) R' G) (face13 R R') := by
  have hp : IsPullback (chart13 (R := R) R' G ≫ projection1 (R := R) R' G) (structure3 (R := R) R' G)
      G.X.hom (face13 R R' ≫ left R R') := by
    rw [chart13_first, ← face12_left R R']
    exact IsPullback.of_hasPullback G.X.hom (face12 R R' ≫ left R R')
  exact hp.of_right (chart13_base (R := R) R' G) (cartesian1 (R := R) R' G)

private theorem transport_congr {T : Scheme.{u}} {x x' : T ⟶ G.X.left} {v v' : T ⟶ Cover R'}
    (hx : x = x') (hv : v = v')
    (h : (x ≫ G.X.hom) ≫ baseMap R R' = v ≫ baseMap R R')
    (h' : (x' ≫ G.X.hom) ≫ baseMap R R' = v' ≫ baseMap R R') :
    (genericModelOfGroupIso (baseMap R R') V G A e).transportMap c hV x v h =
      (genericModelOfGroupIso (baseMap R R') V G A e).transportMap c hV x' v' h' := by
  cases hx
  cases hv
  rfl

/-- Genuine cartesian 23 square, from the actual PROVED chart-1/chart-2
    overlap isomorphism and the canonical model2 pullback. -/
theorem cartesian23 : IsPullback (chart23 R' V G A e c hV) (structure3 (R := R) R' G)
    (structure2 (R := R) R' G) (face23 R R') := by
  let M := genericModelOfGroupIso (baseMap R R') V G A e
  let u₁ := face12 R R' ≫ left R R'
  let u₂ := face23 R R' ≫ left R R'
  have hu : u₁ ≫ baseMap R R' = u₂ ≫ baseMap R R' := by
    dsimp only [u₁, u₂]
    rw [Category.assoc, Category.assoc, left_base R R',
      ← Category.assoc (face12 R R'), face12_right R R', Category.assoc]
    simp only [Category.assoc, left_base R R']
  let E := M.overlapIso c hV u₁ u₂ hu
  let r : model3 (R := R) R' G ⟶ pullback G.X.hom u₂ := E.hom.left
  let Er : model3 (R := R) R' G ≅ pullback G.X.hom u₂ := (Over.forget _).mapIso E
  have hr₂ : r ≫ pullback.snd G.X.hom u₂ = structure3 (R := R) R' G := by
    have h := Over.w E.hom
    change r ≫ pullback.snd G.X.hom u₂ = structure3 (R := R) R' G at h
    exact h
  have hr₁ : r ≫ pullback.fst G.X.hom u₂ =
      M.transportMap c hV (projection3 (R := R) R' G) (structure3 (R := R) R' G ≫ u₂) (toSecond_condition (R := R) R' G) :=
    M.comparisonMap_fst c hV u₁ u₂ hu
  have hp : IsPullback (chart23 R' V G A e c hV ≫ projection1 (R := R) R' G) (structure3 (R := R) R' G) G.X.hom u₂ := by
    refine IsPullback.of_iso_pullback ?_ Er ?_ hr₂
    · constructor
      rw [chart23_first, M.transportMap_base]
    · change r ≫ pullback.fst G.X.hom u₂ = chart23 R' V G A e c hV ≫ projection1 (R := R) R' G
      rw [hr₁, chart23_first]
  exact hp.of_right (chart23_base R' V G A e c hV) (cartesian1 (R := R) R' G)

/-- First tensor-nerve cocycle equation: literal chart-1 point preservation. -/
theorem nerve_eq1 : chart12 (R := R) R' G ≫ projection1 (R := R) R' G = chart13 (R := R) R' G ≫ projection1 (R := R) R' G := by simp

/-- Second equation: actual natural transport from the first point to the
    second, compared with the explicitly constructed chart23 projection. -/
theorem nerve_eq2 : chart12 (R := R) R' G ≫ projection2 R' V G A e c hV =
    chart23 R' V G A e c hV ≫ projection1 (R := R) R' G := by
  let M := genericModelOfGroupIso (baseMap R R') V G A e
  let a := projection1 (R := R) R' G
  let b := structure2 (R := R) R' G ≫ right R R'
  have h : (a ≫ G.X.hom) ≫ baseMap R R' = b ≫ baseMap R R' := by
    rw [pullback.condition, Category.assoc, left_base R R', ← Category.assoc]
  let t := chart12 (R := R) R' G
  have ha : t ≫ a = projection3 (R := R) R' G := chart12_first (R := R) R' G
  have hb : t ≫ b = structure3 (R := R) R' G ≫ face23 R R' ≫ left R R' := by
    dsimp only [b, t]
    rw [← Category.assoc, chart12_base, Category.assoc, face12_right R R']
  have h' : ((t ≫ a) ≫ G.X.hom) ≫ baseMap R R' = (t ≫ b) ≫ baseMap R R' := by
    simpa only [Category.assoc] using congrArg (t ≫ ·) h
  have he := M.transportMap_natural c hV a b h t h'
  have hc := transport_congr R' V G A e c hV ha hb h' (toSecond_condition (R := R) R' G)
  change t ≫ M.comparisonMap c hV (left R R') (right R R') (left_base R R') ≫
      pullback.fst G.X.hom (right R R') = chart23 R' V G A e c hV ≫ projection1 (R := R) R' G
  rw [M.comparisonMap_fst, chart23_first]
  exact he.symm.trans hc

/-- Third equation is the actual global overlap triple cocycle. -/
theorem nerve_eq3 : chart13 (R := R) R' G ≫ projection2 R' V G A e c hV =
    chart23 R' V G A e c hV ≫ projection2 R' V G A e c hV := by
  let M := genericModelOfGroupIso (baseMap R R') V G A e
  let a := projection1 (R := R) R' G
  let b := structure2 (R := R) R' G ≫ right R R'
  let x := projection3 (R := R) R' G
  let v₂ := structure3 (R := R) R' G ≫ face23 R R' ≫ left R R'
  let v₃ := structure3 (R := R) R' G ≫ face23 R R' ≫ right R R'
  have h : (a ≫ G.X.hom) ≫ baseMap R R' = b ≫ baseMap R R' := by
    rw [pullback.condition, Category.assoc, left_base R R', ← Category.assoc]
  have h₂ : (x ≫ G.X.hom) ≫ baseMap R R' = v₂ ≫ baseMap R R' := toSecond_condition (R := R) R' G
  have h₃ : (x ≫ G.X.hom) ≫ baseMap R R' = v₃ ≫ baseMap R R' := h₂.trans (by
    dsimp only [v₂, v₃]
    simp only [Category.assoc, left_base R R'])
  let y := M.transportMap c hV x v₂ h₂
  have h₂₃ : (y ≫ G.X.hom) ≫ baseMap R R' = v₃ ≫ baseMap R R' := by
    rw [M.transportMap_base]
    exact h₂.symm.trans h₃
  have ha₁₃ : chart13 (R := R) R' G ≫ a = x := chart13_first (R := R) R' G
  have hb₁₃ : chart13 (R := R) R' G ≫ b = v₃ := by
    dsimp only [b, v₃]
    rw [← Category.assoc, chart13_base, Category.assoc, face13_right R R']
  have ha₂₃ : chart23 R' V G A e c hV ≫ a = y := chart23_first R' V G A e c hV
  have hb₂₃ : chart23 R' V G A e c hV ≫ b = v₃ := by
    dsimp only [b, v₃]
    rw [← Category.assoc, chart23_base, Category.assoc]
  have hn13 : ((chart13 (R := R) R' G ≫ a) ≫ G.X.hom) ≫ baseMap R R' = (chart13 (R := R) R' G ≫ b) ≫ baseMap R R' := by
    simpa only [Category.assoc] using congrArg (chart13 (R := R) R' G ≫ ·) h
  have hn23 : ((chart23 R' V G A e c hV ≫ a) ≫ G.X.hom) ≫ baseMap R R' =
      (chart23 R' V G A e c hV ≫ b) ≫ baseMap R R' := by
    simpa only [Category.assoc] using congrArg (chart23 R' V G A e c hV ≫ ·) h
  have he13 := (M.transportMap_natural c hV a b h (chart13 (R := R) R' G) hn13).symm.trans
    (transport_congr R' V G A e c hV ha₁₃ hb₁₃ hn13 h₃)
  have he23 := (M.transportMap_natural c hV a b h (chart23 R' V G A e c hV) hn23).symm.trans
    (transport_congr R' V G A e c hV ha₂₃ hb₂₃ hn23 h₂₃)
  have hc := M.transportMap_cocycle c hV x v₂ v₃ h₂ h₃ h₂₃
  change chart13 (R := R) R' G ≫ M.comparisonMap c hV (left R R') (right R R') (left_base R R') ≫
      pullback.fst G.X.hom (right R R') =
    chart23 R' V G A e c hV ≫ M.comparisonMap c hV (left R R') (right R R') (left_base R R') ≫
      pullback.fst G.X.hom (right R R')
  rw [M.comparisonMap_fst]
  change chart13 (R := R) R' G ≫ M.transportMap c hV a b h =
    chart23 R' V G A e c hV ≫ M.transportMap c hV a b h
  exact he13.trans (hc.symm.trans he23.symm)

#print axioms cartesian12
#print axioms cartesian13
#print axioms cartesian23
#print axioms nerve_eq1
#print axioms nerve_eq2
#print axioms nerve_eq3

end ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective.TensorNerve
