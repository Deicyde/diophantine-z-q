/-
Copyright (c) 2026 H5/NOS Round-2 Lane5 contributors.
Released under Apache 2.0 license as described in the project LICENSE.

The actual tensor coequalizer comparison implies effectivity of the SAME
constructed scheme datum, on every test scheme. This is the interface
between the real Proj/equalizer constructor and native fpqc/group descent;
no caller-supplied IsEffective datum appears in the direct construction.
-/
import ZInQKernel.Contrib.CloudR2NOS.GoodDescent.Effective.TensorSquare

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective
open TensorCofaces TensorNerve

variable {R : Type u} [CommRing R] (R' : Type u) [CommRing R'] [Algebra R R']
  (V : (Base R).Opens) (G : Grp (Over (Cover R'))) (A : Grp (Over V.toScheme))
  (e : (Over.pullback ((baseMap R R') ⁻¹ᵁ V).ι).mapGrp.obj G ≅
    (Over.pullback ((baseMap R R') ∣_ V)).mapGrp.obj A)
  [Etale (baseMap R R')] (c : Base R)
  [Mono ((baseMap R R').fiberToSpecResidueField c)]
  (hV : ∀ z : Base R, z ∉ V → z = c)

private theorem tensorTransport_condition :
    (projection1 (R := R) R' G ≫ G.X.hom) ≫ baseMap R R' =
      (structure2 (R := R) R' G ≫ right R R') ≫ baseMap R R' := by
  rw [pullback.condition, Category.assoc, left_base R R', ← Category.assoc]

private theorem transport_congr {T : Scheme.{u}} {x x' : T ⟶ G.X.left} {v v' : T ⟶ Cover R'}
    (hx : x = x') (hv : v = v')
    (h : (x ≫ G.X.hom) ≫ baseMap R R' = v ≫ baseMap R R')
    (h' : (x' ≫ G.X.hom) ≫ baseMap R R' = v' ≫ baseMap R R') :
    (genericModelOfGroupIso (baseMap R R') V G A e).transportMap c hV x v h =
      (genericModelOfGroupIso (baseMap R R') V G A e).transportMap c hV x' v' h' := by
  cases hx
  cases hv
  rfl

/-- The SAME originally constructed datum is made effective by the real
    tensor coequalizer output. Its invariance on arbitrary test schemes is
    proved, not merely its equality on geometric/topological points. -/
theorem datum_effective_of_tensor_coequalizer
    (X : Scheme.{u}) (f : X ⟶ Base R) (q : G.X.left ⟶ X)
    (hq : IsPullback q G.X.hom f (baseMap R R'))
    (hco : projection1 (R := R) R' G ≫ q = projection2 R' V G A e c hV ≫ q) :
    (schemeDatumOfGroupIso (baseMap R R') V G A e c hV).IsEffective := by
  refine ⟨Over.mk f, q, hq, ?_⟩
  intro T u₁ u₂ h a
  let M := genericModelOfGroupIso (baseMap R R') V G A e
  let t : T ⟶ Square R R' := (isPullback_square R R').lift u₁ u₂ h
  have ht₁ : t ≫ left R R' = u₁ := (isPullback_square R R').lift_fst _ _ _
  have ht₂ : t ≫ right R R' = u₂ := (isPullback_square R R').lift_snd _ _ _
  have ha : a.left ≫ G.X.hom = u₁ := by simpa only [Over.mk_hom] using Over.w a
  let z : T ⟶ model2 (R := R) R' G := (cartesian1 (R := R) R' G).lift a.left t (ha.trans ht₁.symm)
  have hz₁ : z ≫ projection1 (R := R) R' G = a.left := (cartesian1 (R := R) R' G).lift_fst _ _ _
  have hz₂ : z ≫ structure2 (R := R) R' G = t := (cartesian1 (R := R) R' G).lift_snd _ _ _
  have hv : z ≫ (structure2 (R := R) R' G ≫ right R R') = u₂ := by
    rw [← Category.assoc, hz₂]
    exact ht₂
  let hb := tensorTransport_condition (R := R) R' G
  have h' : ((z ≫ projection1 (R := R) R' G) ≫ G.X.hom) ≫ baseMap R R' =
      (z ≫ (structure2 (R := R) R' G ≫ right R R')) ≫ baseMap R R' := by
    simpa only [Category.assoc] using congrArg (z ≫ ·) hb
  have hx : (a.left ≫ G.X.hom) ≫ baseMap R R' = u₂ ≫ baseMap R R' := (congrArg (· ≫ baseMap R R') ha).trans h
  have hn := M.transportMap_natural c hV (projection1 (R := R) R' G)
    (structure2 (R := R) R' G ≫ right R R') hb z h'
  have hc := transport_congr R' V G A e c hV hz₁ hv h' hx
  have ht : M.transportMap c hV a.left u₂ hx = z ≫ projection2 R' V G A e c hV := by
    have he := hc.symm.trans hn
    change M.transportMap c hV a.left u₂ hx =
      z ≫ M.comparisonMap c hV (left R R') (right R R') (left_base R R') ≫
        pullback.fst G.X.hom (right R R')
    rw [M.comparisonMap_fst]
    exact he
  change M.transportMap c hV a.left u₂ hx ≫ q = a.left ≫ q
  rw [ht, Category.assoc, ← hco, ← Category.assoc, hz₁]

#print axioms datum_effective_of_tensor_coequalizer

end ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective
