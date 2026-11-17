/-
Copyright (c) 2026 H5/NOS Round-2 Lane5 contributors.
Released under Apache 2.0 license as described in the project LICENSE.

Generic-open part of the SAME constructed tensor nerve. All overlap maps,
cartesian squares and invariance use the frozen original transport maps.
No effective generic scheme isomorphism or generic invariance premise is
supplied. This is an intermediate for the original-A generic comparison.
-/
import ZInQKernel.Contrib.CloudR2NOS.GoodDescent.Effective.TensorSquare
import ZInQKernel.Contrib.CloudR2NOS.GoodDescent.Effective.GenericRestrict

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective
open TensorCofaces TensorNerve

section RestrictEq
variable {X X' U S : Scheme.{u}} {q : X' ⟶ X} {f' : X' ⟶ U} {f : X ⟶ S} {p : U ⟶ S}
  (hc : IsPullback q f' f p) (V : S.Opens) (W : X'.Opens)
  (hW : W = f' ⁻¹ᵁ (p ⁻¹ᵁ V))

/-- Restriction to the exact given source open, preserving the same comparison. -/
def genericMapOnEqOpen : W.toScheme ⟶ (f ⁻¹ᵁ V).toScheme :=
  (opensEqIso hW).hom ≫ genericCartMap hc V

@[reassoc (attr := simp)]
theorem genericMapOnEqOpen_ι : genericMapOnEqOpen hc V W hW ≫ (f ⁻¹ᵁ V).ι = W.ι ≫ q := by
  rw [genericMapOnEqOpen, Category.assoc, genericCartMap_ι, ← Category.assoc, opensEqIso_hom_ι]

/-- The actual open-restricted square retains its original ambient base morphism. -/
theorem genericMapOnEqOpen_isPullback : IsPullback (genericMapOnEqOpen hc V W hW)
    (W.ι ≫ f') ((f ⁻¹ᵁ V).ι ≫ f) p := by
  let h := genericCart_isPullback hc V
  let E := opensEqIso hW ≪≫ h.isoPullback
  refine IsPullback.of_iso_pullback ?_ E ?_ ?_
  · constructor
    rw [← Category.assoc, genericMapOnEqOpen_ι, Category.assoc, hc.w]
    exact (Category.assoc W.ι f' p).symm
  · simp only [E, Iso.trans_hom, Category.assoc, h.isoPullback_hom_fst]
    rfl
  · rw [show E.hom = (opensEqIso hW).hom ≫ h.isoPullback.hom from rfl,
      Category.assoc, h.isoPullback_hom_snd, ← Category.assoc, opensEqIso_hom_ι]
end RestrictEq

section Tensor
variable {R : Type u} [CommRing R] (R' : Type u) [CommRing R'] [Algebra R R']
  (V : (Base R).Opens) (G : Grp (Over (Cover R'))) (A : Grp (Over V.toScheme))
  (e : (Over.pullback ((baseMap R R') ⁻¹ᵁ V).ι).mapGrp.obj G ≅
    (Over.pullback ((baseMap R R') ∣_ V)).mapGrp.obj A)
  [Etale (baseMap R R')] (c : Base R) [Mono ((baseMap R R').fiberToSpecResidueField c)]
  (hV : ∀ z : Base R, z ∉ V → z = c)

abbrev modelGenericOpen : G.X.left.Opens := G.X.hom ⁻¹ᵁ ((baseMap R R') ⁻¹ᵁ V)
abbrev modelSquareGenericOpen : (model2 (R := R) R' G).Opens :=
  structure2 (R := R) R' G ⁻¹ᵁ (left R R' ⁻¹ᵁ ((baseMap R R') ⁻¹ᵁ V))

private theorem squareGeneric_right : modelSquareGenericOpen R' V G =
    structure2 (R := R) R' G ⁻¹ᵁ (right R R' ⁻¹ᵁ ((baseMap R R') ⁻¹ᵁ V)) := by
  dsimp only [modelSquareGenericOpen]
  rw [← Scheme.Hom.comp_preimage (left R R') (baseMap R R'),
    ← Scheme.Hom.comp_preimage (right R R') (baseMap R R'), left_base R R']

/-- Actual two restricted model projections on the original generic locus. -/
def genericProjection1 : (modelSquareGenericOpen R' V G).toScheme ⟶ (modelGenericOpen R' V G).toScheme :=
  genericMapOnEqOpen (cartesian1 (R := R) R' G) ((baseMap R R') ⁻¹ᵁ V)
    (modelSquareGenericOpen R' V G) rfl

def genericProjection2 : (modelSquareGenericOpen R' V G).toScheme ⟶ (modelGenericOpen R' V G).toScheme :=
  genericMapOnEqOpen (cartesian2 R' V G A e c hV) ((baseMap R R') ⁻¹ᵁ V)
    (modelSquareGenericOpen R' V G) (squareGeneric_right R' V G)

abbrev genericStructure1 : (modelGenericOpen R' V G).toScheme ⟶ Cover R' :=
  (modelGenericOpen R' V G).ι ≫ G.X.hom
abbrev genericStructure2 : (modelSquareGenericOpen R' V G).toScheme ⟶ Square R R' :=
  (modelSquareGenericOpen R' V G).ι ≫ structure2 (R := R) R' G

@[reassoc (attr := simp)]
theorem genericProjection1_ι : genericProjection1 R' V G ≫ (modelGenericOpen R' V G).ι =
    (modelSquareGenericOpen R' V G).ι ≫ projection1 (R := R) R' G :=
  genericMapOnEqOpen_ι _ _ _ _

@[reassoc (attr := simp)]
theorem genericProjection2_ι : genericProjection2 R' V G A e c hV ≫ (modelGenericOpen R' V G).ι =
    (modelSquareGenericOpen R' V G).ι ≫ projection2 R' V G A e c hV :=
  genericMapOnEqOpen_ι _ _ _ _

theorem genericCartesian1 : IsPullback (genericProjection1 R' V G) (genericStructure2 R' V G)
    (genericStructure1 R' V G) (left R R') := genericMapOnEqOpen_isPullback _ _ _ _

theorem genericCartesian2 : IsPullback (genericProjection2 R' V G A e c hV) (genericStructure2 R' V G)
    (genericStructure1 R' V G) (right R R') := genericMapOnEqOpen_isPullback _ _ _ _

/-- The generic coordinate q of the ORIGINAL generic GROUP iso is invariant
    under the SAME original second-chart transport, on every scheme test. -/
theorem genericCoordinate_invariant :
    genericProjection1 R' V G ≫ (genericModelOfGroupIso (baseMap R R') V G A e).q =
      genericProjection2 R' V G A e c hV ≫ (genericModelOfGroupIso (baseMap R R') V G A e).q := by
  let M := genericModelOfGroupIso (baseMap R R') V G A e
  let T := (modelSquareGenericOpen R' V G).toScheme
  let t : T ⟶ model2 (R := R) R' G := (modelSquareGenericOpen R' V G).ι
  let x : T ⟶ G.X.left := t ≫ projection1 (R := R) R' G
  let v : T ⟶ Cover R' := t ≫ structure2 (R := R) R' G ≫ right R R'
  have hx : ∀ z : T, x z ∈ modelGenericOpen R' V G := by
    intro z
    change (baseMap R R') (G.X.hom (projection1 (R := R) R' G z.val)) ∈ V
    have h := congrArg (fun m : model2 (R := R) R' G ⟶ Cover R' => m z.val) (cartesian1 (R := R) R' G).w
    simp only [Scheme.Hom.comp_apply] at h
    rw [h]
    exact z.property
  let b := structure2 (R := R) R' G ≫ right R R'
  have h : (projection1 (R := R) R' G ≫ G.X.hom) ≫ baseMap R R' = b ≫ baseMap R R' := by
    dsimp only [b]
    rw [(cartesian1 (R := R) R' G).w, Category.assoc, left_base R R', ← Category.assoc]
  have hb : (x ≫ G.X.hom) ≫ baseMap R R' = v ≫ baseMap R R' := by
    simpa only [x, v, b, Category.assoc] using congrArg (t ≫ ·) h
  have htransport : M.transportMap c hV x v hb = t ≫ projection2 R' V G A e c hV := by
    have hn := M.transportMap_natural c hV (projection1 (R := R) R' G) b h t hb
    change M.transportMap c hV x v hb =
      t ≫ M.comparisonMap c hV (left R R') (right R R') (left_base R R') ≫
        pullback.fst G.X.hom (right R R')
    rw [M.comparisonMap_fst]
    exact hn
  have hgen : M.genericMap x v hb hx = t ≫ projection2 R' V G A e c hV := by
    have hid : ((𝟙 T ≫ x) ≫ G.X.hom) ≫ baseMap R R' = (𝟙 T ≫ v) ≫ baseMap R R' := by
      simpa only [Category.id_comp] using hb
    have hg := M.transportMap_on_generic c hV x v hb (𝟙 T)
      (by simpa only [Category.id_comp] using hx) hid
    have hg' : M.transportMap c hV x v hb = M.genericMap x v hb hx := by
      simpa only [Category.id_comp] using hg
    exact hg'.symm.trans htransport
  have hy : ∀ z : T, (M.genericMap x v hb hx) z ∈ modelGenericOpen R' V G := M.genericMap_mem x v hb hx
  have hq := M.genericMap_q x v hb hx hy
  have he₁ : intoOpen x (modelGenericOpen R' V G) hx = genericProjection1 R' V G := by
    apply (cancel_mono (modelGenericOpen R' V G).ι).mp
    rw [intoOpen_ι, genericProjection1_ι]
  have he₂ : intoOpen (M.genericMap x v hb hx) (modelGenericOpen R' V G) hy = genericProjection2 R' V G A e c hV := by
    apply (cancel_mono (modelGenericOpen R' V G).ι).mp
    rw [intoOpen_ι, genericProjection2_ι]
    exact hgen
  rw [he₁, he₂] at hq
  exact hq.symm

#print axioms genericCartesian1
#print axioms genericCartesian2
#print axioms genericCoordinate_invariant

end Tensor
end ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective
