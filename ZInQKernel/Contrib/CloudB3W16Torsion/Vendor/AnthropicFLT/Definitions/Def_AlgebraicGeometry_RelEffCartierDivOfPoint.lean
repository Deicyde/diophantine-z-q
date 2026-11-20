/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelEffCartierDiv

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) {T : Scheme.{u}} {g : T ⟶ S}

noncomputable def graphOver (a : T ⟶ 𝒞) (ha : a ≫ f = g) : T ⟶ pullback f g :=
  pullback.lift a (𝟙 T) (ha.trans (Category.id_comp g).symm)

lemma graphOver_eq_lift (a : T ⟶ 𝒞) (ha : a ≫ f = g) :
    graphOver f a ha = pullback.lift a (𝟙 T) (ha.trans (Category.id_comp g).symm) := rfl

@[reassoc (attr := simp)]
lemma graphOver_fst (a : T ⟶ 𝒞) (ha : a ≫ f = g) :
    graphOver f a ha ≫ pullback.fst f g = a :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma graphOver_snd (a : T ⟶ 𝒞) (ha : a ≫ f = g) :
    graphOver f a ha ≫ pullback.snd f g = 𝟙 T :=
  pullback.lift_snd _ _ _

instance isClosedImmersion_graphOver [IsSeparated f] (a : T ⟶ 𝒞) (ha : a ≫ f = g) :
    IsClosedImmersion (graphOver f a ha) := by
  have : IsClosedImmersion (graphOver f a ha ≫ pullback.snd f g) := by
    rw [graphOver_snd]; infer_instance
  exact .of_comp (graphOver f a ha) (pullback.snd f g)

instance isIso_ker_graphOver_subschemeIota_snd [IsSeparated f] (a : T ⟶ 𝒞) (ha : a ≫ f = g) :
    IsIso ((graphOver f a ha).ker.subschemeι ≫ pullback.snd f g) := by
  have h : (graphOver f a ha).toImage ≫ ((graphOver f a ha).ker.subschemeι ≫ pullback.snd f g)
      = 𝟙 T := by
    rw [← Category.assoc]
    change ((graphOver f a ha).toImage ≫ (graphOver f a ha).imageι) ≫ _ = _
    rw [Scheme.Hom.toImage_imageι, graphOver_snd]
  exact IsIso.of_isIso_fac_left h

noncomputable def RelEffCartierDiv.ofPoint [IsSeparated f] (a : T ⟶ 𝒞) (ha : a ≫ f = g) :
    RelEffCartierDiv f 1 g where
  I := (graphOver f a ha).ker
  isFinite := inferInstance
  flat := inferInstance
  locallyOfFinitePresentation := inferInstance
  finrank_eq t := by
    rw [Scheme.Hom.finrank_eq_one_of_isIso ((graphOver f a ha).ker.subschemeι ≫ pullback.snd f g)]
    rfl

@[simp] lemma RelEffCartierDiv.ofPoint_I [IsSeparated f] (a : T ⟶ 𝒞) (ha : a ≫ f = g) :
    (RelEffCartierDiv.ofPoint f a ha).I = (graphOver f a ha).ker := rfl

variable {f} in

instance RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one (D : RelEffCartierDiv f 1 g) :
    IsIso (D.I.subschemeι ≫ pullback.snd f g) := by
  have := D.isFinite
  have := D.flat
  exact (Scheme.Hom.isIso_iff_finrank_eq _).mpr (funext fun t => D.finrank_eq t)

variable {f} in

noncomputable def RelEffCartierDiv.toPoint (D : RelEffCartierDiv f 1 g) : T ⟶ 𝒞 :=
  inv (D.I.subschemeι ≫ pullback.snd f g) ≫ D.I.subschemeι ≫ pullback.fst f g

variable {f} in

@[reassoc (attr := simp)]
lemma RelEffCartierDiv.toPoint_comp (D : RelEffCartierDiv f 1 g) : D.toPoint ≫ f = g := by
  calc D.toPoint ≫ f
      = inv (D.I.subschemeι ≫ pullback.snd f g) ≫ D.I.subschemeι ≫ (pullback.fst f g ≫ f) := by
        simp only [RelEffCartierDiv.toPoint, Category.assoc]
    _ = inv (D.I.subschemeι ≫ pullback.snd f g) ≫ (D.I.subschemeι ≫ pullback.snd f g) ≫ g := by
        rw [pullback.condition, Category.assoc]
    _ = g := by rw [IsIso.inv_hom_id_assoc]

end AlgebraicGeometry
