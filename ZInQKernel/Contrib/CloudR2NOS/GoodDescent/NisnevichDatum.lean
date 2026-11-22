/-
Copyright (c) 2026 H5/NOS Round-2 Lane5 contributors.
Released under Apache 2.0 license as described in the project LICENSE.

New construction (2026-11-14): transport by gluing the identity on the open
diagonal with the actual generic cartesian comparison. The original generic
scheme is retained. No hdesc/effective quotient/Neron existence is assumed.
-/
import ZInQKernel.Contrib.CloudR2NOS.GoodDescent.EtaleOverlap
import ZInQKernel.Contrib.CloudR2NOS.GoodDescent.GenericTransport
import ZInQKernel.Contrib.CloudR2NOS.GoodDescent.TwoOpenGlue
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.CategoryTheory.Comma.Over.DescentDatum

set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2NOS.GoodDescent

/-- The canonical open lift of an actual scheme morphism. -/
def intoOpen {T Y : Scheme.{u}} (x : T ⟶ Y) (W : Y.Opens)
    (hx : ∀ t : T, x t ∈ W) : T ⟶ W.toScheme :=
  IsOpenImmersion.lift W.ι x (by
    rintro _ ⟨t, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hx t)

@[reassoc (attr := simp)]
theorem intoOpen_ι {T Y : Scheme.{u}} (x : T ⟶ Y) (W : Y.Opens)
    (hx : ∀ t : T, x t ∈ W) : intoOpen x W hx ≫ W.ι = x :=
  IsOpenImmersion.lift_fac _ _ _

theorem intoOpen_natural {T T' Y : Scheme.{u}} (t : T' ⟶ T) (x : T ⟶ Y) (W : Y.Opens)
    (hx : ∀ a : T, x a ∈ W) (hx' : ∀ a : T', (t ≫ x) a ∈ W) :
    intoOpen (t ≫ x) W hx' = t ≫ intoOpen x W hx := by
  apply (cancel_mono W.ι).mp
  simp

namespace GenericModel
variable {X U S : Scheme.{u}} {f : X ⟶ U} {p : U ⟶ S} {V : S.Opens}
  (M : GenericModel f p V)

private theorem generic_condition {T : Scheme.{u}}
    (x : T ⟶ (f ⁻¹ᵁ (p ⁻¹ᵁ V)).toScheme) (v : T ⟶ (p ⁻¹ᵁ V).toScheme)
    (h : (x ≫ (f ⁻¹ᵁ (p ⁻¹ᵁ V)).ι) ≫ f ≫ p = (v ≫ (p ⁻¹ᵁ V).ι) ≫ p) :
    (x ≫ M.q) ≫ M.a = v ≫ (p ∣_ V) := by
  apply (cancel_mono V.ι).mp
  calc
    ((x ≫ M.q) ≫ M.a) ≫ V.ι = x ≫ (f ∣_ (p ⁻¹ᵁ V)) ≫ (p ∣_ V) ≫ V.ι := by
      simp only [Category.assoc, M.cartesian.w]
    _ = (x ≫ (f ⁻¹ᵁ (p ⁻¹ᵁ V)).ι) ≫ f ≫ p := by
      simp only [morphismRestrict_ι, Category.assoc, morphismRestrict_ι_assoc]
    _ = (v ≫ (p ⁻¹ᵁ V).ι) ≫ p := h
    _ = (v ≫ (p ∣_ V)) ≫ V.ι := by
      simp only [Category.assoc, morphismRestrict_ι]

private theorem newBase_generic {T : Scheme.{u}} (x : T ⟶ X) (v : T ⟶ U)
    (h : (x ≫ f) ≫ p = v ≫ p) (hx : ∀ t : T, x t ∈ f ⁻¹ᵁ (p ⁻¹ᵁ V)) :
    ∀ t : T, v t ∈ p ⁻¹ᵁ V := by
  intro t
  have ht := congrArg (fun a : T ⟶ S => a t) h
  simp only [Scheme.Hom.comp_apply] at ht
  change p (v t) ∈ V
  rw [← ht]
  exact hx t

/-- Actual scheme morphism on a wholly generic test scheme, obtained from
    the original generic model by cartesian lift. -/
def genericMap {T : Scheme.{u}} (x : T ⟶ X) (v : T ⟶ U)
    (h : (x ≫ f) ≫ p = v ≫ p) (hx : ∀ t : T, x t ∈ f ⁻¹ᵁ (p ⁻¹ᵁ V)) : T ⟶ X :=
  M.transfer (intoOpen x (f ⁻¹ᵁ (p ⁻¹ᵁ V)) hx)
    (intoOpen v (p ⁻¹ᵁ V) (newBase_generic x v h hx))
    (M.generic_condition _ _ (by simpa only [intoOpen_ι, Category.assoc] using h)) ≫
      (f ⁻¹ᵁ (p ⁻¹ᵁ V)).ι

@[reassoc (attr := simp)]
theorem genericMap_base {T : Scheme.{u}} (x : T ⟶ X) (v : T ⟶ U)
    (h : (x ≫ f) ≫ p = v ≫ p) (hx : ∀ t : T, x t ∈ f ⁻¹ᵁ (p ⁻¹ᵁ V)) :
    M.genericMap x v h hx ≫ f = v := by
  unfold genericMap
  rw [Category.assoc, ← morphismRestrict_ι f (p ⁻¹ᵁ V), ← Category.assoc,
    M.transfer_base, intoOpen_ι]

/-- Identity where the two base morphisms already agree; this is the
    diagonal/generic intersection compatibility, not an hdesc assumption. -/
theorem genericMap_identity {T : Scheme.{u}} (x : T ⟶ X) (v : T ⟶ U)
    (h : (x ≫ f) ≫ p = v ≫ p) (hx : ∀ t : T, x t ∈ f ⁻¹ᵁ (p ⁻¹ᵁ V))
    (hv : x ≫ f = v) : M.genericMap x v h hx = x := by
  let x' := intoOpen x (f ⁻¹ᵁ (p ⁻¹ᵁ V)) hx
  let v' := intoOpen v (p ⁻¹ᵁ V) (newBase_generic x v h hx)
  have he : v' = x' ≫ (f ∣_ (p ⁻¹ᵁ V)) := by
    apply (cancel_mono (p ⁻¹ᵁ V).ι).mp
    calc
      v' ≫ (p ⁻¹ᵁ V).ι = v := intoOpen_ι _ _ _
      _ = x ≫ f := hv.symm
      _ = (x' ≫ (f ∣_ (p ⁻¹ᵁ V))) ≫ (p ⁻¹ᵁ V).ι := by
        simp only [x', Category.assoc, morphismRestrict_ι, intoOpen_ι_assoc]
  have ht : M.transfer x' v' (M.generic_condition _ _ (by simpa only [x', v', intoOpen_ι, Category.assoc] using h)) = x' := by
    apply M.cartesian.hom_ext
    · simp
    · simpa only [M.transfer_base] using he
  change M.transfer x' v' _ ≫ _ = x
  rw [ht]
  exact intoOpen_ι x _ hx

/-- Naturality of the generic comparison as a scheme morphism. -/
theorem genericMap_natural {T T' : Scheme.{u}} (t : T' ⟶ T) (x : T ⟶ X) (v : T ⟶ U)
    (h : (x ≫ f) ≫ p = v ≫ p) (hx : ∀ a : T, x a ∈ f ⁻¹ᵁ (p ⁻¹ᵁ V))
    (h' : ((t ≫ x) ≫ f) ≫ p = (t ≫ v) ≫ p)
    (hx' : ∀ a : T', (t ≫ x) a ∈ f ⁻¹ᵁ (p ⁻¹ᵁ V)) :
    M.genericMap (t ≫ x) (t ≫ v) h' hx' = t ≫ M.genericMap x v h hx := by
  let x' := intoOpen x (f ⁻¹ᵁ (p ⁻¹ᵁ V)) hx
  let v' := intoOpen v (p ⁻¹ᵁ V) (newBase_generic x v h hx)
  let x'' := intoOpen (t ≫ x) (f ⁻¹ᵁ (p ⁻¹ᵁ V)) hx'
  let v'' := intoOpen (t ≫ v) (p ⁻¹ᵁ V) (newBase_generic _ _ h' hx')
  have hxnat : x'' = t ≫ x' := intoOpen_natural t x _ hx hx'
  have hvnat : v'' = t ≫ v' := intoOpen_natural t v _ _ _
  have ht : M.transfer x'' v'' (M.generic_condition _ _ (by simpa only [x'', v'', intoOpen_ι, Category.assoc] using h')) =
      t ≫ M.transfer x' v' (M.generic_condition _ _ (by simpa only [x', v', intoOpen_ι, Category.assoc] using h)) := by
    apply M.cartesian.hom_ext
    · simpa only [Category.assoc, M.transfer_q, M.transfer_q_assoc] using congrArg (· ≫ M.q) hxnat
    · simpa only [Category.assoc, M.transfer_base, M.transfer_base_assoc] using hvnat
  change M.transfer x'' v'' _ ≫ _ = t ≫ M.transfer x' v' _ ≫ _
  rw [ht, Category.assoc]

/-- Genericity of the constructed output follows from its actual base map. -/
theorem genericMap_mem {T : Scheme.{u}} (x : T ⟶ X) (v : T ⟶ U)
    (h : (x ≫ f) ≫ p = v ≫ p) (hx : ∀ t : T, x t ∈ f ⁻¹ᵁ (p ⁻¹ᵁ V)) :
    ∀ t : T, (M.genericMap x v h hx) t ∈ f ⁻¹ᵁ (p ⁻¹ᵁ V) := by
  have he : (M.genericMap x v h hx ≫ f) ≫ p = (x ≫ f) ≫ p :=
    (congrArg (· ≫ p) (M.genericMap_base x v h hx)).trans h.symm
  intro t
  have ht := congrArg (fun a : T ⟶ S => a t) he
  simp only [Scheme.Hom.comp_apply] at ht
  change p (f ((M.genericMap x v h hx) t)) ∈ V
  rw [ht]
  exact hx t

/-- The generic comparison retains the original generic-coordinate map. -/
theorem genericMap_q {T : Scheme.{u}} (x : T ⟶ X) (v : T ⟶ U)
    (h : (x ≫ f) ≫ p = v ≫ p) (hx : ∀ t : T, x t ∈ f ⁻¹ᵁ (p ⁻¹ᵁ V))
    (hy : ∀ t : T, (M.genericMap x v h hx) t ∈ f ⁻¹ᵁ (p ⁻¹ᵁ V)) :
    intoOpen (M.genericMap x v h hx) (f ⁻¹ᵁ (p ⁻¹ᵁ V)) hy ≫ M.q =
      intoOpen x (f ⁻¹ᵁ (p ⁻¹ᵁ V)) hx ≫ M.q := by
  let x' := intoOpen x (f ⁻¹ᵁ (p ⁻¹ᵁ V)) hx
  let v' := intoOpen v (p ⁻¹ᵁ V) (newBase_generic x v h hx)
  let r := M.transfer x' v' (M.generic_condition _ _
    (by simpa only [x', v', intoOpen_ι, Category.assoc] using h))
  have he : intoOpen (M.genericMap x v h hx) (f ⁻¹ᵁ (p ⁻¹ᵁ V)) hy = r := by
    apply (cancel_mono (f ⁻¹ᵁ (p ⁻¹ᵁ V)).ι).mp
    simp only [intoOpen_ι]
    rfl
  rw [he]
  exact M.transfer_q x' v' _

/-- The generic triple comparison is a genuine cocycle. The redundant
    membership witnesses concern the already constructed maps only. -/
theorem genericMap_cocycle {T : Scheme.{u}} (x : T ⟶ X) (v₂ v₃ : T ⟶ U)
    (h₂ : (x ≫ f) ≫ p = v₂ ≫ p) (h₃ : (x ≫ f) ≫ p = v₃ ≫ p)
    (hx : ∀ t : T, x t ∈ f ⁻¹ᵁ (p ⁻¹ᵁ V))
    (hy : ∀ t : T, (M.genericMap x v₂ h₂ hx) t ∈ f ⁻¹ᵁ (p ⁻¹ᵁ V))
    (h₂₃ : (M.genericMap x v₂ h₂ hx ≫ f) ≫ p = v₃ ≫ p)
    (hz : ∀ t : T, (M.genericMap (M.genericMap x v₂ h₂ hx) v₃ h₂₃ hy) t ∈ f ⁻¹ᵁ (p ⁻¹ᵁ V))
    (hz' : ∀ t : T, (M.genericMap x v₃ h₃ hx) t ∈ f ⁻¹ᵁ (p ⁻¹ᵁ V)) :
    M.genericMap (M.genericMap x v₂ h₂ hx) v₃ h₂₃ hy = M.genericMap x v₃ h₃ hx := by
  have he : intoOpen (M.genericMap (M.genericMap x v₂ h₂ hx) v₃ h₂₃ hy)
      (f ⁻¹ᵁ (p ⁻¹ᵁ V)) hz =
      intoOpen (M.genericMap x v₃ h₃ hx) (f ⁻¹ᵁ (p ⁻¹ᵁ V)) hz' := by
    apply M.cartesian.hom_ext
    · rw [M.genericMap_q, M.genericMap_q, M.genericMap_q]
    · apply (cancel_mono (p ⁻¹ᵁ V).ι).mp
      simp only [Category.assoc, morphismRestrict_ι, intoOpen_ι_assoc, M.genericMap_base]
  simpa only [intoOpen_ι] using congrArg (· ≫ (f ⁻¹ᵁ (p ⁻¹ᵁ V)).ι) he

end GenericModel

/-- Open locus where two base maps agree as *morphisms*, defined by the
    actual open diagonal of the finite etale neighbourhood. -/
def equalityOpen {U S T : Scheme.{u}} (p : U ⟶ S) [Etale p]
    (u₁ u₂ : T ⟶ U) (h : u₁ ≫ p = u₂ ≫ p) : T.Opens :=
  (pullback.lift u₁ u₂ h) ⁻¹ᵁ (pullback.diagonal p).opensRange

theorem equalityOpen_eq {U S T : Scheme.{u}} (p : U ⟶ S) [Etale p]
    (u₁ u₂ : T ⟶ U) (h : u₁ ≫ p = u₂ ≫ p) :
    (equalityOpen p u₁ u₂ h).ι ≫ u₁ = (equalityOpen p u₁ u₂ h).ι ≫ u₂ := by
  let W := equalityOpen p u₁ u₂ h
  let a := pullback.lift u₁ u₂ h
  let d : W.toScheme ⟶ U := IsOpenImmersion.lift (pullback.diagonal p) (W.ι ≫ a) (by
    rintro _ ⟨w, rfl⟩
    exact w.2)
  have hd : d ≫ pullback.diagonal p = W.ι ≫ a := IsOpenImmersion.lift_fac _ _ _
  have hd₁ := congrArg (· ≫ pullback.fst p p) hd
  have hd₂ := congrArg (· ≫ pullback.snd p p) hd
  simp only [Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd,
    Category.comp_id, a, pullback.lift_fst, pullback.lift_snd] at hd₁ hd₂
  exact hd₁.symm.trans hd₂

#print axioms GenericModel.genericMap_identity
#print axioms GenericModel.genericMap_natural
#print axioms equalityOpen_eq

end ZInQ.Contrib.CloudR2NOS.GoodDescent
