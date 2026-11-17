/-
Copyright (c) 2026 H5/NOS Round-2 Lane5 contributors.
Released under Apache 2.0 license as described in the project LICENSE.

New scheme-overlap morphism construction for the henselization route.
Identity on the diagonal is glued to the *constructed* generic comparison.
The overlap compatibility is proved here, not supplied as hdesc.
-/
import ZInQKernel.Contrib.CloudR2NOS.GoodDescent.NisnevichDatum

set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2NOS.GoodDescent

/-- The required test-scheme cover is proved from the special fibre. -/
theorem equality_sup_generic_eq_top
    {U S T : Scheme.{u}} (p : U ⟶ S) [Etale p]
    (s : S) [Mono (p.fiberToSpecResidueField s)]
    (V : S.Opens) (hV : ∀ z : S, z ∉ V → z = s)
    (u₁ u₂ : T ⟶ U) (h : u₁ ≫ p = u₂ ≫ p) :
    equalityOpen p u₁ u₂ h ⊔ (u₁ ≫ p) ⁻¹ᵁ V = ⊤ := by
  have he := preimage_diagonal_sup_generic_eq_top p s V hV (pullback.lift u₁ u₂ h)
  simpa only [equalityOpen, pullback.lift_fst_assoc] using he

namespace GenericModel

variable {X U S : Scheme.{u}} {f : X ⟶ U} {p : U ⟶ S} {V : S.Opens}
  (M : GenericModel f p V)

private theorem onGeneric_mem {T : Scheme.{u}} (x : T ⟶ X) :
    ∀ z : (((x ≫ f) ≫ p) ⁻¹ᵁ V).toScheme,
      ((((x ≫ f) ≫ p) ⁻¹ᵁ V).ι ≫ x) z ∈ f ⁻¹ᵁ (p ⁻¹ᵁ V) := by
  intro z
  change p (f (x z.1)) ∈ V
  exact z.2

/-- The generic part of the comparison is a cartesian lift through the
    specified original generic scheme. -/
def genericPart {T : Scheme.{u}} (x : T ⟶ X) (v : T ⟶ U)
    (h : (x ≫ f) ≫ p = v ≫ p) : (((x ≫ f) ≫ p) ⁻¹ᵁ V).toScheme ⟶ X :=
  M.genericMap ((((x ≫ f) ≫ p) ⁻¹ᵁ V).ι ≫ x)
    ((((x ≫ f) ≫ p) ⁻¹ᵁ V).ι ≫ v)
    (by simpa only [Category.assoc] using congrArg (((((x ≫ f) ≫ p) ⁻¹ᵁ V).ι) ≫ ·) h)
    (onGeneric_mem x)

/-- Genuine compatibility on the diagonal/generic intersection. -/
theorem genericPart_compatible {T : Scheme.{u}} [Etale p]
    (x : T ⟶ X) (v : T ⟶ U) (h : (x ≫ f) ≫ p = v ≫ p) :
    pullback.fst (equalityOpen p (x ≫ f) v h).ι (((x ≫ f) ≫ p) ⁻¹ᵁ V).ι ≫
        ((equalityOpen p (x ≫ f) v h).ι ≫ x) =
      pullback.snd (equalityOpen p (x ≫ f) v h).ι (((x ≫ f) ≫ p) ⁻¹ᵁ V).ι ≫ M.genericPart x v h := by
  let D := equalityOpen p (x ≫ f) v h
  let G := ((x ≫ f) ≫ p) ⁻¹ᵁ V
  let t₁ := pullback.fst D.ι G.ι
  let t₂ := pullback.snd D.ι G.ι
  have hG : ((G.ι ≫ x) ≫ f) ≫ p = (G.ι ≫ v) ≫ p := by
    simpa only [Category.assoc] using congrArg (G.ι ≫ ·) h
  have hP : ((t₂ ≫ (G.ι ≫ x)) ≫ f) ≫ p = (t₂ ≫ (G.ι ≫ v)) ≫ p := by
    simpa only [Category.assoc] using congrArg (t₂ ≫ ·) hG
  have hxP : ∀ a, (t₂ ≫ (G.ι ≫ x)) a ∈ f ⁻¹ᵁ (p ⁻¹ᵁ V) := by
    intro a
    exact onGeneric_mem x (t₂ a)
  have hb : (t₂ ≫ (G.ι ≫ x)) ≫ f = t₂ ≫ (G.ι ≫ v) := by
    have he := congrArg (t₁ ≫ ·) (equalityOpen_eq p (x ≫ f) v h)
    simpa only [t₁, t₂, D, G, Category.assoc, pullback.condition_assoc] using he
  change t₁ ≫ (D.ι ≫ x) = t₂ ≫ M.genericPart x v h
  calc
    t₁ ≫ (D.ι ≫ x) = t₂ ≫ (G.ι ≫ x) := by
      simp only [t₁, t₂, Category.assoc, pullback.condition_assoc]
    _ = M.genericMap (t₂ ≫ (G.ι ≫ x)) (t₂ ≫ (G.ι ≫ v)) hP hxP :=
      (M.genericMap_identity _ _ hP hxP hb).symm
    _ = t₂ ≫ M.genericPart x v h :=
      M.genericMap_natural t₂ _ _ hG (onGeneric_mem x) hP hxP

/-- The actual global overlap morphism. This constructs the morphism itself,
    not a proposition saying that some descent data have been supplied. -/
def transportMap [Etale p] (s : S) [Mono (p.fiberToSpecResidueField s)]
    (hV : ∀ z : S, z ∉ V → z = s) {T : Scheme.{u}}
    (x : T ⟶ X) (v : T ⟶ U) (h : (x ≫ f) ≫ p = v ≫ p) : T ⟶ X :=
  glueTwo (equality_sup_generic_eq_top p s V hV (x ≫ f) v h)
    ((equalityOpen p (x ≫ f) v h).ι ≫ x) (M.genericPart x v h)
    (M.genericPart_compatible x v h)

@[reassoc (attr := simp)]
theorem transportMap_diagonal [Etale p] (s : S) [Mono (p.fiberToSpecResidueField s)]
    (hV : ∀ z : S, z ∉ V → z = s) {T : Scheme.{u}}
    (x : T ⟶ X) (v : T ⟶ U) (h : (x ≫ f) ≫ p = v ≫ p) :
    (equalityOpen p (x ≫ f) v h).ι ≫ M.transportMap s hV x v h =
      (equalityOpen p (x ≫ f) v h).ι ≫ x := by
  exact ι_glueTwo_left _ _ _ _

@[reassoc (attr := simp)]
theorem transportMap_generic [Etale p] (s : S) [Mono (p.fiberToSpecResidueField s)]
    (hV : ∀ z : S, z ∉ V → z = s) {T : Scheme.{u}}
    (x : T ⟶ X) (v : T ⟶ U) (h : (x ≫ f) ≫ p = v ≫ p) :
    ((((x ≫ f) ≫ p) ⁻¹ᵁ V).ι) ≫ M.transportMap s hV x v h = M.genericPart x v h := by
  exact ι_glueTwo_right _ _ _ _

/-- The glued morphism lies over the second base morphism. -/
@[reassoc (attr := simp)]
theorem transportMap_base [Etale p] (s : S) [Mono (p.fiberToSpecResidueField s)]
    (hV : ∀ z : S, z ∉ V → z = s) {T : Scheme.{u}}
    (x : T ⟶ X) (v : T ⟶ U) (h : (x ≫ f) ≫ p = v ≫ p) :
    M.transportMap s hV x v h ≫ f = v := by
  apply hom_ext_two (equality_sup_generic_eq_top p s V hV (x ≫ f) v h)
  · rw [← Category.assoc, M.transportMap_diagonal, Category.assoc]
    exact equalityOpen_eq p (x ≫ f) v h
  · rw [← Category.assoc, M.transportMap_generic]
    exact M.genericMap_base _ _ _ _

/-- On any test lying on the diagonal the constructed comparison is the
    identity. The test need not be reduced, affine, or field-valued. -/
theorem transportMap_on_equal [Etale p] (s : S) [Mono (p.fiberToSpecResidueField s)]
    (hV : ∀ z : S, z ∉ V → z = s) {T T' : Scheme.{u}}
    (x : T ⟶ X) (v : T ⟶ U) (h : (x ≫ f) ≫ p = v ≫ p)
    (t : T' ⟶ T) (ht : (t ≫ x) ≫ f = t ≫ v) :
    t ≫ M.transportMap s hV x v h = t ≫ x := by
  let D := equalityOpen p (x ≫ f) v h
  have hp : t ≫ pullback.lift (x ≫ f) v h = (t ≫ x ≫ f) ≫ pullback.diagonal p := by
    apply pullback.hom_ext
    · simp
    · simpa only [Category.assoc, pullback.lift_snd, pullback.diagonal_snd,
        Category.comp_id] using ht.symm
  have hmem : ∀ a : T', t a ∈ D := by
    intro a
    change (pullback.lift (x ≫ f) v h) (t a) ∈ Set.range (pullback.diagonal p)
    refine ⟨(t ≫ x ≫ f) a, ?_⟩
    have ha := congrArg (fun q : T' ⟶ pullback p p => q a) hp
    simpa only [Scheme.Hom.comp_apply] using ha.symm
  let r := intoOpen t D hmem
  calc
    t ≫ M.transportMap s hV x v h = r ≫ D.ι ≫ M.transportMap s hV x v h := by simp [r]
    _ = r ≫ D.ι ≫ x := by rw [M.transportMap_diagonal]
    _ = t ≫ x := by simp [r]

/-- On any wholly generic test, the global comparison equals the actual
    generic cartesian lift. -/
theorem transportMap_on_generic [Etale p] (s : S) [Mono (p.fiberToSpecResidueField s)]
    (hV : ∀ z : S, z ∉ V → z = s) {T T' : Scheme.{u}}
    (x : T ⟶ X) (v : T ⟶ U) (h : (x ≫ f) ≫ p = v ≫ p)
    (t : T' ⟶ T) (ht : ∀ a : T', (t ≫ x) a ∈ f ⁻¹ᵁ (p ⁻¹ᵁ V))
    (h' : ((t ≫ x) ≫ f) ≫ p = (t ≫ v) ≫ p) :
    t ≫ M.transportMap s hV x v h = M.genericMap (t ≫ x) (t ≫ v) h' ht := by
  let G := ((x ≫ f) ≫ p) ⁻¹ᵁ V
  have hmem : ∀ a : T', t a ∈ G := by
    intro a
    change p (f (x (t a))) ∈ V
    exact ht a
  let r := intoOpen t G hmem
  have hrx : r ≫ (G.ι ≫ x) = t ≫ x := by simp [r]
  have hrv : r ≫ (G.ι ≫ v) = t ≫ v := by simp [r]
  have hG : ((G.ι ≫ x) ≫ f) ≫ p = (G.ι ≫ v) ≫ p := by
    simpa only [Category.assoc] using congrArg (G.ι ≫ ·) h
  have hr : ((r ≫ (G.ι ≫ x)) ≫ f) ≫ p = (r ≫ (G.ι ≫ v)) ≫ p := by
    rw [hrx, hrv]
    exact h'
  have hxr : ∀ a, (r ≫ (G.ι ≫ x)) a ∈ f ⁻¹ᵁ (p ⁻¹ᵁ V) := by
    rw [hrx]
    exact ht
  have hn := M.genericMap_natural r (G.ι ≫ x) (G.ι ≫ v) hG (onGeneric_mem x) hr hxr
  calc
    t ≫ M.transportMap s hV x v h = r ≫ G.ι ≫ M.transportMap s hV x v h := by simp [r]
    _ = r ≫ M.genericPart x v h := by rw [M.transportMap_generic]
    _ = M.genericMap (t ≫ x) (t ≫ v) h' ht := by
      change r ≫ M.genericMap (G.ι ≫ x) (G.ι ≫ v) _ _ = M.genericMap (t ≫ x) (t ≫ v) h' ht
      simpa only [hrx, hrv] using hn.symm

/-- Identity of the global comparison whenever the base morphisms agree. -/
theorem transportMap_identity [Etale p] (s : S) [Mono (p.fiberToSpecResidueField s)]
    (hV : ∀ z : S, z ∉ V → z = s) {T : Scheme.{u}}
    (x : T ⟶ X) (v : T ⟶ U) (h : (x ≫ f) ≫ p = v ≫ p)
    (hv : x ≫ f = v) : M.transportMap s hV x v h = x := by
  have he := M.transportMap_on_equal s hV x v h (𝟙 T) (by simpa using hv)
  simpa using he

/-- Naturality of the constructed global overlap morphism. -/
theorem transportMap_natural [Etale p] (s : S) [Mono (p.fiberToSpecResidueField s)]
    (hV : ∀ z : S, z ∉ V → z = s) {T T' : Scheme.{u}}
    (x : T ⟶ X) (v : T ⟶ U) (h : (x ≫ f) ≫ p = v ≫ p)
    (t : T' ⟶ T) (h' : ((t ≫ x) ≫ f) ≫ p = (t ≫ v) ≫ p) :
    M.transportMap s hV (t ≫ x) (t ≫ v) h' = t ≫ M.transportMap s hV x v h := by
  let D := equalityOpen p ((t ≫ x) ≫ f) (t ≫ v) h'
  let G := (((t ≫ x) ≫ f) ≫ p) ⁻¹ᵁ V
  apply hom_ext_two (equality_sup_generic_eq_top p s V hV ((t ≫ x) ≫ f) (t ≫ v) h')
  · have he : (D.ι ≫ (t ≫ x)) ≫ f = D.ι ≫ (t ≫ v) := by
      simpa only [Category.assoc] using equalityOpen_eq p ((t ≫ x) ≫ f) (t ≫ v) h'
    have he' : ((D.ι ≫ t) ≫ x) ≫ f = (D.ι ≫ t) ≫ v := by
      simpa only [Category.assoc] using he
    calc
      D.ι ≫ M.transportMap s hV (t ≫ x) (t ≫ v) h' = D.ι ≫ (t ≫ x) :=
        M.transportMap_on_equal s hV _ _ h' D.ι he
      _ = (D.ι ≫ t) ≫ x := (Category.assoc ..).symm
      _ = (D.ι ≫ t) ≫ M.transportMap s hV x v h :=
        (M.transportMap_on_equal s hV x v h (D.ι ≫ t) he').symm
      _ = D.ι ≫ t ≫ M.transportMap s hV x v h := Category.assoc ..
  · have hG : ((G.ι ≫ (t ≫ x)) ≫ f) ≫ p = (G.ι ≫ (t ≫ v)) ≫ p := by
      simpa only [Category.assoc] using congrArg (G.ι ≫ ·) h'
    have hG' : (((G.ι ≫ t) ≫ x) ≫ f) ≫ p = ((G.ι ≫ t) ≫ v) ≫ p := by
      simpa only [Category.assoc] using hG
    have hg : ∀ a, (G.ι ≫ (t ≫ x)) a ∈ f ⁻¹ᵁ (p ⁻¹ᵁ V) := onGeneric_mem (t ≫ x)
    have hg' : ∀ a, ((G.ι ≫ t) ≫ x) a ∈ f ⁻¹ᵁ (p ⁻¹ᵁ V) := by
      simpa only [Category.assoc] using hg
    rw [M.transportMap_on_generic s hV _ _ h' G.ι hg hG]
    have he := M.transportMap_on_generic s hV x v h (G.ι ≫ t) hg' hG'
    simpa only [Category.assoc] using he.symm

end GenericModel

#print axioms GenericModel.genericPart_compatible
#print axioms GenericModel.transportMap_base
#print axioms GenericModel.transportMap_on_equal

end ZInQ.Contrib.CloudR2NOS.GoodDescent
