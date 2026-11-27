import Mathlib

/-! # cmheight62-p1: values of regular functions at complex points

`ev q V s ∈ ℂ` is the value of `s ∈ Γ(X, V)` at a morphism `q : Spec ℂ → X` (`0` if `q ∉ V`),
the common shape of `GroupModel.evalAt` and `LeafPush2.cEvalAt`. Composition, restriction and
ring operations. -/

set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.CMHeight62

open CategoryTheory AlgebraicGeometry

/-- The value of a regular function at a complex point. -/
def ev {X : Scheme.{0}} (q : Spec (CommRingCat.of ℂ) ⟶ X) (V : X.Opens) (s : Γ(X, V)) : ℂ := by
  classical
  exact if h : ⊤ ≤ q ⁻¹ᵁ V then (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (q.appLE V ⊤ h s) else 0

/-- Evaluation at a point of `V` is a ring homomorphism. -/
def evHom {X : Scheme.{0}} (q : Spec (CommRingCat.of ℂ) ⟶ X) (V : X.Opens) (h : ⊤ ≤ q ⁻¹ᵁ V) :
    Γ(X, V) →+* ℂ :=
  ((q.appLE V ⊤ h) ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom).hom

theorem ev_eq_evHom {X : Scheme.{0}} (q : Spec (CommRingCat.of ℂ) ⟶ X) (V : X.Opens)
    (h : ⊤ ≤ q ⁻¹ᵁ V) (s : Γ(X, V)) : ev q V s = evHom q V h s := by
  unfold ev; rw [dite_eq_left h]; rfl

theorem ev_mul {X : Scheme.{0}} (q : Spec (CommRingCat.of ℂ) ⟶ X) (V : X.Opens)
    (h : ⊤ ≤ q ⁻¹ᵁ V) (s t : Γ(X, V)) : ev q V (s * t) = ev q V s * ev q V t := by
  simp only [ev_eq_evHom q V h, map_mul]

theorem ev_neg {X : Scheme.{0}} (q : Spec (CommRingCat.of ℂ) ⟶ X) (V : X.Opens)
    (h : ⊤ ≤ q ⁻¹ᵁ V) (s : Γ(X, V)) : ev q V (-s) = -ev q V s := by
  simp only [ev_eq_evHom q V h, map_neg]

/-- Composition. -/
theorem ev_comp {X Y : Scheme.{0}} (q : Spec (CommRingCat.of ℂ) ⟶ X) (f : X ⟶ Y) (V : Y.Opens)
    (s : Γ(Y, V)) : ev (q ≫ f) V s = ev q (f ⁻¹ᵁ V) (f.app V s) := by
  unfold ev
  by_cases h : ⊤ ≤ (q ≫ f) ⁻¹ᵁ V
  · have h' : ⊤ ≤ q ⁻¹ᵁ (f ⁻¹ᵁ V) := h
    rw [dite_eq_left h, dite_eq_left h']
    congr 1
  · have h' : ¬ ⊤ ≤ q ⁻¹ᵁ (f ⁻¹ᵁ V) := h
    rw [dite_eq_right h, dite_eq_right h']

/-- Restriction. -/
theorem ev_res {X : Scheme.{0}} (q : Spec (CommRingCat.of ℂ) ⟶ X) {V W : X.Opens}
    (i : W ≤ V) (h : ⊤ ≤ q ⁻¹ᵁ W) (s : Γ(X, V)) :
    ev q V s = ev q W (X.presheaf.map (homOfLE i).op s) := by
  have hV : ⊤ ≤ q ⁻¹ᵁ V := h.trans (q.preimage_mono i)
  unfold ev
  rw [dite_eq_left hV, dite_eq_left h]
  congr 1
  have := Scheme.Hom.map_appLE q (V := ⊤) (U := W) (U' := V) h (homOfLE i).op
  exact ((congrArg (fun φ => φ.hom s) this).trans rfl).symm

end ZInQ.Contrib.CMHeight62
