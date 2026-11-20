/-
Copyright (c) 2026 H5/NOS Round-2 Lane5 contributors.
Released under Apache 2.0 license as described in the project LICENSE.
New constructive generic-overlap transport for henselization-specific descent.
The common target is the ORIGINAL generic model; no overlap isomorphism,
cocycle, effective quotient or model properness is postulated here.
-/
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.Etale

set_option autoImplicit false
noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2NOS.GoodDescent

/-- The actual generic-fibre identification, in cartesian-square form.
    `A` is the specified original generic scheme, not a replacement fibre.
    A group-object generic isomorphism supplies this square after forgetting
    only for this scheme-level construction. Group compatibility is retained
    separately when packaging the descended group object. -/
structure GenericModel {X U S : Scheme.{u}} (f : X ⟶ U) (p : U ⟶ S) (V : S.Opens) where
  A : Scheme.{u}
  a : A ⟶ V.toScheme
  q : (f ⁻¹ᵁ (p ⁻¹ᵁ V)).toScheme ⟶ A
  cartesian : IsPullback q (f ∣_ (p ⁻¹ᵁ V)) a (p ∣_ V)

namespace GenericModel

variable {X U S : Scheme.{u}} {f : X ⟶ U} {p : U ⟶ S} {V : S.Opens}
  (M : GenericModel f p V)

/-- Construct the comparison on the generic open by the *actual* cartesian
    square, not by assuming that the two model pullbacks are isomorphic. -/
def transfer {T : Scheme.{u}}
    (x : T ⟶ (f ⁻¹ᵁ (p ⁻¹ᵁ V)).toScheme)
    (v : T ⟶ (p ⁻¹ᵁ V).toScheme)
    (h : (x ≫ M.q) ≫ M.a = v ≫ (p ∣_ V)) :
    T ⟶ (f ⁻¹ᵁ (p ⁻¹ᵁ V)).toScheme :=
  M.cartesian.lift (x ≫ M.q) v h

@[reassoc (attr := simp)]
theorem transfer_q {T : Scheme.{u}}
    (x : T ⟶ (f ⁻¹ᵁ (p ⁻¹ᵁ V)).toScheme)
    (v : T ⟶ (p ⁻¹ᵁ V).toScheme)
    (h : (x ≫ M.q) ≫ M.a = v ≫ (p ∣_ V)) :
    M.transfer x v h ≫ M.q = x ≫ M.q :=
  M.cartesian.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem transfer_base {T : Scheme.{u}}
    (x : T ⟶ (f ⁻¹ᵁ (p ⁻¹ᵁ V)).toScheme)
    (v : T ⟶ (p ⁻¹ᵁ V).toScheme)
    (h : (x ≫ M.q) ≫ M.a = v ≫ (p ∣_ V)) :
    M.transfer x v h ≫ (f ∣_ (p ⁻¹ᵁ V)) = v :=
  M.cartesian.lift_snd _ _ _

/-- Identity on the generic open. -/
@[simp]
theorem transfer_self {T : Scheme.{u}}
    (x : T ⟶ (f ⁻¹ᵁ (p ⁻¹ᵁ V)).toScheme) :
    M.transfer x (x ≫ (f ∣_ (p ⁻¹ᵁ V)))
      (by rw [Category.assoc, M.cartesian.w, Category.assoc]) = x := by
  apply M.cartesian.hom_ext <;> simp

/-- Naturality of the actual comparison morphism. -/
theorem transfer_natural {T T' : Scheme.{u}} (t : T' ⟶ T)
    (x : T ⟶ (f ⁻¹ᵁ (p ⁻¹ᵁ V)).toScheme)
    (v : T ⟶ (p ⁻¹ᵁ V).toScheme)
    (h : (x ≫ M.q) ≫ M.a = v ≫ (p ∣_ V)) :
    t ≫ M.transfer x v h =
      M.transfer (t ≫ x) (t ≫ v) (by simpa only [Category.assoc] using congrArg (t ≫ ·) h) := by
  apply M.cartesian.hom_ext <;> simp

/-- The generic triple-overlap cocycle is proved by uniqueness of the
    cartesian lift, preserving the original generic map `M.q`. -/
theorem transfer_cocycle {T : Scheme.{u}}
    (x : T ⟶ (f ⁻¹ᵁ (p ⁻¹ᵁ V)).toScheme)
    (v₂ v₃ : T ⟶ (p ⁻¹ᵁ V).toScheme)
    (h₂ : (x ≫ M.q) ≫ M.a = v₂ ≫ (p ∣_ V))
    (h₃ : (x ≫ M.q) ≫ M.a = v₃ ≫ (p ∣_ V)) :
    M.transfer (M.transfer x v₂ h₂) v₃ (by rw [M.transfer_q]; exact h₃) =
      M.transfer x v₃ h₃ := by
  apply M.cartesian.hom_ext <;> simp

/-- The reverse generic comparison is the inverse, not an independently
    chosen or assumed isomorphism. -/
theorem transfer_inverse {T : Scheme.{u}}
    (x : T ⟶ (f ⁻¹ᵁ (p ⁻¹ᵁ V)).toScheme)
    (v₂ : T ⟶ (p ⁻¹ᵁ V).toScheme)
    (h₂ : (x ≫ M.q) ≫ M.a = v₂ ≫ (p ∣_ V)) :
    M.transfer (M.transfer x v₂ h₂) (x ≫ (f ∣_ (p ⁻¹ᵁ V)))
      (by rw [M.transfer_q, Category.assoc, M.cartesian.w, Category.assoc]) = x := by
  apply M.cartesian.hom_ext <;> simp

end GenericModel

#print axioms GenericModel.transfer_self
#print axioms GenericModel.transfer_natural
#print axioms GenericModel.transfer_cocycle
#print axioms GenericModel.transfer_inverse

end ZInQ.Contrib.CloudR2NOS.GoodDescent
