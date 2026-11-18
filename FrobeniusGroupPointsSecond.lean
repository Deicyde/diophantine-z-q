import FrobeniusSchemeFixedThird

/-!
# Native residue automorphisms and the finite fixed-point group

A genuine ring automorphism with the finite-base-field Frobenius law fixes
the base field by its own finite-field power identity. Thus it is an actual
base-algebra automorphism, not a substituted representation. Its fixed
geometric scheme points form the actual fixed subgroup of the point group.
The group's finiteness is proved by the fixed-field and Spec-descent theorem.
-/

noncomputable section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace SemistableGeometry.FrobeniusFixed

variable {k L : Type} [Field k] [Field L] [Algebra k L]

/-- A native ring Frobenius fixes the finite base field and hence has the genuine algebra-automorphism type. -/
def ofRingFrobenius [Finite k] (τ : L ≃+* L)
    (hτ : ∀ a : L, τ a = a ^ Nat.card k) : L ≃ₐ[k] L where
  __ := τ
  commutes' a := by
    have ha : a ^ Nat.card k = a := by
      let : Fintype k := Fintype.ofFinite k
      simpa only [Nat.card_eq_fintype_card] using FiniteField.pow_card a
    change τ (algebraMap k L a) = algebraMap k L a
    rw [hτ, ← map_pow, ha]

/-- The algebra-automorphism power is the exact native ring-automorphism power. -/
theorem ofRingFrobenius_pow_apply [Finite k] (τ : L ≃+* L)
    (hτ : ∀ a : L, τ a = a ^ Nat.card k) (r : ℕ) (a : L) :
    (ofRingFrobenius τ hτ ^ r) a = (τ ^ r) a := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simp only [pow_succ', AlgEquiv.mul_apply]
    change τ ((ofRingFrobenius τ hτ ^ r) a) = τ ((τ ^ r) a)
    exact congrArg τ ih

/-- Actual precomposition by the indicated geometric field action is a homomorphism of point groups. -/
def pointActionHom (σ : L ≃ₐ[k] L) (r : ℕ)
    (X : Over (Spec (CommRingCat.of k))) [GrpObj X] :
    (pointDomain (k := k) (L := L) ⟶ X) →* (pointDomain (k := k) (L := L) ⟶ X) where
  toFun x := algebraPointMap (σ ^ r).toAlgHom ≫ x
  map_one' := MonObj.comp_one _
  map_mul' x y := MonObj.comp_mul _ _ _

/-- The actual fixed subgroup of the geometric point group. -/
def fixedPointSubgroup (σ : L ≃ₐ[k] L) (r : ℕ)
    (X : Over (Spec (CommRingCat.of k))) [GrpObj X] :
    Subgroup (pointDomain (k := k) (L := L) ⟶ X) where
  carrier := {x | algebraPointMap (σ ^ r).toAlgHom ≫ x = x}
  one_mem' := MonObj.comp_one _
  mul_mem' {x y} hx hy := by
    change algebraPointMap (σ ^ r).toAlgHom ≫ x = x at hx
    change algebraPointMap (σ ^ r).toAlgHom ≫ y = y at hy
    change algebraPointMap (σ ^ r).toAlgHom ≫ (x * y) = x * y
    rw [MonObj.comp_mul, hx, hy]
  inv_mem' {x} hx := by
    change pointActionHom σ r X x = x at hx
    change pointActionHom σ r X (x⁻¹) = x⁻¹
    rw [map_inv, hx]

/-- The finite fixed geometric-point set is the finite actual fixed point subgroup. -/
theorem finite_fixedPointSubgroup (σ : L ≃ₐ[k] L) (q : ℕ) (hq : 2 ≤ q)
    (hσ : ∀ a : L, σ a = a ^ q) (r : ℕ) (hr : 0 < r)
    (X : Over (Spec (CommRingCat.of k))) [GrpObj X]
    [LocallyOfFiniteType X.hom] [CompactSpace X.left] :
    Finite (fixedPointSubgroup σ r X) := by
  change Finite (fixedPoints σ r X)
  exact finite_fixedPoints σ q hq hσ r hr X

/-- A native residue Frobenius over a finite base field gives the finite actual fixed point group. -/
theorem finite_ringFrobenius_fixedPointSubgroup [Finite k] (τ : L ≃+* L)
    (hτ : ∀ a : L, τ a = a ^ Nat.card k) (r : ℕ) (hr : 0 < r)
    (X : Over (Spec (CommRingCat.of k))) [GrpObj X]
    [LocallyOfFiniteType X.hom] [CompactSpace X.left] :
    Finite (fixedPointSubgroup (ofRingFrobenius τ hτ) r X) := by
  exact finite_fixedPointSubgroup (ofRingFrobenius τ hτ) (Nat.card k)
    Finite.one_lt_card hτ r hr X

end SemistableGeometry.FrobeniusFixed
