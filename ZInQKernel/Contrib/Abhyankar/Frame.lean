import ZInQKernel.Contrib.Abhyankar.Field
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Canonical integral-closure tower maps

The scoped algebra structure is the restriction of the given field embedding.
Its scalar towers and integral-closure identity are proved. The scope is only
opened by the contribution; no baseline object or target definition is edited.
In particular, primes are restricted along this specified embedding, not along
an arbitrary presentation of the integral closure.
-/

namespace ZInQ.Contrib.Abhyankar.ClosureTower

noncomputable section

variable (R L M : Type*) [CommRing R] [Field L] [Field M]
  [Algebra R L] [Algebra L M] [Algebra R M] [IsScalarTower R L M]

/-- Restriction of the given field embedding to the actual integral closures. -/
def map : integralClosure R L →ₐ[R] integralClosure R M :=
  (IsScalarTower.toAlgHom R L M).mapIntegralClosure

/-- The map is the original field embedding on underlying elements. -/
@[simp]
theorem coe_map (s : integralClosure R L) :
    (map R L M s : M) = algebraMap L M (s : L) := rfl

/-- The integral-closure tower uses the map just defined. -/
scoped instance (priority := 100) algebra : Algebra (integralClosure R L) (integralClosure R M) :=
  (map R L M).toRingHom.toAlgebra

open scoped ZInQ.Contrib.Abhyankar.ClosureTower

/-- The tower map preserves the original `R`-algebra structures. -/
scoped instance towerBase : IsScalarTower R (integralClosure R L) (integralClosure R M) :=
  IsScalarTower.of_algHom (map R L M)

/-- The tower map composes to the given embedding into `M`. -/
scoped instance towerField : IsScalarTower (integralClosure R L) (integralClosure R M) M :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

/-- Integrality over the first closure is equivalent to integrality over `R`,
so the second actual closure is also the closure over the first one. -/
scoped instance isIntegralClosure :
    IsIntegralClosure (integralClosure R M) (integralClosure R L) M :=
  IsIntegralClosure.tower_top (R := R)

/-- The closure of the closure is canonically the actual original closure,
with its specified integral-closure-tower algebra structure. -/
def equiv : integralClosure (integralClosure R L) M ≃ₐ[integralClosure R L] integralClosure R M :=
  IsIntegralClosure.equiv (integralClosure R L) (integralClosure (integralClosure R L) M)
    M (integralClosure R M)

/-- The canonical comparison is compatible with the original coefficient ring. -/
def equivBase : integralClosure (integralClosure R L) M ≃ₐ[R] integralClosure R M :=
  (equiv R L M).restrictScalars R

/-- The comparison does not change the element of the ambient field. -/
@[simp]
theorem coe_equiv (s : integralClosure (integralClosure R L) M) :
    (equiv R L M s : M) = (s : M) := by
  exact IsIntegralClosure.algebraMap_equiv (integralClosure R L)
    (integralClosure (integralClosure R L) M) M (integralClosure R M) s

/-- Restriction along the canonical tower map preserves prime ideals and the
full lying-over condition at the original base maximal ideal. -/
theorem prime_under [IsLocalRing R]
    (Q : Ideal (integralClosure R M)) [Q.IsPrime] [Q.LiesOver (IsLocalRing.maximalIdeal R)] :
    (Q.under (integralClosure R L)).IsPrime ∧
      (Q.under (integralClosure R L)).LiesOver (IsLocalRing.maximalIdeal R) := by
  exact ⟨Ideal.IsPrime.under _ Q,
    Ideal.LiesOver.tower_bot Q (Q.under (integralClosure R L)) (IsLocalRing.maximalIdeal R)⟩

end

end ZInQ.Contrib.Abhyankar.ClosureTower
