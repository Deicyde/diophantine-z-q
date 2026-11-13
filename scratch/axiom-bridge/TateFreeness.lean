import AxiomBridge.AbelianVariety
import ComposedPointTateSmoke
import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.TateModule

/-
DRAFT — not compiled in the parent session.

This is the actual geometric consumer of the separately authored Points and
TateComparison sources. Unlike the generic transfer lemmas, it derives the
Stacks module properties from the actual base-changed abelian variety.
No rank/dimension, semisimplicity, Frobenius, C10 or H claim is made before checks.
-/

noncomputable section

namespace AxiomBridge.TateConsumer

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory
open scoped MonObj

variable {k : Type} [Field k]

/-- The original characteristic condition makes the same prime a unit in the
actual geometric point field, not an unrelated algebraically closed field. -/
theorem prime_isUnit_on_geometric_field (ℓ : ℕ) (hℓ : (ℓ : k) ≠ 0) :
    IsUnit (ℓ : AlgebraicClosure k) := by
  have hk : IsUnit (ℓ : k) := isUnit_iff_ne_zero.mpr hℓ
  simpa only [map_natCast] using hk.map (algebraMap k (AlgebraicClosure k))

/-- The actual base-change object carries the pinned Stacks abelian-variety
predicate through the unchanged Objects/PR53 bridge. -/
theorem geometric_isAbelianVariety (A : PkgI3.AbVar k) :
    AlgebraicGeometry.IsAbelianVariety (AlgebraicClosure k)
      (A.baseChange (AlgebraicClosure k)).X :=
  AxiomBridge.axiom_of_pkgI2
    (ObjBridge.toGrp (A.baseChange (AlgebraicClosure k))) inferInstance

/-- The original geometric Tate module is free and finite. The supplying
module is the Tate module of the actual pullback of A, and the equivalence is
constructed by the point adjunction; no desired Fact or caller module property
is introduced. -/
theorem tate_free_finite (A : PkgI3.AbVar k) (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : (ℓ : k) ≠ 0) :
    Module.Free ℤ_[ℓ] (A.T ℓ) ∧ Module.Finite ℤ_[ℓ] (A.T ℓ) := by
  let B := A.baseChange (AlgebraicClosure k)
  letI : AlgebraicGeometry.IsAbelianVariety (AlgebraicClosure k) B.X :=
    geometric_isAbelianVariety A
  have hu : IsUnit (ℓ : AlgebraicClosure k) := prime_isUnit_on_geometric_field ℓ hℓ
  let e := (AxiomBridge.pointsBaseChangeMulEquiv A (AlgebraicClosure k)).toAdditive
  constructor
  · exact AxiomBridge.TateComparison.free_ofPointEquiv ℓ e
      (Stacks.Groupoids.module_free_tateModule B.X ℓ hu)
  · exact AxiomBridge.TateComparison.finite_ofPointEquiv ℓ e
      (Stacks.Groupoids.module_finite_tateModule B.X ℓ hu)

/-- A genuine finite-space input for the abelian-variety side of C10. It does
not supply the modular representation, continuity, semisimplicity or traces. -/
theorem rational_tate_finite (A : PkgI3.AbVar k) (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : (ℓ : k) ≠ 0) : FiniteDimensional ℚ_[ℓ] (A.V ℓ) := by
  letI := (tate_free_finite A ℓ hℓ).1
  letI := (tate_free_finite A ℓ hℓ).2
  exact Module.Finite.of_basis
    ((Module.Free.chooseBasis ℤ_[ℓ] (A.T ℓ)).baseChange ℚ_[ℓ])

end AxiomBridge.TateConsumer

#print axioms AxiomBridge.TateConsumer.prime_isUnit_on_geometric_field
#print axioms AxiomBridge.TateConsumer.geometric_isAbelianVariety
#print axioms AxiomBridge.TateConsumer.tate_free_finite
#print axioms AxiomBridge.TateConsumer.rational_tate_finite
