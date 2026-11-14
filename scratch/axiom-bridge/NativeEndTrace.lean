import TateFreeness
import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.CharPoly
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.Trace

/-
UNCOMPILED CONSUMER DRAFT.

Transport the pinned Stacks rational endomorphism polynomial/trace to the actual
original PkgI3 homT and its scalar extension. The geometric point field and
endomorphism are the same on both sides. This does NOT prove the stronger
PkgI3.CharPolyIndepOfEll predicate, which requires an integer polynomial for all
fields, and does not construct C10's reduction/descent/Frobenius squares.

The CharPoly dependency is outside the currently frozen/published v2 cache
snapshot. No compiler or public-package addition is implied by this draft.
-/

noncomputable section

namespace AxiomBridge.NativeEndTrace

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory
open scoped MonObj

variable {k : Type} [Field k]

/-- Pull back the SAME original endomorphism along k → AlgebraicClosure k. -/
def geometricEnd (A : PkgI3.AbVar k) (φ : PkgI3.AbVar.End A) :
    (A.baseChange (AlgebraicClosure k)).X ⟶
      (A.baseChange (AlgebraicClosure k)).X :=
  (baseChangedHom A A φ).hom.hom

instance geometricEnd_isMonHom (A : PkgI3.AbVar k) (φ : PkgI3.AbVar.End A) :
    IsMonHom (geometricEnd A φ) :=
  (baseChangedHom A A φ).hom.isMonHom_hom

/-- The actual geometric endomorphism's pinned rational polynomial.
No choice of coefficient prime or Tate basis enters this definition. -/
def rationalCharPoly (A : PkgI3.AbVar k) (φ : PkgI3.AbVar.End A) : Polynomial ℚ := by
  letI := AxiomBridge.TateConsumer.geometric_isAbelianVariety A
  exact Stacks.Groupoids.endCharPoly
    (A.baseChange (AlgebraicClosure k)).X (geometricEnd A φ)

theorem rationalCharPoly_monic (A : PkgI3.AbVar k) (φ : PkgI3.AbVar.End A) :
    (rationalCharPoly A φ).Monic := by
  letI := AxiomBridge.TateConsumer.geometric_isAbelianVariety A
  exact Stacks.Groupoids.endCharPoly_monic
    (A.baseChange (AlgebraicClosure k)).X (geometricEnd A φ)

/-- One rational trace, independent of the coefficient prime. -/
def rationalTrace (A : PkgI3.AbVar k) (φ : PkgI3.AbVar.End A) : ℚ :=
  -(rationalCharPoly A φ).nextCoeff

/-- The existing genuine point-equivalence square, specialized to the same
endomorphism and written using the actual Stacks geometric Tate map. -/
theorem geometricEnd_natural (A : PkgI3.AbVar k) (φ : PkgI3.AbVar.End A)
    (ℓ : ℕ) [Fact ℓ.Prime] (x : A.T ℓ) :
    geometricTateEquiv A ℓ (PkgI3.AbVar.homT φ x) =
      Stacks.Groupoids.tateModuleMap ℓ (geometricEnd A φ)
        (geometricTateEquiv A ℓ x) := by
  apply AxiomBridge.TateComparison.ofPointEquiv_natural
  intro y
  exact congrArg Additive.ofMul
    (AxiomBridge.pointsBaseChangeMulEquiv_ptMap A (AlgebraicClosure k) φ y.toMul)

/-- The actual integral endomorphism maps are conjugate, not merely same-rank. -/
theorem conjugate_homT (A : PkgI3.AbVar k) (φ : PkgI3.AbVar.End A)
    (ℓ : ℕ) [Fact ℓ.Prime] :
    (geometricTateEquiv A ℓ).conj (PkgI3.AbVar.homT (ℓ := ℓ) φ) =
      Stacks.Groupoids.tateModuleMap ℓ (geometricEnd A φ) := by
  apply LinearMap.ext
  intro x
  change geometricTateEquiv A ℓ
      (PkgI3.AbVar.homT φ ((geometricTateEquiv A ℓ).symm x)) = _
  rw [geometricEnd_natural, LinearEquiv.apply_symm_apply]

/-- Rational-polynomial comparison in every actual finite rational-Tate basis.
The original T-free/finite and geometric hypotheses are constructed. -/
theorem charpoly_homT_baseChange (A : PkgI3.AbVar k) (φ : PkgI3.AbVar.End A)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : k) ≠ 0)
    {I : Type*} [Fintype I] [DecidableEq I]
    (b : Module.Basis I ℚ_[ℓ] (A.V ℓ)) :
    (LinearMap.toMatrix b b
      ((PkgI3.AbVar.homT (ℓ := ℓ) φ).baseChange ℚ_[ℓ])).charpoly =
        (rationalCharPoly A φ).map (algebraMap ℚ ℚ_[ℓ]) := by
  let B := A.baseChange (AlgebraicClosure k)
  letI := AxiomBridge.TateConsumer.geometric_isAbelianVariety A
  have hu := AxiomBridge.TateConsumer.prime_isUnit_on_geometric_field ℓ hℓ
  have hA := AxiomBridge.TateConsumer.tate_free_finite A ℓ hℓ
  letI := hA.1
  letI := hA.2
  letI := Module.Free.of_basis b
  letI := Module.Finite.of_basis b
  letI := Stacks.Groupoids.module_free_tateModule B.X ℓ hu
  letI := Stacks.Groupoids.module_finite_tateModule B.X ℓ hu
  rw [LinearMap.charpoly_toMatrix, LinearMap.charpoly_baseChange]
  have hc := (geometricTateEquiv A ℓ).charpoly_conj (PkgI3.AbVar.homT (ℓ := ℓ) φ)
  rw [conjugate_homT] at hc
  rw [← hc]
  change (LinearMap.charpoly (Stacks.Groupoids.tateModuleMap ℓ (geometricEnd A φ))).map
      PadicInt.Coe.ringHom =
    (Stacks.Groupoids.endCharPoly B.X (geometricEnd A φ)).map (algebraMap ℚ ℚ_[ℓ])
  exact Stacks.Groupoids.charpoly_tateModuleMap B.X ℓ (geometricEnd A φ) hu

/-- The rational trace belongs to the SAME original endomorphism's rational
Tate map for every allowed prime, without a characteristic-zero base restriction. -/
theorem trace_homT_baseChange (A : PkgI3.AbVar k) (φ : PkgI3.AbVar.End A)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : k) ≠ 0) :
    LinearMap.trace ℚ_[ℓ] (A.V ℓ)
      ((PkgI3.AbVar.homT (ℓ := ℓ) φ).baseChange ℚ_[ℓ]) =
        (rationalTrace A φ : ℚ_[ℓ]) := by
  let B := A.baseChange (AlgebraicClosure k)
  letI := AxiomBridge.TateConsumer.geometric_isAbelianVariety A
  have hu := AxiomBridge.TateConsumer.prime_isUnit_on_geometric_field ℓ hℓ
  have hA := AxiomBridge.TateConsumer.tate_free_finite A ℓ hℓ
  letI := hA.1
  letI := hA.2
  have ht : LinearMap.trace ℤ_[ℓ] (A.T ℓ) (PkgI3.AbVar.homT (ℓ := ℓ) φ) =
      LinearMap.trace ℤ_[ℓ] (Stacks.Groupoids.tateModule B.X ℓ)
        (Stacks.Groupoids.tateModuleMap ℓ (geometricEnd A φ)) := by
    rw [← conjugate_homT]
    exact (LinearMap.trace_conj' (PkgI3.AbVar.homT (ℓ := ℓ) φ)
      (geometricTateEquiv A ℓ)).symm
  rw [LinearMap.trace_baseChange, ht]
  change ((LinearMap.trace ℤ_[ℓ] (Stacks.Groupoids.tateModule B.X ℓ)
      (Stacks.Groupoids.tateModuleMap ℓ (geometricEnd A φ)) : ℤ_[ℓ]) : ℚ_[ℓ]) =
    (Stacks.Groupoids.abelianVarietyTrace B.X (geometricEnd A φ) : ℚ_[ℓ])
  exact Stacks.Groupoids.trace_tateModuleMap_eq_abelianVarietyTrace
    B.X ℓ (geometricEnd A φ) hu

/-- The same trace under the actual further coefficient-field scalar extension. -/
theorem trace_homT_scalar_extension (A : PkgI3.AbVar k) (φ : PkgI3.AbVar.End A)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : k) ≠ 0)
    (L : Type) [Field L] [CharZero L] [Algebra ℚ_[ℓ] L] :
    LinearMap.trace L (TensorProduct ℚ_[ℓ] L (A.V ℓ))
      (((PkgI3.AbVar.homT (ℓ := ℓ) φ).baseChange ℚ_[ℓ]).baseChange L) =
        (rationalTrace A φ : L) := by
  have hA := AxiomBridge.TateConsumer.tate_free_finite A ℓ hℓ
  letI := hA.1
  letI := hA.2
  let b := (Module.Free.chooseBasis ℤ_[ℓ] (A.T ℓ)).baseChange ℚ_[ℓ]
  letI := Module.Free.of_basis b
  letI := Module.Finite.of_basis b
  rw [LinearMap.trace_baseChange, trace_homT_baseChange A φ ℓ hℓ]
  simp only [map_ratCast]

/-- A concrete common-coefficient trace input: for one original endomorphism,
its traces at all allowed coefficient primes are images of ONE element of C.
C10's actual reduction/descent/projected-representation squares are still needed. -/
theorem exists_common_coefficient_trace (A : PkgI3.AbVar k)
    (φ : PkgI3.AbVar.End A) (C : Type) [Field C] [CharZero C] :
    ∃ c : C, ∀ (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : k) ≠ 0 →
      ∀ (L : Type) [Field L] [CharZero L] [Algebra ℚ_[ℓ] L] (j : C →+* L),
      LinearMap.trace L (TensorProduct ℚ_[ℓ] L (A.V ℓ))
        (((PkgI3.AbVar.homT (ℓ := ℓ) φ).baseChange ℚ_[ℓ]).baseChange L) = j c := by
  refine ⟨(rationalTrace A φ : C), ?_⟩
  intro ℓ _ hℓ L _ _ _ j
  simpa only [map_ratCast] using trace_homT_scalar_extension A φ ℓ hℓ L

end AxiomBridge.NativeEndTrace

#check AxiomBridge.NativeEndTrace.charpoly_homT_baseChange
#check AxiomBridge.NativeEndTrace.exists_common_coefficient_trace
#print axioms AxiomBridge.NativeEndTrace.geometricEnd_natural
#print axioms AxiomBridge.NativeEndTrace.conjugate_homT
#print axioms AxiomBridge.NativeEndTrace.charpoly_homT_baseChange
#print axioms AxiomBridge.NativeEndTrace.trace_homT_baseChange
#print axioms AxiomBridge.NativeEndTrace.exists_common_coefficient_trace
