import ZInQKernel.Contrib.OneProof.RC.ModelLevels3.Y0LevelFinite
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.IsTensorProduct
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-! # The dimension bound over any field of the detector -/

namespace WeierstrassCurve.ModelLevels.Pinned

open ModelTorsion
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

private theorem integral_ringKrullDim_le (A D : Type*) [CommRing A] [CommRing D]
    [Algebra A D] [Algebra.IsIntegral A D] : ringKrullDim D ≤ ringKrullDim A := by
  apply Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap A D))
  intro p q hpq
  let : p.asIdeal.IsPrime := p.isPrime
  exact Ideal.IsIntegral.under_lt_under (R := A) (show p.asIdeal < q.asIdeal from hpq)

private theorem finite_polynomial_fibre_dimension {R B k : Type*} [CommRing R] [CommRing B]
    [Field k] [Algebra R B] [Algebra R k] (jB : Polynomial R →ₐ[R] B)
    (hfin : letI := jB.toRingHom.toAlgebra
      Module.Finite (Polynomial R) B) :
    ringKrullDim (k ⊗[R] B) ≤ 1 := by
  let P := Polynomial R
  letI : Algebra P B := jB.toRingHom.toAlgebra
  let : IsScalarTower R P B := IsScalarTower.of_algebraMap_eq fun r => (jB.commutes r).symm
  let : Module.Finite P B := hfin
  let A := k ⊗[R] P
  let C := A ⊗[P] B
  let e : C ≃ₐ[k] k ⊗[R] B :=
    Algebra.IsPushout.cancelBaseChangeAlg R k P A B
  let f : A ≃ₐ[k] Polynomial k :=
    (Algebra.TensorProduct.congr (.refl : k ≃ₐ[k] k) (MvPolynomial.uniqueAlgEquiv R Unit).symm).trans
      (MvPolynomial.scalarRTensorAlgEquiv.trans (MvPolynomial.uniqueAlgEquiv k Unit))
  let : Module.Finite A C := inferInstanceAs (Module.Finite A (A ⊗[P] B))
  calc
    ringKrullDim (k ⊗[R] B) = ringKrullDim C := ringKrullDim_eq_of_ringEquiv e.symm.toRingEquiv
    _ ≤ ringKrullDim A := integral_ringKrullDim_le A C
    _ = ringKrullDim (Polynomial k) := ringKrullDim_eq_of_ringEquiv f.toRingEquiv
    _ = 1 := by
      rw [Polynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add]

variable {ell N : ℕ} [Fact ell.Prime] [NeZero N] (h₅ : 5 ≤ ell)
  (htame : ¬ ell ∣ N * N.totient) (h₂ : 2 ≤ N)

set_option maxHeartbeats 600000 in
/-- Each field fibre, including the geometric closed and generic
fibres, has Krull dimension at most one. -/
theorem levelQuotient_fibre_dimension (k : Type*) [Field k] [Algebra (LocalIntegers ell) k] :
    ringKrullDim (k ⊗[LocalIntegers ell] Y0LevelAlgebra h₅ htame h₂) ≤ 1 :=
  finite_polynomial_fibre_dimension (R := LocalIntegers ell) (B := ↥(Y0LevelAlgebra h₅ htame h₂))
    (k := k) (Y0LevelJMap h₅ htame h₂) (Y0LevelJMap_finite h₅ htame h₂)

#print axioms integral_ringKrullDim_le
#print axioms finite_polynomial_fibre_dimension
#print axioms levelQuotient_fibre_dimension

end WeierstrassCurve.ModelLevels.Pinned
