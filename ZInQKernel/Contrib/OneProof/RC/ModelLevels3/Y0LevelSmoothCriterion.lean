import ZInQKernel.Contrib.OneProof.RC.ModelLevels3.Y0LevelFibreDimension
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.RingTheory.Smooth.RegularLocalRing
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.Etale.Descent
import Mathlib.RingTheory.Smooth.Fiber

/-! # The geometric fibre criterion for the pinned model -/

namespace WeierstrassCurve.ModelLevels.Pinned

open ModelTorsion
open scoped TensorProduct

private theorem smooth_of_geometric_regular {R B : Type} [CommRing R] [CommRing B]
    [Algebra R B] [Module.Flat R B] [Algebra.FinitePresentation R B]
    (hreg : ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra R k],
      ∀ (q : Ideal (k ⊗[R] B)) [q.IsPrime], IsRegularLocalRing (Localization.AtPrime q)) :
    Algebra.Smooth R B := by
  apply Algebra.Smooth.of_formallySmooth_fiber
  intro p hp
  let K := p.ResidueField
  let L := AlgebraicClosure K
  let e : L ⊗[K] (K ⊗[R] B) ≃ₐ[L] L ⊗[R] B :=
    Algebra.TensorProduct.cancelBaseChange R K L L B
  let : Algebra.FiniteType L (L ⊗[R] B) := Algebra.FiniteType.baseChange L
  let : Algebra.Smooth L (L ⊗[R] B) :=
    Algebra.Smooth.of_isRegularLocalRing (hreg L)
  let : Algebra.Smooth L (L ⊗[K] (K ⊗[R] B)) := Algebra.Smooth.of_equiv e.symm
  exact (Algebra.Smooth.of_smooth_tensorProduct_of_faithfullyFlat (R := K) L).formallySmooth

private theorem regularLocal_of_normal_stalk {A : Type*} [CommRing A] [IsNoetherianRing A]
    (q : Ideal A) [q.IsPrime] (hd : ringKrullDim A ≤ 1)
    [IsDomain (Localization.AtPrime q)] [IsIntegrallyClosed (Localization.AtPrime q)] :
    IsRegularLocalRing (Localization.AtPrime q) := by
  let D := Localization.AtPrime q
  have hd' : ringKrullDim D ≤ 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height q D]
    exact Ideal.height_le_ringKrullDim_of_isPrime.trans hd
  let : Ring.KrullDimLE 1 D := Ring.krullDimLE_iff.mpr hd'
  let : Ring.DimensionLEOne D :=
    ⟨Ring.krullDimLE_one_iff_of_noZeroDivisors.mp inferInstance _⟩
  let : IsDedekindRing D := ⟨⟩
  let : IsDedekindDomain D := ⟨⟩
  exact IsRegularLocalRing.of_isRegularRing_of_isLocalRing D

variable {ell N : ℕ} [Fact ell.Prime] [NeZero N] (h₅ : 5 ≤ ell)
  (htame : ¬ ell ∣ N * N.totient) (h₂ : 2 ≤ N)

/-- Regularity of the local rings on the algebraically closed fibres
suffices for smoothness of the pinned coordinate algebra. -/
theorem levelQuotient_smooth_of_geometric_regular
    (hreg : ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra (LocalIntegers ell) k],
      ∀ (q : Ideal (k ⊗[LocalIntegers ell] Y0LevelAlgebra h₅ htame h₂)) [q.IsPrime],
        IsRegularLocalRing (Localization.AtPrime q)) :
    Algebra.Smooth (LocalIntegers ell) (Y0LevelAlgebra h₅ htame h₂) := by
  let := levelQuotient_flat h₅ htame h₂
  let := levelQuotient_finitePresentation h₅ htame h₂
  exact smooth_of_geometric_regular hreg

/-- Normality of the local rings on the algebraically closed fibres
suffices for smoothness of the pinned coordinate algebra. -/
theorem levelQuotient_smooth_of_geometric_normal
    (hnormal : ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra (LocalIntegers ell) k],
      ∀ (q : Ideal (k ⊗[LocalIntegers ell] Y0LevelAlgebra h₅ htame h₂)) [q.IsPrime],
        IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q)) :
    Algebra.Smooth (LocalIntegers ell) (Y0LevelAlgebra h₅ htame h₂) := by
  apply levelQuotient_smooth_of_geometric_regular h₅ htame h₂
  intro k _ _ _ q _
  let : Algebra.FiniteType (LocalIntegers ell) (Y0LevelAlgebra h₅ htame h₂) :=
    levelQuotient_finiteType h₅ htame h₂
  let := Algebra.FiniteType.baseChange (R := LocalIntegers ell) (A := ↥(Y0LevelAlgebra h₅ htame h₂)) k
  let : IsNoetherianRing (k ⊗[LocalIntegers ell] Y0LevelAlgebra h₅ htame h₂) :=
    Algebra.FiniteType.isNoetherianRing k _
  let := (hnormal k q).1
  let := (hnormal k q).2
  exact regularLocal_of_normal_stalk q (levelQuotient_fibre_dimension h₅ htame h₂ k)

#print axioms smooth_of_geometric_regular
#print axioms regularLocal_of_normal_stalk
#print axioms levelQuotient_smooth_of_geometric_regular
#print axioms levelQuotient_smooth_of_geometric_normal

end WeierstrassCurve.ModelLevels.Pinned
