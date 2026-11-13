import ZInQKernel.HDecomp.Objects
import ZInQKernel.Contrib.Abhyankar.Field
import ZInQKernel.Contrib.Abhyankar.Transport

/-!
# The exact exponent-one case of the baseline DVR statement

`AbhyankarDVRAt n` only fixes the exponent in the unchanged baseline statement.
`baseline_iff_all_exponents` checks the complete type comparison. The closed
proof `atExponent_one` proves this restricted case for all the baseline rings,
fields, scalar towers, and integral-closure primes. It is not a proof provider
for the general baseline proposition.
-/

namespace ZInQ.Contrib.Abhyankar

open IsLocalRing

/-- The exact baseline assertion with its exponent fixed, in universe zero. -/
def AbhyankarDVRAt (n : ℕ) : Prop :=
  ∀ (R K L M : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Field M] [Algebra L M] [Algebra K M] [Algebra R M]
    [IsScalarTower K L M] [IsScalarTower R K M]
    (π : R), Irreducible π → 0 < n → IsUnit (n : R) →
    (∀ (Q : Ideal (integralClosure R L)) [Q.IsPrime] [Q.LiesOver (maximalIdeal R)],
      IsUnit ((Q.ramificationIdx R : ℕ) : R) ∧ Q.ramificationIdx R ∣ n ∧
      Algebra.IsSeparable (R ⧸ maximalIdeal R) (integralClosure R L ⧸ Q)) →
    ∀ t : M, t ^ n = algebraMap R M π → IntermediateField.adjoin L {t} = ⊤ →
      ∀ (Q : Ideal (integralClosure R M)) [Q.IsPrime] [Q.LiesOver (maximalIdeal R)],
        Q.ramificationIdx R = n ∧
        Algebra.IsSeparable (R ⧸ maximalIdeal R) (integralClosure R M ⧸ Q)

/-- This is a type comparison, not a discharge of the general baseline proposition. -/
theorem baseline_iff_all_exponents :
    PkgI2.AbhyankarDVR.{0} ↔ ∀ n, AbhyankarDVRAt n := by
  unfold PkgI2.AbhyankarDVR AbhyankarDVRAt
  constructor
  · intro h n R K L M instR domR dvrR instK algRK fracRK instL algKL algRL towerRKL
      finKL sepKL instM algLM algKM algRM towerKLM towerRKM π hπ
    exact h R K L M π hπ n
  · intro h R K L M instR domR dvrR instK algRK fracRK instL algKL algRL towerRKL
      finKL sepKL instM algLM algKM algRM towerKLM towerRKM π hπ n
    exact h n R K L M π hπ

/-- **Closed, exact exponent-one case.** The root lies in the given image of `L`,
so `M/L` is an actual algebra equivalence. Pullback covers every target prime,
and transports the residue algebra rather than assuming that `L = M`. -/
theorem atExponent_one : AbhyankarDVRAt 1 := by
  intro R K L M instR domR dvrR instK algRK fracRK instL algKL algRL towerRKL
    finKL sepKL instM algLM algKM algRM towerKLM towerRKM π hπ hn hu htame
    t ht hadjoin Q hQprime hQover
  have : IsScalarTower R L M := scalarTower_right (K := K)
  have htL : t ∈ Set.range (algebraMap L M) := by
    refine ⟨algebraMap R L π, ?_⟩
    simpa only [pow_one, IsScalarTower.algebraMap_apply R L M] using ht.symm
  let eLM : L ≃ₐ[L] M := AlgEquiv.ofBijective (Algebra.ofId L M)
    ⟨(algebraMap L M).injective, algebraMap_surjective_of_adjoin_eq_top htL hadjoin⟩
  let e : integralClosure R L ≃ₐ[R] integralClosure R M :=
    (eLM.restrictScalars R).mapIntegralClosure
  refine allPrimeData_of_algEquiv (maximalIdeal R) e ?_ Q
  intro P hPprime hPover
  obtain ⟨_, hdvd, hsep⟩ := htame P
  exact ⟨Nat.dvd_one.mp hdvd, hsep⟩

end ZInQ.Contrib.Abhyankar
