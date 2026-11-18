import ValuationResidueCharacteristicCoherent
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.Tactic

/-!
# The residue characteristic of an actual number-field DVR

An actual nonzero nonunit is algebraic over the integers. Its integral
polynomial relation has nonzero constant coefficient; reducing the
relation gives a nonzero integer killed in the actual residue field.
Thus the actual residue characteristic is positive and prime.
-/

noncomputable section
set_option autoImplicit false

namespace ValuationResidueCharacteristic

variable {K : Type*} [Field K] [NumberField K]

theorem numberField_residue_prime (O : ValuationSubring K) [IsDiscreteValuationRing O] :
    ∃ p : ℕ, p.Prime ∧ CharP (IsLocalRing.ResidueField O) p := by
  obtain ⟨pi, hpi⟩ := IsDiscreteValuationRing.exists_irreducible (R := O)
  have hpiK : (pi : K) ≠ 0 := fun h => hpi.ne_zero (Subtype.ext h)
  haveI : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
  have halg : IsAlgebraic ℤ (pi : K) := (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (pi : K)).restrictScalars ℤ
  obtain ⟨q, hq0, hqK⟩ := halg.exists_nonzero_coeff_and_aeval_eq_zero
    (mem_nonZeroDivisors_iff_ne_zero.mpr hpiK)
  have hqO : Polynomial.aeval pi q = 0 := by
    apply (show Function.Injective O.subtype.toIntAlgHom from Subtype.coe_injective)
    rw [← Polynomial.aeval_algHom_apply, map_zero]
    exact hqK
  have hpiMax : pi ∈ IsLocalRing.maximalIdeal O := by
    rw [hpi.maximalIdeal_eq]
    exact Ideal.mem_span_singleton_self pi
  have hpiRes : IsLocalRing.residue O pi = 0 := (IsLocalRing.residue_eq_zero_iff pi).mpr hpiMax
  have hqRes : Polynomial.aeval (IsLocalRing.residue O pi) q = 0 := by
    change Polynomial.aeval ((IsLocalRing.residue O).toIntAlgHom pi) q = 0
    rw [Polynomial.aeval_algHom_apply, hqO, map_zero]
  have hconstant : (q.coeff 0 : IsLocalRing.ResidueField O) = 0 := by
    change algebraMap ℤ (IsLocalRing.ResidueField O) (q.coeff 0) = 0
    rw [Polynomial.coeff_zero_eq_aeval_zero']
    simpa only [hpiRes] using hqRes
  have hp0 : ringChar (IsLocalRing.ResidueField O) ≠ 0 := by
    intro h
    haveI : CharP (IsLocalRing.ResidueField O) 0 := by rw [← h]; infer_instance
    have hz := (CharP.intCast_eq_zero_iff (IsLocalRing.ResidueField O) 0 (q.coeff 0)).mp hconstant
    exact hq0 (by simpa using hz)
  exact ⟨ringChar (IsLocalRing.ResidueField O),
    CharP.char_prime_of_ne_zero (IsLocalRing.ResidueField O) hp0, inferInstance⟩

#check numberField_residue_prime
#print axioms numberField_residue_prime

end ValuationResidueCharacteristic
