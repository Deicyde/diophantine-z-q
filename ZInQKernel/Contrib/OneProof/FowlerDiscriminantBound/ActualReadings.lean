import ZInQKernel.Contrib.OneProof.FowlerDiscriminantBound.ActualOrder
import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.Global.Orders.Quadratic.Conductor

/-! The same-order form of Fowler, Proposition 2.7, from the three classical readings. -/

namespace HDec.CMBranch.FowlerArithmetic

open NumberField TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

/-- The unit index in Cox, Theorem 7.24: the units of the given order, included in
those of the ring of integers. -/
noncomputable def quadraticOrderUnitIndex (O : NumberFieldOrder K) : ℕ :=
  (Units.map O.toRingOfIntegers.val.toMonoidHom).range.index

/-- Oesterlé, Theorem 1 and §5.1, specialized to the field of the given order. -/
def OesterleFieldBound (K : Type*) [Field K] [NumberField K] : Prop :=
  (∏ p ∈ oesterlePrimes (NumberField.discr K), oesterleFactor p) *
    Real.log |(NumberField.discr K : ℝ)| ≤ 7000 * (classNumber K : ℝ)

/-- The consequence of genus theory in Cox, Theorem 6.1(iii), for the same field. -/
def FieldGenusDivisibility (K : Type*) [Field K] [NumberField K] : Prop :=
  2 ^ ((NumberField.discr K).natAbs.primeFactors.card - 1) ∣ classNumber K

/-- The portion of Cox, Theorem 7.24, needed for the bound. The local symbols only
enter via an upper bound by 1. The conductor equals the index for degree two. -/
def CoxConductorData (O : NumberFieldOrder K) : Prop :=
  quadraticOrderUnitIndex O ≤ 3 ∧
  (NumberField.discr K ≠ -3 → NumberField.discr K ≠ -4 → quadraticOrderUnitIndex O = 1) ∧
  ∃ s : ℕ → ℤ, (∀ p ∈ O.index.primeFactors, s p ≤ 1) ∧
    (Nat.card (Pic O) : ℝ) * (quadraticOrderUnitIndex O : ℝ) =
      (classNumber K : ℝ) * (O.index : ℝ) *
        ∏ p ∈ O.index.primeFactors, (1 - (s p : ℝ) / (p : ℝ))

/-- The actual conductor of the same order is its index times the maximal order. -/
theorem orderConductor_eq_index (O : NumberFieldOrder K) (hK : Module.finrank ℚ K = 2) :
    O.conductor = Ideal.span {(O.index : 𝓞 K)} :=
  O.conductor_eq_span_index hK

/-- Oesterlé's estimate and the genus divisibility on the same field give the
logarithmic inequality with its actual class number. -/
theorem field_log_bound_of_oesterle (ho : OesterleFieldBound K) (hg : FieldGenusDivisibility K) :
    Real.log |(NumberField.discr K : ℝ)| ≤ 42000 * (classNumber K : ℝ)^2 := by
  let D := NumberField.discr K
  let S := oesterlePrimes D
  let F := ∏ p ∈ S, oesterleFactor p
  by_cases hl : 0 ≤ Real.log |(D : ℝ)|
  · have hS : S.card = D.natAbs.primeFactors.card - 1 := by
      unfold S oesterlePrimes
      split
      · exact Finset.card_erase_of_mem (Finset.max'_mem _ _)
      · rename_i hS
        rw [Finset.not_nonempty_iff_eq_empty.mp hS]
        decide
    have hp (p : ℕ) (h : p ∈ S) : p.Prime := by
      unfold S oesterlePrimes at h
      split at h
      · exact Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase h)
      · exact (Finset.notMem_empty _ h).elim
    have hd : 2 ^ S.card ∣ classNumber K := by rw [hS]; exact hg
    have hh : (2 : ℝ)^S.card ≤ (classNumber K : ℝ) := by
      exact_mod_cast Nat.le_of_dvd (classNumber_pos K) hd
    have hF : (1 : ℝ)/6 ≤ (2 : ℝ)^S.card * F := oesterle_product_estimate S hp
    have hF0 : 0 ≤ F := by
      have hpow : (0 : ℝ) < (2 : ℝ)^S.card := by positivity
      exact nonneg_of_mul_nonneg_right (by linarith) hpow
    have hFH : (1 : ℝ)/6 ≤ (classNumber K : ℝ) * F :=
      hF.trans (mul_le_mul_of_nonneg_right hh hF0)
    have hO : F * Real.log |(D : ℝ)| ≤ 7000 * (classNumber K : ℝ) := ho
    calc
      Real.log |(D : ℝ)| = 6 * (Real.log |(D : ℝ)| * (1 / 6)) := by ring
      _ ≤ 6 * (Real.log |(D : ℝ)| * ((classNumber K : ℝ) * F)) := by gcongr
      _ = (6 * (classNumber K : ℝ)) * (F * Real.log |(D : ℝ)|) := by ring
      _ ≤ (6 * (classNumber K : ℝ)) * (7000 * (classNumber K : ℝ)) := by gcongr
      _ = 42000 * (classNumber K : ℝ)^2 := by ring
  · exact (le_of_not_ge hl).trans (by positivity)

/-- Fowler's bound for the Picard group of an actual imaginary quadratic order,
retaining only the field estimate, the genus divisibility, and Cox's order data. -/
theorem fowler_bound_of_order_readings [IsTotallyComplex K]
    (O : NumberFieldOrder K) (hK : Module.finrank ℚ K = 2)
    (ho : OesterleFieldBound K) (hg : FieldGenusDivisibility K) (hc : CoxConductorData O)
    (n : ℕ) (hn : 0 < n) (hh : Nat.card (Pic O) ≤ n) :
    Real.sqrt |(O.discr : ℝ)| ≤ 2 * (n : ℝ)^2 * Real.exp (21000 * (n : ℝ)^2) := by
  have hdim := NumberField.IsTotallyComplex.finrank (K := K)
  have hnc : InfinitePlace.nrComplexPlaces K = 1 := by rw [hK] at hdim; omega
  have hD := NumberField.sign_discr K
  rw [hnc] at hD
  norm_num at hD
  obtain ⟨hu, hu1, _, hs, heq⟩ := hc
  exact fowler_bound_of_pic hD (field_log_bound_of_oesterle ho hg) hu hu1
    (classNumber_mul_totient_le_pic_mul hs heq) hn hh

end HDec.CMBranch.FowlerArithmetic
