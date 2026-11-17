import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.DivisionEisensteinTraceInvariance

/-!
# Lower Eisenstein trace closure when the new prime divides the level

For a prime p dividing N, the actual trace from pN to N sends every arbitrary
series generator into the lower series span. Primitive rows are moved to every
point of the complete fibre by genuine principal matrices; nonprimitive rows
reduce by actual label scaling. No complete-fibre orbit assumption is an input.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open UpperHalfPlane Matrix CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped BigOperators Matrix MatrixGroups ModularForm

namespace ZInQ.Contrib.HeckePrimeRationality.DivisionEisensteinLowerClosure

open EisensteinWeightTwo DivisionEisensteinLevelMaps

set_option quotPrecheck false in
local notation "ΓP" N => (CongruenceSubgroup.Gamma N).map (mapGL ℝ)

/-- The actual trace of a primitive-row generator equals that of every point
in its complete fibre. This follows from constructed integral group moves. -/
theorem normalizedTrace_fiber_point (p N : ℕ) [Fact p.Prime] (hN : 0 < N) (hpN : p ∣ N)
    (a b : ℤ) (hab : (a : ZMod p) ≠ 0 ∨ (b : ZMod p) ≠ 0) (r s : Fin p) :
    normalizedTrace N (p * N) (Nat.mul_pos (Fact.out : p.Prime).pos hN)
      (divisionEisensteinMF (p * N) (Nat.mul_pos (Fact.out : p.Prime).pos hN)
        ![a + (N : ℤ) * (r : ℕ),b + (N : ℤ) * (s : ℕ)]) =
    normalizedTrace N (p * N) (Nat.mul_pos (Fact.out : p.Prime).pos hN)
      (divisionEisensteinMF (p * N) (Nat.mul_pos (Fact.out : p.Prime).pos hN) ![a,b]) := by
  obtain ⟨γ, hγ, h0, h1⟩ := exists_Gamma_prime_fiber_move p N hpN a b (r : ℕ) (s : ℕ) hab
  have hv : ![(![a,b] ᵥ* γ.1) 0,(![a,b] ᵥ* γ.1) 1] = (![a,b] ᵥ* γ.1) := by
    ext i; fin_cases i <;> rfl
  have he := divisionMF_eq_of_congr (p * N) (Nat.mul_pos (Fact.out : p.Prime).pos hN)
    _ _ (a + (N : ℤ) * (r : ℕ)) (b + (N : ℤ) * (s : ℕ)) h0 h1
  rw [hv] at he
  rw [← he]
  exact normalizedTrace_generator_SL N (p * N) (Nat.mul_pos (Fact.out : p.Prime).pos hN) ![a,b] γ hγ

/-- For a primitive row modulo the repeated prime, the trace is the actual
lower series generator at the same integer label. -/
theorem normalizedTrace_primitive_repeated_prime (p N : ℕ) [Fact p.Prime]
    (hN : 0 < N) (hpN : p ∣ N) (a b : ℤ)
    (hab : (a : ZMod p) ≠ 0 ∨ (b : ZMod p) ≠ 0) :
    normalizedTrace N (p * N) (Nat.mul_pos (Fact.out : p.Prime).pos hN)
      (divisionEisensteinMF (p * N) (Nat.mul_pos (Fact.out : p.Prime).pos hN) ![a,b]) =
      divisionEisensteinMF N hN ![a,b] := by
  classical
  have hp : 0 < p := (Fact.out : p.Prime).pos
  let T := normalizedTrace N (p * N) (Nat.mul_pos hp hN)
  let F := divisionEisensteinMF (p * N) (Nat.mul_pos hp hN) ![a,b]
  have hsum : T (completeFiber p N hp hN a b) = (p : ℂ) ^ 2 • T F := by
    simp only [T, F, completeFiber, map_sum, normalizedTrace_fiber_point p N hN hpN a b hab,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    simp only [pow_two, ← Nat.cast_mul, Nat.cast_smul_eq_nsmul, mul_nsmul]
  have he : (p : ℂ) ^ 2 • divisionEisensteinMF N hN ![a,b] = (p : ℂ) ^ 2 • T F := by
    rw [← normalizedTrace_completeFiber p N hp hN a b]
    exact hsum
  have hp2 : (p : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 (Nat.cast_ne_zero.mpr hp.ne')
  have he' := congrArg (fun f : _root_.ModularForm (ΓP N) 2 => ((p : ℂ) ^ 2)⁻¹ • f) he
  simp only [smul_smul, inv_mul_cancel₀ hp2, one_smul] at he'
  exact he'.symm

/-- Every arbitrary integer upper label has lower series-span trace closure
for a prime extension whose prime divides the lower level. -/
theorem arbitrary_generator_trace_repeated_prime_mem (p N : ℕ) [Fact p.Prime]
    (hN : 0 < N) (hpN : p ∣ N) (a : Fin 2 → ℤ) :
    normalizedTrace N (p * N) (Nat.mul_pos (Fact.out : p.Prime).pos hN)
      (divisionEisensteinMF (p * N) (Nat.mul_pos (Fact.out : p.Prime).pos hN) a) ∈ seriesSpan N hN := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hv : ![a 0,a 1] = a := by ext i; fin_cases i <;> rfl
  by_cases hz : (a 0 : ZMod p) = 0 ∧ (a 1 : ZMod p) = 0
  · obtain ⟨c, hc⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (a 0) p).mp hz.1
    obtain ⟨d, hd⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (a 1) p).mp hz.2
    rw [← hv, hc, hd, series_scaled_label p N hp hN c d,
      normalizedTrace_restriction (Nat.mul_pos hp hN) (dvd_mul_left N p)]
    exact generator_mem_seriesSpan N hN ![c,d]
  · have hab : (a 0 : ZMod p) ≠ 0 ∨ (a 1 : ZMod p) ≠ 0 := by tauto
    rw [← hv, normalizedTrace_primitive_repeated_prime p N hN hpN (a 0) (a 1) hab]
    exact generator_mem_seriesSpan N hN ![a 0,a 1]

/-- Lower trace closure for every upper series-span member in a repeated-prime extension. -/
theorem trace_seriesSpan_repeated_prime (p N : ℕ) [Fact p.Prime]
    (hN : 0 < N) (hpN : p ∣ N)
    {f : _root_.ModularForm (ΓP (p * N)) 2}
    (hf : f ∈ seriesSpan (p * N) (Nat.mul_pos (Fact.out : p.Prime).pos hN)) :
    normalizedTrace N (p * N) (Nat.mul_pos (Fact.out : p.Prime).pos hN) f ∈ seriesSpan N hN := by
  have hle : seriesSpan (p * N) (Nat.mul_pos (Fact.out : p.Prime).pos hN) ≤
      (seriesSpan N hN).comap (normalizedTrace N (p * N) (Nat.mul_pos (Fact.out : p.Prime).pos hN)) := by
    apply Submodule.span_le.mpr
    rintro f ⟨a, rfl⟩
    exact arbitrary_generator_trace_repeated_prime_mem p N hN hpN a
  exact hle hf

/-- Genuine invariant series-span descent in a repeated-prime extension. -/
theorem invariant_series_descent_repeated_prime (p N : ℕ) [Fact p.Prime]
    (hN : 0 < N) (hpN : p ∣ N)
    (f : _root_.ModularForm (ΓP (p * N)) 2)
    (hf : f ∈ seriesSpan (p * N) (Nat.mul_pos (Fact.out : p.Prime).pos hN))
    (hinv : ∀ γ ∈ (ΓP N), ⇑f ∣[(2 : ℤ)] γ = ⇑f) :
    ∃ g : _root_.ModularForm (ΓP N) 2, g ∈ seriesSpan N hN ∧
      restriction N (p * N) (dvd_mul_left N p) g = f := by
  exact ⟨normalizedTrace N (p * N) (Nat.mul_pos (Fact.out : p.Prime).pos hN) f,
    trace_seriesSpan_repeated_prime p N hN hpN hf,
    restriction_normalizedTrace_of_invariant hN (Nat.mul_pos (Fact.out : p.Prime).pos hN)
      (dvd_mul_left N p) f hinv⟩

end ZInQ.Contrib.HeckePrimeRationality.DivisionEisensteinLowerClosure
