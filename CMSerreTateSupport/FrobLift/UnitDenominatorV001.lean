import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Unit denominators for roots in a valuation ring

Let `B → E` be a ring map into a field whose image is integrally closed in `E`, and let `w` be a
valuation subring of `E` containing that image. If `x ∈ w` is a root of a polynomial over `B` one of
whose coefficients is a `w`-unit, then `s * x = a` with `s, a` coming from `B` and `s` a `w`-unit.

Classical argument: for `g = ∑ bᵢ Xⁱ` with `g(x) = 0`, the tails `∑_{i ≥ k} bᵢ x^{i-k+1}` (`k ≥ 1`)
are integral, by descending induction using the leading-coefficient lemma; take `j` maximal with
`bⱼ` a unit and `s = ∑_{i ≥ j} bᵢ x^{i-j}`.
-/

noncomputable section

namespace FrobLift

open Polynomial

variable {B E : Type*} [CommRing B] [Field E] [Algebra B E]

/-- The tail sum `∑_{k ≤ i ≤ n} bᵢ x^{i-k+1}`. -/
def tail (b : ℕ → E) (x : E) (n k : ℕ) : E :=
  ∑ i ∈ Finset.Ico k (n + 1), b i * x ^ (i - k + 1)

theorem tail_eq (b : ℕ → E) (x : E) {n k : ℕ} (hk : k ≤ n) :
    tail b x n k = (b k + tail b x n (k + 1)) * x := by
  unfold tail
  rw [Finset.sum_eq_sum_Ico_succ_bot (by omega), add_mul, Finset.sum_mul]
  congr 1
  · simp
  · apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_Ico] at hi
    rw [mul_assoc, ← pow_succ]
    congr 2
    omega

theorem eval_split (b : ℕ → E) (x : E) {n k : ℕ} (hk : k ≤ n) :
    (b k + tail b x n (k + 1)) * x ^ k + ∑ i ∈ Finset.range k, b i * x ^ i =
      ∑ i ∈ Finset.range (n + 1), b i * x ^ i := by
  rw [← Finset.sum_range_add_sum_Ico _ (show k ≤ n + 1 by omega), add_comm]
  congr 1
  rw [Finset.sum_eq_sum_Ico_succ_bot (by omega), add_mul]
  congr 1
  unfold tail
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_Ico] at hi
  rw [mul_assoc, ← pow_add]
  congr 2
  omega

theorem tail_top (b : ℕ → E) (x : E) (n : ℕ) : tail b x n (n + 1) = 0 := by
  simp [tail]

/-- **Unit denominators.** -/
theorem exists_unit_denominator (w : ValuationSubring E)
    (hB : ∀ z : E, IsIntegral B z → z ∈ (algebraMap B E).range)
    (hBw : ∀ b : B, algebraMap B E b ∈ w)
    (g : B[X]) {x : E} (hx : x ∈ w) (hg : aeval x g = 0)
    (hunit : ∃ i, w.valuation (algebraMap B E (g.coeff i)) = 1) :
    ∃ s a : B, w.valuation (algebraMap B E s) = 1 ∧ algebraMap B E s * x = algebraMap B E a := by
  classical
  set n := g.natDegree with hn
  set b : ℕ → E := fun i => algebraMap B E (g.coeff i) with hb
  have hsum : ∑ i ∈ Finset.range (n + 1), b i * x ^ i = 0 := by
    rw [aeval_eq_sum_range] at hg
    simpa [hb, Algebra.smul_def] using hg
  have hxv : w.valuation x ≤ 1 := (ValuationSubring.valuation_le_one_iff w x).2 hx
  -- integrality of the tails, by descending induction
  have htail : ∀ d k, k + d = n + 1 → 1 ≤ k → tail b x n k ∈ (algebraMap B E).range := by
    intro d
    induction d with
    | zero =>
      intro k hk _
      have : k = n + 1 := by omega
      subst this
      rw [tail_top]
      exact ⟨0, map_zero _⟩
    | succ d ih =>
      intro k hk hk1
      obtain ⟨u, hu⟩ := ih (k + 1) (by omega) (by omega)
      set c : B := g.coeff k + u with hcdef
      have hc : algebraMap B E c = b k + tail b x n (k + 1) := by
        simp [hcdef, hu, hb]
      set h : B[X] := (∑ i ∈ Finset.range k, C (g.coeff i) * X ^ i) + C c * X ^ k with hhdef
      have hh : aeval x h = 0 := by
        have e : aeval x h = algebraMap B E c * x ^ k + ∑ i ∈ Finset.range k, b i * x ^ i := by
          simp [hhdef, hb, add_comm]
        rw [e, hc, eval_split b x (by omega : k ≤ n)]
        exact hsum
      by_cases hc0 : c = 0
      · refine ⟨0, ?_⟩
        rw [tail_eq b x (by omega : k ≤ n), ← hc, hc0]
        simp
      · have hdeg : (∑ i ∈ Finset.range k, C (g.coeff i) * X ^ i).degree <
            (C c * X ^ k).degree := by
          rw [degree_C_mul_X_pow k hc0, degree_lt_iff_coeff_zero]
          intro m hm
          rw [finset_sum_coeff]
          apply Finset.sum_eq_zero
          intro i hi
          rw [coeff_C_mul_X_pow, if_neg]
          have := Finset.mem_range.mp hi
          omega
        have hlc : h.leadingCoeff = c := by
          rw [hhdef, leadingCoeff_add_of_degree_lt hdeg, leadingCoeff_C_mul_X_pow]
        have hint := isIntegral_leadingCoeff_smul h x hh
        rw [hlc, Algebra.smul_def] at hint
        obtain ⟨a, ha⟩ := hB _ hint
        refine ⟨a, ?_⟩
        rw [ha, tail_eq b x (by omega : k ≤ n), hc]
  -- the largest unit coefficient
  obtain ⟨i₀, hi₀⟩ := hunit
  have hi₀n : i₀ ≤ n := by
    by_contra hlt
    have : g.coeff i₀ = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    rw [this, map_zero, map_zero] at hi₀
    exact zero_ne_one hi₀
  set S := (Finset.range (n + 1)).filter (fun i => w.valuation (b i) = 1) with hS
  have hSne : S.Nonempty := ⟨i₀, by simp [hS, hb, hi₀]; omega⟩
  set j := S.max' hSne with hj
  have hjS : j ∈ S := S.max'_mem hSne
  have hjn : j ≤ n := by
    have := (Finset.mem_filter.mp hjS).1
    exact Nat.lt_succ_iff.mp (Finset.mem_range.mp this)
  have hjv : w.valuation (b j) = 1 := (Finset.mem_filter.mp hjS).2
  have hbig : ∀ i, j < i → i ≤ n → w.valuation (b i) < 1 := by
    intro i hji hin
    have hle : w.valuation (b i) ≤ 1 := (ValuationSubring.valuation_le_one_iff w _).2 (hBw _)
    refine lt_of_le_of_ne hle ?_
    intro heq
    have : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), heq⟩
    have := S.le_max' i this
    omega
  have htailv : w.valuation (tail b x n (j + 1)) < 1 := by
    unfold tail
    apply Valuation.map_sum_lt _ one_ne_zero
    intro i hi
    rw [Finset.mem_Ico] at hi
    rw [Valuation.map_mul, Valuation.map_pow]
    calc w.valuation (b i) * w.valuation x ^ (i - (j + 1) + 1)
        ≤ w.valuation (b i) * 1 := by
          gcongr
          exact pow_le_one₀ zero_le' hxv
      _ < 1 := by rw [mul_one]; exact hbig i (by omega) (by omega)
  obtain ⟨u, hu⟩ := htail (n + 1 - (j + 1)) (j + 1) (by omega) (by omega)
  have hsv : w.valuation (b j + tail b x n (j + 1)) = 1 := by
    rw [Valuation.map_add_eq_of_lt_left _ (by rw [hjv]; exact htailv), hjv]
  have hj1 : 1 ≤ j := by
    by_contra h0
    have hj0 : j = 0 := by omega
    have : b j + tail b x n (j + 1) = 0 := by
      have e := eval_split b x (k := j) (n := n) hjn
      rw [hj0] at e ⊢
      simpa using e.trans hsum
    rw [this, map_zero] at hsv
    exact zero_ne_one hsv
  obtain ⟨a, ha⟩ := htail (n + 1 - j) j (by omega) hj1
  refine ⟨g.coeff j + u, a, ?_, ?_⟩
  · simpa [hu, hb] using hsv
  · rw [ha, tail_eq b x hjn]
    simp [hu, hb]

end FrobLift
