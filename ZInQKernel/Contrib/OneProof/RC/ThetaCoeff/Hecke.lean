import ZInQKernel.Contrib.OneProof.RC.Odd.Operators
import Mathlib.NumberTheory.ArithmeticFunction.Defs

/-! Positive Fourier coefficients of newforms, their degeneracy translates, and
weight-two Eisenstein series. The Eisenstein calculation uses only divisor sums. -/

noncomputable section

open Finset Nat
namespace ZInQ.Manuscript.RC.ThetaCoeff

variable {K : Type} [Field K]

/-- The recursion at positive indices; the input sequences are extended by zero at index zero. -/
def GoodRec (a : ℕ → K) (eigenvalue χ : K) (q : ℕ) : Prop :=
  ∀ n, eigenvalue * a n = a (q * n) + (q : K) * χ * Odd.divCoeff a q n

/-- The recursion commutes with every degeneracy `g(z) ↦ g(dz)` at `q ∤ d`. -/
theorem GoodRec.degeneracy {a : ℕ → K} {eigenvalue χ : K} {q d : ℕ}
    (h : GoodRec a eigenvalue χ q) (hq : 0 < q) (hd : 0 < d) (hc : d.Coprime q) :
    GoodRec (Odd.divCoeff a d) eigenvalue χ q := by
  intro n
  rw [Odd.divCoeff_mul_coprime a hc, ← Odd.divCoeff_divCoeff_comm a hq hd hc.symm]
  by_cases hn : d ∣ n
  · simpa only [Odd.divCoeff, ite_eq_left hn] using h (n / d)
  · simp only [Odd.divCoeff, ite_eq_right hn, mul_zero, add_zero]

private def eisLeft (α : ℕ →* K) : ArithmeticFunction K :=
  ⟨fun n => if n = 0 then 0 else α n, by simp⟩

private def eisRight (β : ℕ →* K) : ArithmeticFunction K :=
  ⟨fun n => (n : K) * β n, by simp⟩

/-- The positive weight-two Eisenstein coefficients `∑_{d|n} α(n/d)β(d)d`. -/
def eisenstein (α β : ℕ →* K) : ArithmeticFunction K := eisLeft α * eisRight β

private theorem eisenstein_mult (α β : ℕ →* K) : (eisenstein α β).IsMultiplicative := by
  unfold eisenstein
  apply ArithmeticFunction.IsMultiplicative.mul
  · constructor
    · simp [eisLeft]
    · intro m n _
      change (if m * n = 0 then 0 else α (m * n)) =
        (if m = 0 then 0 else α m) * (if n = 0 then 0 else α n)
      by_cases hm : m = 0
      · simp [hm]
      by_cases hn : n = 0
      · simp [hn]
      simp [hm, hn, Nat.mul_ne_zero hm hn, map_mul]
  · constructor
    · simp [eisRight]
    · intro m n _
      change ((m * n : ℕ) : K) * β (m * n) = ((m : K) * β m) * ((n : K) * β n)
      simp [map_mul, mul_mul_mul_comm]

def hpoly (x y : K) (t : ℕ) : K := ∑ i ∈ range (t + 1), x ^ (t - i) * y ^ i

private theorem hpoly_succ (x y : K) (t : ℕ) :
    hpoly x y (t + 1) = x ^ (t + 1) + y * hpoly x y t := by
  rw [hpoly, sum_range_succ', hpoly, mul_sum]
  simp only [Nat.sub_zero, pow_zero, mul_one]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [Nat.add_sub_add_right, pow_succ]
  ring

private theorem hpoly_rec (x y : K) (t : ℕ) :
    (x + y) * hpoly x y (t + 1) = hpoly x y (t + 2) + x * y * hpoly x y t := by
  rw [hpoly_succ x y (t + 1)]
  have h := hpoly_succ x y t
  calc
    _ = y * hpoly x y (t + 1) + x * (x ^ (t + 1) + y * hpoly x y t) := by rw [← h]; ring
    _ = _ := by rw [pow_succ x (t + 1)]; ring

theorem eisenstein_pow (α β : ℕ →* K) {q : ℕ} (hq : q.Prime) (t : ℕ) :
    eisenstein α β (q ^ t) = hpoly (α q) ((q : K) * β q) t := by
  rw [eisenstein, ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal' (fun x y => eisLeft α x * eisRight β y), Nat.sum_divisors_prime_pow hq]
  unfold hpoly
  apply Finset.sum_congr rfl
  intro i hi
  have hit : i ≤ t := by simpa [Nat.lt_succ_iff] using hi
  have hdiv : q ^ t / q ^ i = q ^ (t - i) := by
    have he : q ^ t = q ^ i * q ^ (t - i) := by rw [← pow_add, Nat.add_sub_of_le hit]
    nth_rw 1 [he]
    exact Nat.mul_div_cancel_left _ (pow_pos hq.pos _)
  simp [eisLeft, eisRight, hdiv, hq.ne_zero, map_pow, mul_pow]

theorem eisenstein_at_prime (α β : ℕ →* K) {q : ℕ} (hq : q.Prime) :
    eisenstein α β q = α q + (q : K) * β q := by
  conv_lhs => rw [← pow_one q, eisenstein_pow α β hq]
  simp [hpoly, Finset.sum_range_succ]

/-- The good eigenform recursion for an Eisenstein constituent, proved from its divisor sums. -/
theorem eisenstein_rec (α β : ℕ →* K) {q : ℕ} (hq : q.Prime) :
    GoodRec (eisenstein α β) (α q + (q : K) * β q) (α q * β q) q := by
  intro n
  rcases eq_or_ne n 0 with rfl | hn
  · simp [Odd.divCoeff]
  obtain ⟨t, b, hb, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn q hq.ne_one
  have hcop := (hq.coprime_iff_not_dvd.mpr hb)
  have hmul : ∀ k : ℕ, eisenstein α β (q ^ k * b) =
      hpoly (α q) ((q : K) * β q) k * eisenstein α β b := fun k => by
    rw [(eisenstein_mult α β).map_mul_of_coprime (hcop.pow_left k), eisenstein_pow α β hq k]
  cases t with
  | zero =>
    rw [pow_zero, one_mul, Odd.divCoeff_of_not_dvd _ hb, mul_zero, add_zero]
    rw [(eisenstein_mult α β).map_mul_of_coprime hcop, eisenstein_at_prime α β hq]
  | succ t =>
    rw [show q * (q ^ (t + 1) * b) = q ^ (t + 2) * b by rw [pow_succ q (t + 1)]; ring,
      hmul, hmul, show q ^ (t + 1) * b = q * (q ^ t * b) by rw [pow_succ]; ring,
      Odd.divCoeff_mul_left _ hq.pos, hmul, ← mul_assoc, hpoly_rec]
    ring

#print axioms GoodRec.degeneracy
#print axioms eisenstein_mult
#print axioms hpoly_succ
#print axioms hpoly_rec
#print axioms eisenstein_pow
#print axioms eisenstein_at_prime
#print axioms eisenstein_rec

end ZInQ.Manuscript.RC.ThetaCoeff
