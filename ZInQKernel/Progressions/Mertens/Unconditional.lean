import ZInQKernel.Progressions.Mertens.Twisted
import ZInQKernel.Progressions.Mertens.Count
import ZInQKernel.Progressions.LSeries.PartialSum

/-!
# Plan step 4.2 without hypotheses, and the count from a lower bound for `L(1, χ)`

With the partial-sum estimate of plan step 1 (`norm_partialSum_sub_LFunction_one_le`) and the
bound `‖T(x)‖ ≤ M²`, `M = log q + 3` (`norm_partialSum_log_le`), for `χ ≠ 1`:
`‖L(1, χ)‖ · ‖S_χ(x)‖ ≤ ‖T(x)‖ + 2q ψ(x)/x ≤ M² + 6q`. A lower bound `c ≤ ‖L(1, χ)‖` for all
`χ ≠ 1` (plan steps 2 and 3) then gives the bound `B = (M² + 6q)/c` of
`twentytwo_primes_of_twisted_bound`.
-/

namespace ZInQ.Progressions

open Finset
open scoped Chebyshev

variable {q : ℕ} [NeZero q]

/-- **Plan step 4.2**: `‖L(1, χ)‖ · ‖S_χ(x)‖ ≤ ‖T(x)‖ + 2q ψ(x)/x` for `χ ≠ 1` and `x ≥ 1`. -/
theorem norm_LFunction_one_mul_norm_twistedSum_le {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    {x : ℝ} (hx : 1 ≤ x) :
    ‖DirichletCharacter.LFunction χ 1‖ * ‖twistedSum χ x‖ ≤
      ‖logSum χ x‖ + 2 * q * ψ x / x :=
  norm_LFunction_one_mul_norm_twistedSum_le_of χ
    (fun _ hy ↦ norm_partialSum_sub_LFunction_one_le hχ hy) hx

/-- `‖L(1, χ)‖ · ‖S_χ(x)‖ ≤ M² + 6q` with `M = log q + 3`, for `χ ≠ 1` and `x ≥ 1`. -/
theorem norm_LFunction_one_mul_norm_twistedSum_le_explicit {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) {x : ℝ} (hx : 1 ≤ x) :
    ‖DirichletCharacter.LFunction χ 1‖ * ‖twistedSum χ x‖ ≤ (Real.log q + 3) ^ 2 + 6 * q := by
  have h1 := norm_LFunction_one_mul_norm_twistedSum_le hχ hx
  have h2 : ‖logSum χ x‖ ≤ (Real.log q + 3) ^ 2 := norm_partialSum_log_le hχ x
  have h3 : 2 * q * ψ x / x ≤ 6 * q := by
    have := psi_div_le_three (by linarith : (0 : ℝ) < x)
    have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    rw [mul_div_assoc]
    nlinarith
  linarith

/-- `‖S_χ(x)‖ ≤ (M² + 6q)/‖L(1, χ)‖` with `M = log q + 3`, for `χ ≠ 1` and `x ≥ 1`. -/
theorem norm_twistedSum_le {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {x : ℝ} (hx : 1 ≤ x) :
    ‖twistedSum χ x‖ ≤ ((Real.log q + 3) ^ 2 + 6 * q) / ‖DirichletCharacter.LFunction χ 1‖ := by
  have hL : 0 < ‖DirichletCharacter.LFunction χ 1‖ :=
    norm_pos_iff.mpr (DirichletCharacter.LFunction_apply_one_ne_zero hχ)
  rw [le_div_iff₀ hL, mul_comm]
  exact norm_LFunction_one_mul_norm_twistedSum_le_explicit hχ hx

/-- **Twenty-two primes from a lower bound for `L(1, χ)`.** Let `q ≥ 3`, `a` coprime to `q`, and
`c > 0` with `c ≤ ‖L(1, χ)‖` for every Dirichlet character `χ ≠ 1` mod `q`. Then at least 22
primes `p ≡ a (mod q)` satisfy `q^8 < p ≤ q^8 · exp(5qB)` with `B = ((log q + 3)² + 6q)/c`. -/
theorem twentytwo_primes_of_LFunction_lower_bound (hq : 3 ≤ q) {a : ℕ} (ha : a.Coprime q)
    {c : ℝ} (hc : 0 < c)
    (hL : ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → c ≤ ‖DirichletCharacter.LFunction χ 1‖) :
    22 ≤ #{p ∈ Ioc (q ^ 8)
        ⌊(q : ℝ) ^ 8 * Real.exp (5 * q * (((Real.log q + 3) ^ 2 + 6 * q) / c))⌋₊ |
      p.Prime ∧ p ≡ a [MOD q]} := by
  have hq' : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg (by linarith)
  refine twentytwo_primes_of_twisted_bound hq ha ?_ fun χ hχ x hx ↦ ?_
  · -- `B ≥ 1`: some `χ ≠ 1` exists, and `c ≤ ‖L(1, χ)‖ ≤ log q + 3`
    have : Fact (2 < q) := ⟨by omega⟩
    obtain ⟨χ, hχ⟩ := DirichletCharacter.exists_apply_ne_one_of_hasEnoughRootsOfUnity ℂ
      (ZMod.neg_one_ne_one (n := q))
    have hχ1 : χ ≠ 1 := by
      rintro rfl
      exact hχ (MulChar.one_apply (isUnit_one.neg))
    have h1 := (hL χ hχ1).trans (norm_LFunction_one_le hχ1)
    rw [le_div_iff₀ hc]
    nlinarith
  · calc ‖twistedSum χ x‖ ≤ ((Real.log q + 3) ^ 2 + 6 * q) /
          ‖DirichletCharacter.LFunction χ 1‖ := norm_twistedSum_le hχ hx
      _ ≤ ((Real.log q + 3) ^ 2 + 6 * q) / c := by
          gcongr
          exact hL χ hχ

end ZInQ.Progressions
