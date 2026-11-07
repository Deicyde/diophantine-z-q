import ZInQKernel.Compiler.Circuits.Packed.Masks

/-!
# The packed nonzero indicator

Let `c > 0`, `K = 2^c`, `B = 4K`, `F = F_q`, `D = (K - 1) F_q` and `R = ∑_{t ≤ q} ρ_t B^t` with
every `ρ_t < K`. Then `(R + D) AND (K F_q) = K ∑_{t ≤ q} [ρ_t > 0] B^t`; consequently
`K N = (R + D) AND (K F_q)` iff `N` is the packed nonzero indicator of `R`.

(Blueprint: `compiler/natural/packed/packed-nonzero-indicator.md`.)
-/

namespace ZInQ.Compiler.Packed

open Finset

/-- Below `2^{c+1}`, bit `c` is set exactly from `2^c` on. -/
theorem land_two_pow_eq {c n : ℕ} (hn : n < 2 ^ (c + 1)) :
    n &&& 2 ^ c = if 2 ^ c ≤ n then 2 ^ c else 0 := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, Nat.testBit_two_pow]
  by_cases hjc : c = j
  · subst hjc
    have hbit : n.testBit c = decide (2 ^ c ≤ n) := by
      rw [Nat.testBit_eq_decide_div_mod_eq]
      have h2 : n / 2 ^ c < 2 := by
        rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos c)]; rw [pow_succ] at hn; omega
      have h3 : 2 ^ c ≤ n ↔ 1 ≤ n / 2 ^ c := by
        rw [Nat.le_div_iff_mul_le (Nat.two_pow_pos c), one_mul]
      by_cases h : 2 ^ c ≤ n
      · have : n / 2 ^ c = 1 := by have := h3.1 h; omega
        simp [this, h]
      · have : n / 2 ^ c = 0 := Nat.lt_one_iff.mp (Nat.lt_of_not_le (mt h3.2 h))
        simp [this, h]
    rw [hbit]
    split_ifs with h <;> simp [h, Nat.testBit_two_pow_self]
  · simp only [hjc, decide_false, Bool.and_false]
    split_ifs
    · rw [Nat.testBit_two_pow]; simp [hjc]
    · simp

/-- **The packed nonzero indicator.** -/
theorem nonzero_indicator {c q K B F D : ℕ} (_hc : 0 < c) (hK : K = 2 ^ c) (hB : B = 4 * K)
    (hF : F = ∑ t ∈ range (q + 1), B ^ t) (hD : D = (K - 1) * F) (ρ : ℕ → ℕ)
    (hρ : ∀ t ≤ q, ρ t < K) :
    Nat.land (∑ t ∈ range (q + 1), ρ t * B ^ t + D) (K * F) =
        K * ∑ t ∈ range (q + 1), (if 0 < ρ t then 1 else 0) * B ^ t ∧
      ∀ N, K * N = Nat.land (∑ t ∈ range (q + 1), ρ t * B ^ t + D) (K * F) ↔
        N = ∑ t ∈ range (q + 1), (if 0 < ρ t then 1 else 0) * B ^ t := by
  have hB2 : B = 2 ^ (c + 2) := by rw [hB, hK, four_mul_two_pow]
  have hK1 : 1 ≤ K := by rw [hK]; exact Nat.one_le_two_pow
  have hKpos : 0 < K := hK1
  have hFp : F = pack B (fun _ => 1) q := by rw [hF]; simp [pack]
  have hsum : ∑ t ∈ range (q + 1), ρ t * B ^ t + D = pack B (fun t => ρ t + (K - 1)) q := by
    rw [← pack_def, hD, hFp, mul_pack, pack_add]; simp
  have hKF : K * F = pack B (fun _ => K) q := by rw [hFp, mul_pack]; simp
  have main : Nat.land (∑ t ∈ range (q + 1), ρ t * B ^ t + D) (K * F) =
      K * ∑ t ∈ range (q + 1), (if 0 < ρ t then 1 else 0) * B ^ t := by
    rw [hsum, hKF, ← pack_def, mul_pack, hB2]
    show pack (2 ^ (c + 2)) _ q &&& pack (2 ^ (c + 2)) _ q = _
    have hK2 : K < 2 ^ (c + 2) := by rw [← hB2]; omega
    rw [land_pack (fun t ht => by have := hρ t ht; rw [← hB2]; omega) (fun t _ => hK2)]
    refine pack_congr fun t ht => ?_
    have hlt : ρ t + (K - 1) < 2 ^ (c + 1) := by
      have := hρ t ht; rw [pow_succ, ← hK]; omega
    have hl : (ρ t + (K - 1)) &&& K = if K ≤ ρ t + (K - 1) then K else 0 := by
      have := land_two_pow_eq hlt; rwa [← hK] at this
    rw [hl]
    by_cases h : 0 < ρ t
    · rw [ite_eq_left (by omega), ite_eq_left h, mul_one]
    · rw [ite_eq_right (by omega), ite_eq_right h, mul_zero]
  refine ⟨main, fun N => ?_⟩
  rw [main]
  exact ⟨fun h => Nat.eq_of_mul_eq_mul_left hKpos h, fun h => by rw [h]⟩

end ZInQ.Compiler.Packed
