import ZInQKernel.Compiler.Circuits.Packed.Digits

/-!
# Decoding the transition equations

Let `K < B` and `q ∈ ℕ`.

1. (Registers) For `ρ_t < K`, `α_t ≤ 1`, `γ_t ≤ 1` (`t ≤ q`) and `ι < K`, with
   `R = ∑ ρ_t B^t`, `A = ∑ α_t B^t`, `C = ∑ γ_t B^t`: `R + B C = ι + B R + B A` iff `ρ_0 = ι`,
   `ρ_{t+1} + γ_t = ρ_t + α_t` for `t < q`, and `γ_q = ρ_q + α_q`.
2. (States) For `σ_t ≤ 1`, `η_t ≤ 1`, `e ∈ {0, 1}`, with `S = ∑ σ_t B^t`, `I = ∑ η_t B^t`:
   `S = e + B I` iff `σ_0 = e`, `σ_{t+1} = η_t` for `t < q`, and `η_q = 0`.

(Blueprint: `compiler/natural/packed/packed-transitions.md`.)
-/

namespace ZInQ.Compiler.Packed

open Finset

/-- Multiplying by `B` shifts the digits. -/
theorem mul_base_pack (B : ℕ) (f : ℕ → ℕ) (q : ℕ) :
    B * pack B f q = pack B (fun t => if t = 0 then 0 else f (t - 1)) (q + 1) := by
  rw [pack_succ]
  simp

/-- A packing of length `q + 1` is one of length `q + 2` with a zero top digit. -/
theorem pack_extend (B : ℕ) (f : ℕ → ℕ) (q : ℕ) :
    pack B f q = pack B (fun t => if t ≤ q then f t else 0) (q + 1) := by
  rw [pack_succ_top, ite_eq_right (by omega), zero_mul, add_zero]
  exact pack_congr fun t ht => (ite_eq_left ht).symm

/-- **Item 1: the register equations.** -/
theorem packed_register_iff {B K q ι : ℕ} (hKB : K < B) (ρ α γ : ℕ → ℕ)
    (hρ : ∀ t ≤ q, ρ t < K) (hα : ∀ t ≤ q, α t ≤ 1) (hγ : ∀ t ≤ q, γ t ≤ 1) (hι : ι < K) :
    (∑ t ∈ range (q + 1), ρ t * B ^ t) + B * (∑ t ∈ range (q + 1), γ t * B ^ t) =
        ι + B * (∑ t ∈ range (q + 1), ρ t * B ^ t) + B * (∑ t ∈ range (q + 1), α t * B ^ t) ↔
      ρ 0 = ι ∧ (∀ t < q, ρ (t + 1) + γ t = ρ t + α t) ∧ γ q = ρ q + α q := by
  simp only [← pack_def]
  have hL : pack B ρ q + B * pack B γ q =
      pack B (fun t => (if t ≤ q then ρ t else 0) + (if t = 0 then 0 else γ (t - 1))) (q + 1) := by
    rw [pack_extend B ρ q, mul_base_pack, pack_add]
  have hR : ι + B * pack B ρ q + B * pack B α q =
      pack B (fun t => (if t = 0 then ι else 0) + ((if t = 0 then 0 else ρ (t - 1)) +
        (if t = 0 then 0 else α (t - 1)))) (q + 1) := by
    rw [mul_base_pack, mul_base_pack, add_assoc, pack_add, pack_succ, pack_succ]
    simp only [ite_eq_left, Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false, add_tsub_cancel_right]
    simp
  rw [hL, hR]
  have hdL : ∀ t ≤ q + 1, (if t ≤ q then ρ t else 0) + (if t = 0 then 0 else γ (t - 1)) < B := by
    intro t ht
    split_ifs with h1 h2 h2
    · have := hρ t h1; omega
    · have := hρ t h1; have := hγ (t - 1) (by omega); omega
    · omega
    · have := hγ (t - 1) (by omega); omega
  have hdR : ∀ t ≤ q + 1, (if t = 0 then ι else 0) + ((if t = 0 then 0 else ρ (t - 1)) +
      (if t = 0 then 0 else α (t - 1))) < B := by
    intro t ht
    split_ifs with h1
    · omega
    · have := hρ (t - 1) (by omega); have := hα (t - 1) (by omega); omega
  constructor
  · intro h
    have e := pack_inj hdL hdR h
    refine ⟨by simpa using e 0 (by omega), fun t ht => ?_, ?_⟩
    · have := e (t + 1) (by omega)
      simp only [show t + 1 ≤ q by omega, ite_true, Nat.add_eq_zero_iff, one_ne_zero, and_false,
        ite_false, add_tsub_cancel_right, zero_add] at this
      exact this
    · have := e (q + 1) (by omega)
      simp only [show ¬ (q + 1 ≤ q) by omega, ite_false, Nat.add_eq_zero_iff, one_ne_zero,
        and_false, add_tsub_cancel_right, zero_add] at this
      exact this
  · rintro ⟨h0, h1, h2⟩
    refine pack_congr fun t ht => ?_
    rcases t with _ | t
    · simp [h0]
    · simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false, add_tsub_cancel_right,
        zero_add]
      split_ifs with h
      · exact h1 t (by omega)
      · rw [show t = q by omega, h2]; simp

/-- **Item 2: the state equations.** -/
theorem packed_state_iff {B q e : ℕ} (hB : 1 < B) (σ η : ℕ → ℕ) (hσ : ∀ t ≤ q, σ t ≤ 1)
    (hη : ∀ t ≤ q, η t ≤ 1) (he : e ≤ 1) :
    (∑ t ∈ range (q + 1), σ t * B ^ t) = e + B * (∑ t ∈ range (q + 1), η t * B ^ t) ↔
      σ 0 = e ∧ (∀ t < q, σ (t + 1) = η t) ∧ η q = 0 := by
  simp only [← pack_def]
  have hR : e + B * pack B η q =
      pack B (fun t => (if t = 0 then e else 0) + (if t = 0 then 0 else η (t - 1))) (q + 1) := by
    rw [mul_base_pack, pack_succ, pack_succ]
    simp
  rw [pack_extend B σ q, hR]
  have hdL : ∀ t ≤ q + 1, (if t ≤ q then σ t else 0) < B := by
    intro t ht; split_ifs with h
    · have := hσ t h; omega
    · omega
  have hdR : ∀ t ≤ q + 1, (if t = 0 then e else 0) + (if t = 0 then 0 else η (t - 1)) < B := by
    intro t ht
    split_ifs with h1
    · omega
    · have := hη (t - 1) (by omega); omega
  constructor
  · intro h
    have e' := pack_inj hdL hdR h
    refine ⟨by simpa using e' 0 (by omega), fun t ht => ?_, ?_⟩
    · have := e' (t + 1) (by omega)
      simp only [show t + 1 ≤ q by omega, ite_true, Nat.add_eq_zero_iff, one_ne_zero, and_false,
        ite_false, add_tsub_cancel_right, zero_add] at this
      exact this
    · have := e' (q + 1) (by omega)
      simp only [show ¬ (q + 1 ≤ q) by omega, ite_false, Nat.add_eq_zero_iff, one_ne_zero,
        and_false, add_tsub_cancel_right, zero_add] at this
      exact this.symm
  · rintro ⟨h0, h1, h2⟩
    refine pack_congr fun t ht => ?_
    rcases t with _ | t
    · simp [h0]
    · simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false, add_tsub_cancel_right,
        zero_add]
      split_ifs with h
      · exact h1 t (by omega)
      · rw [show t = q by omega, h2]

end ZInQ.Compiler.Packed
