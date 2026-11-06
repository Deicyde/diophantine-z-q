import ZInQKernel.Compiler.Circuits.Packed.Digits

/-!
# Digits of masked histories

Let `c > 0`, `K = 2^c`, `B = 4K`, `T = B^q`, and let `F, D` satisfy `B F + 1 = F + B T` and
`D + F = K F`. Then

1. `F = F_q = ∑_{t ≤ q} B^t` and `D = (K - 1) F_q`;
2. `R` is masked by `D` with `R < T` iff `R = ∑_{t ≤ q} ρ_t B^t` with every `ρ_t < K` and
   `ρ_q = 0`;
3. `S` is masked by `F_q` iff `S = ∑_{t ≤ q} σ_t B^t` with every `σ_t ∈ {0, 1}`.

The digit sequences are unique (`pack_inj`).

(Blueprint: `compiler/natural/packed/packed-masks.md`.)
-/

namespace ZInQ.Compiler.Packed

open Finset

theorem pack_one_geom (B q : ℕ) : B * pack B (fun _ => 1) q + 1 = pack B (fun _ => 1) q + B ^ (q + 1) := by
  induction q with
  | zero => simp [add_comm]
  | succ q ih =>
    rw [pack_succ_top, pow_succ B (q + 1)]
    nlinarith

theorem four_mul_two_pow (c : ℕ) : 4 * 2 ^ c = 2 ^ (c + 2) := by
  rw [pow_add]; ring

/-- Item 1: `F = F_q` and `D = (K - 1) F_q`. -/
theorem F_D_eq {B K F D T q : ℕ} (hB : 2 ≤ B) (hT : T = B ^ q) (hF : B * F + 1 = F + B * T)
    (hD : D + F = K * F) : F = pack B (fun _ => 1) q ∧ D = pack B (fun _ => K - 1) q := by
  have hG := pack_one_geom B q
  set G := pack B (fun _ => 1) q
  have hFG : F = G := by
    rw [hT, ← pow_succ'] at hF
    have h1 : (B - 1) * F = (B - 1) * G := by
      rw [Nat.sub_one_mul, Nat.sub_one_mul]
      omega
    exact Nat.eq_of_mul_eq_mul_left (by omega) h1
  refine ⟨hFG, ?_⟩
  have : D = (K - 1) * F := by rw [Nat.sub_one_mul]; omega
  rw [this, hFG, mul_pack]
  simp

theorem land_le_right' (a b : ℕ) : Nat.land a b ≤ b := Nat.and_le_right

/-- **Digits of masked histories.** -/
theorem packed_masks {c q K B T F D : ℕ} (_hc : 0 < c) (hK : K = 2 ^ c) (hB : B = 4 * K)
    (hT : T = B ^ q) (hF : B * F + 1 = F + B * T) (hD : D + F = K * F) :
    (F = ∑ t ∈ range (q + 1), B ^ t ∧ D = ∑ t ∈ range (q + 1), (K - 1) * B ^ t) ∧
    (∀ R, (Nat.land R D = R ∧ R < T) ↔
      ∃ ρ : ℕ → ℕ, (∀ t ≤ q, ρ t < K) ∧ ρ q = 0 ∧ R = ∑ t ∈ range (q + 1), ρ t * B ^ t) ∧
    (∀ S, Nat.land S F = S ↔
      ∃ σ : ℕ → ℕ, (∀ t ≤ q, σ t ≤ 1) ∧ S = ∑ t ∈ range (q + 1), σ t * B ^ t) := by
  have hB2 : B = 2 ^ (c + 2) := by rw [hB, hK, four_mul_two_pow]
  have hK1 : 1 ≤ K := by rw [hK]; exact Nat.one_le_two_pow
  have hKB : K < B := by omega
  have hBpos : 0 < B := by omega
  obtain ⟨hFq, hDq⟩ := F_D_eq (by omega) hT hF hD
  refine ⟨⟨by rw [hFq, pack]; simp, by rw [hDq, pack]⟩, fun R => ?_, fun S => ?_⟩
  · have hDlt : D < B ^ (q + 1) := by rw [hDq]; exact pack_lt fun t _ => by omega
    have key : ∀ ρ : ℕ → ℕ, (∀ t ≤ q, ρ t < B) →
        Nat.land (pack B ρ q) D = pack B (fun t => ρ t % K) q := by
      intro ρ hρ
      rw [hDq, hB2]
      show pack (2 ^ (c + 2)) ρ q &&& pack (2 ^ (c + 2)) (fun _ => K - 1) q = _
      rw [land_pack (hB2 ▸ hρ) (fun t _ => by rw [← hB2]; omega)]
      refine pack_congr fun t _ => ?_
      rw [hK, Nat.and_two_pow_sub_one_eq_mod]
    constructor
    · rintro ⟨hland, hRT⟩
      have hRD : R ≤ D := hland ▸ land_le_right' R D
      have hR := eq_pack_digit hBpos (q := q) (R := R) (by omega)
      refine ⟨digit B R, fun t ht => ?_, ?_, hR⟩
      · have h1 := key (digit B R) fun t _ => digit_lt hBpos R t
        rw [← hR, hland] at h1
        conv_lhs at h1 => rw [hR]
        have := pack_inj (fun t _ => digit_lt hBpos R t)
          (fun t _ => lt_of_le_of_lt (Nat.mod_le _ _) (digit_lt hBpos R t)) h1 t ht
        rw [this]
        exact Nat.mod_lt _ (by omega)
      · simp [digit, Nat.div_eq_of_lt (hT ▸ hRT)]
    · rintro ⟨ρ, hρ, hρq, rfl⟩
      rw [← pack_def]
      refine ⟨?_, ?_⟩
      · rw [key ρ fun t ht => lt_trans (hρ t ht) hKB]
        exact pack_congr fun t ht => Nat.mod_eq_of_lt (hρ t ht)
      · rw [hT]
        rcases q with _ | q
        · simpa using hρq
        · rw [pack_succ_top, hρq, zero_mul, add_zero]
          exact pack_lt fun t ht => lt_trans (hρ t (by omega)) hKB
  · have hFlt : F < B ^ (q + 1) := by rw [hFq]; exact pack_lt fun t _ => by omega
    have key : ∀ σ : ℕ → ℕ, (∀ t ≤ q, σ t < B) →
        Nat.land (pack B σ q) F = pack B (fun t => σ t % 2) q := by
      intro σ hσ
      rw [hFq, hB2]
      show pack (2 ^ (c + 2)) σ q &&& pack (2 ^ (c + 2)) (fun _ => 1) q = _
      rw [land_pack (hB2 ▸ hσ) (fun t _ => by rw [← hB2]; omega)]
      refine pack_congr fun t _ => ?_
      exact Nat.and_two_pow_sub_one_eq_mod (σ t) 1
    constructor
    · intro hland
      have hSF : S ≤ F := hland ▸ land_le_right' S F
      have hS := eq_pack_digit hBpos (q := q) (R := S) (by omega)
      refine ⟨digit B S, fun t ht => ?_, hS⟩
      have h1 := key (digit B S) fun t _ => digit_lt hBpos S t
      rw [← hS, hland] at h1
      conv_lhs at h1 => rw [hS]
      have := pack_inj (fun t _ => digit_lt hBpos S t)
        (fun t _ => lt_of_le_of_lt (Nat.mod_le _ _) (digit_lt hBpos S t)) h1 t ht
      rw [this]
      exact Nat.le_of_lt_succ (Nat.mod_lt _ (by omega))
    · rintro ⟨σ, hσ, rfl⟩
      rw [← pack_def, key σ fun t ht => by have := hσ t ht; omega]
      exact pack_congr fun t ht => Nat.mod_eq_of_lt (by have := hσ t ht; omega)

end ZInQ.Compiler.Packed
