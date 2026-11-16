import ZInQKernel.Contrib.HeckeFE.Basic

/-!
# gz-theta: `heckeCoeff 1 N` as a sum over `a` odd, `b` even

`heckeCoeff 1 N = ¼ ∑_{a² + b² = N} u(a, b) (a + b i)` (`HeckeFE/Basic.lean`), where
`u(a, b) = unitOf(a mod 4, b mod 4)` vanishes unless `a ≢ b (mod 2)`. Pairing `(b, a)` with
`(a, b)` and using `u(−a, b) = −u(a, b)`:

  `heckeCoeff 1 N = ∑_{a² + b² = N, a odd, b even} u(a, b) · ⌊a/2⌋`

(`heckeCoeff_one_eq_sum_Soe`), and `u(2n + 1, 2m) = (−1)^{n+m}` (`uo_odd_even`).
-/

open Complex ZInQ.Contrib.HeckeFE
open scoped Real

noncomputable section

namespace ZInQ.GZTheta

/-- `u(a, b) = unitOf(a mod 4, b mod 4)`. -/
def uo (p : ℤ × ℤ) : ℂ := unitOf ((p.1 : ZMod 4), (p.2 : ZMod 4))

/-- The points of the fibre with `a` odd, `b` even. -/
def Soe (N : ℕ) : Finset (ℤ × ℤ) := (normFiber N).filter (fun p => p.1 % 2 = 1 ∧ p.2 % 2 = 0)

/-- The points of the fibre with `a` even, `b` odd. -/
def Seo (N : ℕ) : Finset (ℤ × ℤ) := (normFiber N).filter (fun p => p.1 % 2 = 0 ∧ p.2 % 2 = 1)

theorem intCast_zmod4 (a : ℤ) : (a : ZMod 4) = ((a % 4 : ℤ) : ZMod 4) :=
  (ZMod.intCast_mod a 4).symm

/-- The values of `u` at `a` odd, `b` even, in terms of residues. -/
theorem uo_cases {a b : ℤ} (ha : a % 2 = 1) (hb : b % 2 = 0) :
    (a % 4 = 1 ∧ b % 4 = 0 ∧ uo (a, b) = 1) ∨ (a % 4 = 3 ∧ b % 4 = 2 ∧ uo (a, b) = 1) ∨
      (a % 4 = 3 ∧ b % 4 = 0 ∧ uo (a, b) = -1) ∨ (a % 4 = 1 ∧ b % 4 = 2 ∧ uo (a, b) = -1) := by
  have h4a : a % 4 = 1 ∨ a % 4 = 3 := by omega
  have h4b : b % 4 = 0 ∨ b % 4 = 2 := by omega
  unfold uo
  rw [intCast_zmod4 a, intCast_zmod4 b]
  rcases h4a with h1 | h1 <;> rcases h4b with h2 | h2 <;> rw [h1, h2] <;>
    simp [unitOf] <;> decide

theorem uo_cases_eo {a b : ℤ} (ha : a % 2 = 1) (hb : b % 2 = 0) :
    (a % 4 = 1 ∧ b % 4 = 0 ∧ uo (b, a) = -I) ∨ (a % 4 = 3 ∧ b % 4 = 2 ∧ uo (b, a) = -I) ∨
      (a % 4 = 3 ∧ b % 4 = 0 ∧ uo (b, a) = I) ∨ (a % 4 = 1 ∧ b % 4 = 2 ∧ uo (b, a) = I) := by
  have h4a : a % 4 = 1 ∨ a % 4 = 3 := by omega
  have h4b : b % 4 = 0 ∨ b % 4 = 2 := by omega
  unfold uo
  rw [intCast_zmod4 a, intCast_zmod4 b]
  rcases h4a with h1 | h1 <;> rcases h4b with h2 | h2 <;> rw [h1, h2] <;>
    simp (config := { decide := true }) [unitOf]

theorem uo_swap {a b : ℤ} (ha : a % 2 = 1) (hb : b % 2 = 0) :
    uo (b, a) * ((b : ℂ) + a * I) = uo (a, b) * ((a : ℂ) - b * I) := by
  have h1 := uo_cases ha hb
  have h2 := uo_cases_eo ha hb
  rcases h1 with ⟨x1, x2, x3⟩ | ⟨x1, x2, x3⟩ | ⟨x1, x2, x3⟩ | ⟨x1, x2, x3⟩ <;>
    rcases h2 with ⟨y1, y2, y3⟩ | ⟨y1, y2, y3⟩ | ⟨y1, y2, y3⟩ | ⟨y1, y2, y3⟩ <;>
    first | omega | (rw [x3, y3]; ring_nf; rw [I_sq]; ring)

theorem uo_neg {a b : ℤ} (ha : a % 2 = 1) (hb : b % 2 = 0) : uo (-a, b) = -uo (a, b) := by
  have hab := uo_cases ha hb
  have hna := uo_cases (a := -a) (b := b) (by omega) hb
  rcases hab with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;>
    rcases hna with ⟨k1, k2, k3⟩ | ⟨k1, k2, k3⟩ | ⟨k1, k2, k3⟩ | ⟨k1, k2, k3⟩ <;>
    first | omega | (rw [h3, k3]; try norm_num)

theorem uo_eq_zero {a b : ℤ} (h : a % 2 = b % 2) : uo (a, b) = 0 := by
  show unitOf ((a : ZMod 4), (b : ZMod 4)) = 0
  apply unitOf_eq_zero_of_even
  have h1 := ZMod.val_intCast (n := 4) a
  have h2 := ZMod.val_intCast (n := 4) b
  omega

theorem mem_normFiber_swap {N : ℕ} {p : ℤ × ℤ} :
    (p.2, p.1) ∈ normFiber N ↔ p ∈ normFiber N := by
  rw [mem_normFiber, mem_normFiber]
  constructor <;> intro h <;> linarith

/-- `heckeCoeff 1 N = ½ ∑_{Soe} u(a, b) a`. -/
theorem heckeCoeff_one_eq_half_sum (N : ℕ) :
    heckeCoeff 1 N = (1 / 2) * ∑ p ∈ Soe N, uo p * (p.1 : ℂ) := by
  unfold heckeCoeff
  have hgz : ∀ p : ℤ × ℤ, gz 0 0 p = (p.1 : ℂ) + p.2 * I := fun p => by simp [gz]
  simp only [jacobiSym.one_right, Int.cast_one, one_mul, hgz]
  change (1 / 4 : ℂ) * ∑ p ∈ normFiber N, uo p * ((p.1 : ℂ) + p.2 * I) = _
  -- split off `Soe`, then `Seo`; the rest vanishes
  rw [← Finset.sum_filter_add_sum_filter_not (normFiber N)
    (fun p => p.1 % 2 = 1 ∧ p.2 % 2 = 0)]
  rw [← Finset.sum_filter_add_sum_filter_not ((normFiber N).filter
    (fun p : ℤ × ℤ => ¬ (p.1 % 2 = 1 ∧ p.2 % 2 = 0))) (fun p => p.1 % 2 = 0 ∧ p.2 % 2 = 1)]
  have hrest : ∑ p ∈ ((normFiber N).filter (fun p : ℤ × ℤ => ¬ (p.1 % 2 = 1 ∧ p.2 % 2 = 0))).filter
      (fun p : ℤ × ℤ => ¬ (p.1 % 2 = 0 ∧ p.2 % 2 = 1)), uo p * ((p.1 : ℂ) + p.2 * I) = 0 := by
    refine Finset.sum_eq_zero fun p hp => ?_
    simp only [Finset.mem_filter] at hp
    rw [uo_eq_zero (by omega), zero_mul]
  rw [hrest, add_zero]
  have hSeo : ∑ p ∈ ((normFiber N).filter (fun p : ℤ × ℤ => ¬ (p.1 % 2 = 1 ∧ p.2 % 2 = 0))).filter
      (fun p : ℤ × ℤ => p.1 % 2 = 0 ∧ p.2 % 2 = 1), uo p * ((p.1 : ℂ) + p.2 * I) =
      ∑ p ∈ Soe N, uo p * ((p.1 : ℂ) - p.2 * I) := by
    refine Finset.sum_nbij' (fun p => (p.2, p.1)) (fun p => (p.2, p.1)) ?_ ?_ ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_filter, Soe] at hp ⊢
      exact ⟨mem_normFiber_swap.mpr hp.1.1, hp.2.2, hp.2.1⟩
    · intro p hp
      simp only [Finset.mem_filter, Soe] at hp ⊢
      refine ⟨⟨mem_normFiber_swap.mpr hp.1, by omega⟩, hp.2.2, hp.2.1⟩
    · intro p _; rfl
    · intro p _; rfl
    · intro p hp
      simp only [Finset.mem_filter] at hp
      exact uo_swap (a := p.2) (b := p.1) hp.2.2 hp.2.1
  rw [hSeo]
  change (1 / 4 : ℂ) * (∑ p ∈ Soe N, uo p * ((p.1 : ℂ) + p.2 * I) +
    ∑ p ∈ Soe N, uo p * ((p.1 : ℂ) - p.2 * I)) = _
  rw [← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  ring

/-- `∑_{Soe} u(a, b) = 0` (the involution `a ↦ −a`). -/
theorem sum_Soe_uo (N : ℕ) : ∑ p ∈ Soe N, uo p = 0 := by
  have h : ∑ p ∈ Soe N, uo p = ∑ p ∈ Soe N, -uo p := by
    refine Finset.sum_nbij' (fun p => (-p.1, p.2)) (fun p => (-p.1, p.2)) ?_ ?_ ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_filter, Soe, mem_normFiber] at hp ⊢
      refine ⟨by rw [neg_sq]; exact hp.1, by omega, hp.2.2⟩
    · intro p hp
      simp only [Finset.mem_filter, Soe, mem_normFiber] at hp ⊢
      refine ⟨by rw [neg_sq]; exact hp.1, by omega, hp.2.2⟩
    · intro p _; simp
    · intro p _; simp
    · intro p hp
      simp only [Finset.mem_filter, Soe] at hp
      rw [uo_neg hp.2.1 hp.2.2, neg_neg]
  rw [Finset.sum_neg_distrib] at h
  have : (2 : ℂ) * ∑ p ∈ Soe N, uo p = 0 := by linear_combination h
  simpa using this

/-- **`heckeCoeff 1 N = ∑_{a² + b² = N, a odd, b even} u(a, b) ⌊a/2⌋`.** -/
theorem heckeCoeff_one_eq_sum_Soe (N : ℕ) :
    heckeCoeff 1 N = ∑ p ∈ Soe N, uo p * ((p.1 / 2 : ℤ) : ℂ) := by
  rw [heckeCoeff_one_eq_half_sum]
  have h0 := sum_Soe_uo N
  have : ∀ p ∈ Soe N, uo p * (p.1 : ℂ) = 2 * (uo p * ((p.1 / 2 : ℤ) : ℂ)) + uo p := by
    intro p hp
    simp only [Soe, Finset.mem_filter] at hp
    have : p.1 = 2 * (p.1 / 2) + 1 := by omega
    conv_lhs => rw [this]
    push_cast
    ring
  rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, h0, add_zero, ← Finset.mul_sum]
  ring

/-- `u(2n + 1, 2m) = (−1)^{n+m}`, as `e^{π i (n + m)}`. -/
theorem uo_odd_even (n m : ℤ) : uo (2 * n + 1, 2 * m) = cexp (π * I * (n + m)) := by
  have hc := uo_cases (a := 2 * n + 1) (b := 2 * m) (by omega) (by omega)
  have hsign : ∀ k : ℤ, cexp (π * I * k) = if k % 2 = 0 then 1 else -1 := by
    intro k
    have hk : k = 2 * (k / 2) + k % 2 := by omega
    have hk2 : k % 2 = 0 ∨ k % 2 = 1 := by omega
    rcases hk2 with h | h
    · rw [if_pos h]
      have : π * I * (k : ℂ) = ((k / 2 : ℤ) : ℂ) * (2 * π * I) := by
        conv_lhs => rw [hk, h]
        push_cast; ring
      rw [this, Complex.exp_int_mul_two_pi_mul_I]
    · rw [if_neg (by omega)]
      have : π * I * (k : ℂ) = π * I + ((k / 2 : ℤ) : ℂ) * (2 * π * I) := by
        conv_lhs => rw [hk, h]
        push_cast; ring
      rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, Complex.exp_pi_mul_I]
      ring
  have e : (π : ℂ) * I * ((n : ℂ) + m) = π * I * ((n + m : ℤ) : ℂ) := by push_cast; ring
  rw [e, hsign]
  rcases hc with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;> rw [h3] <;>
    split_ifs <;> first | rfl | omega

end ZInQ.GZTheta
