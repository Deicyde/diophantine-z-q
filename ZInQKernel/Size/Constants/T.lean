import ZInQKernel.Size.Constants.D
import ZInQKernel.Size.Constants.FormalMultiple

/-!
# `R = D`, the closed form of `T`, and the triple-tower bound

Blueprint: `size/constants/r-equals-d.md`, `size/constants/t-identity.md`,
`size/constants/t-bound.md`.

Under the catalogue bound CAT₈ `D` dominates `H_max`, `c_*` and `10^12`, so `R = D`; then
`Q = D^(10 G₀² D³)`, the maximum defining `A_ht` is `Q^17`, and
`T = (96·10^13)^13 · D^(2210 G₀² D³) < 2^(D^8) < 2^(2^(2^9013))`.

As everywhere in this directory, every estimate is first proved for variables and then applied
to the named constants after rewriting them with their defining equations: the kernel never
compares two different terms containing `D`, so it never tries to evaluate it.
-/

namespace ZInQ.Size

open Syntax AmbientPow

/-! ### `R = D` -/

set_option exponentiation.threshold 4200 in
theorem W_pow_eight_lt : W ^ 8 < 2 ^ 4096 :=
  calc W ^ 8 < (2 ^ 512) ^ 8 := natPow_lt_natPow_left W_lt_two_pow_512 (by decide)
    _ = 2 ^ (512 * 8) := (natPow_mul _ _ _).symm

/-- `H_max < 2^(W⁸) < 2^(2^4096)`: the cutoff of CAT₈ in the form used by the size chain. -/
theorem Hmax_lt_two_pow_two_pow (hCAT : CatalogueBound8) :
    Hmax < 2 ^ W ^ 8 ∧ 2 ^ W ^ 8 < 2 ^ 2 ^ 4096 :=
  ⟨Hmax_lt_of_catalogueBound8 hCAT, natPow_lt_natPow_right (by decide) W_pow_eight_lt⟩

/-- `H_max < 2^(W⁸) < 2^(2^4096) < D`. -/
theorem Hmax_lt_D (hCAT : CatalogueBound8) : Hmax < D :=
  calc Hmax < 2 ^ W ^ 8 := (Hmax_lt_two_pow_two_pow hCAT).1
    _ < 2 ^ 2 ^ 4096 := (Hmax_lt_two_pow_two_pow hCAT).2
    _ < D := two_pow_two_pow_lt_D (by decide)

/-- `c_* < 2^(2^4617) < D`. -/
theorem cstar_lt_D (hCAT : CatalogueBound8) : cstar < D :=
  (cstar_lt hCAT).trans (two_pow_two_pow_lt_D (by decide))

set_option exponentiation.threshold 8100 in
/-- `10^12 < 2^40 < D`. -/
theorem ten_pow_twelve_lt_D : 10 ^ 12 < D :=
  lt_D_of_lt (closed_comparisons_3.1.trans (natPow_lt_natPow_right (by decide) (by decide)))

theorem max_three_eq_of {d h c t : ℕ} (hh : h ≤ d) (hc : c ≤ d) (ht : t ≤ d) :
    max (max (max d h) c) t = d := by
  rw [max_eq_left hh, max_eq_left hc, max_eq_left ht]

/-- `R = max(D, H_max, c_*, 10^12) = D`. -/
theorem R_eq_D (hCAT : CatalogueBound8) : R = D := by
  rw [R_eq]
  exact max_three_eq_of (Hmax_lt_D hCAT).le (cstar_lt_D hCAT).le ten_pow_twelve_lt_D.le

/-- The parameter `R` equals `D` (the blueprint statement). -/
theorem r_equals_d (hCAT : CatalogueBound8) :
    Hmax < D ∧ cstar < D ∧ 10 ^ 12 < D ∧ R = D :=
  ⟨Hmax_lt_D hCAT, cstar_lt_D hCAT, ten_pow_twelve_lt_D, R_eq_D hCAT⟩

/-! ### The closed form of `T` -/

theorem Q_exponent_eq (d g : ℕ) : d * (10 * (d * g) ^ 2) = 10 * g ^ 2 * d ^ 3 := by
  ring

/-- `Q = R^(R E₀) = D^(10 G₀² D³)`. -/
theorem Q_eq_closed (hCAT : CatalogueBound8) : Q = D ^ (10 * G0 ^ 2 * D ^ 3) := by
  rw [Q_eq, R_eq_D hCAT, E0_eq, Q_exponent_eq]

/-- The estimate `C_cm < 2^(50000 D²)`, for a variable `d ≥ 1`. -/
theorem Ccm_lt_of {d : ℕ} (hd : 1 ≤ d) :
    2 * (d ^ 2 * 3 ^ (21000 * d ^ 2) + 1) + 4096 * ((1028 + 5 * d) + 84000 * d ^ 2) <
      2 ^ (50000 * d ^ 2) := by
  have hs : 1 ≤ d ^ 2 := one_le_natPow hd 2
  have hds : d ≤ d ^ 2 := le_self_natPow (by decide)
  generalize d ^ 2 = s at hs hds ⊢
  have h3 : 3 ^ (21000 * s) ≤ 2 ^ (42000 * s) :=
    calc 3 ^ (21000 * s) ≤ (2 ^ 2) ^ (21000 * s) := natPow_le_natPow_left (by decide) _
      _ = 2 ^ (42000 * s) := by rw [← natPow_mul]; congr 1; ring
  have hB : s * 3 ^ (21000 * s) + 1 ≤ 2 ^ (42001 * s) :=
    calc s * 3 ^ (21000 * s) + 1 ≤ 2 ^ s * 2 ^ (42000 * s) :=
          Nat.mul_lt_mul_of_lt_of_le (lt_two_natPow s) h3 (natPow_pos (by decide) _)
      _ = 2 ^ (42001 * s) := by rw [← natPow_add]; congr 1; ring
  have hL : 4096 * ((1028 + 5 * d) + 84000 * s) < 2 ^ (42001 * s) :=
    calc 4096 * ((1028 + 5 * d) + 84000 * s) ≤ 4096 * 85033 * s := by nlinarith
      _ < 2 ^ 29 * 2 ^ s :=
          Nat.mul_lt_mul_of_lt_of_lt closed_comparisons_4 (lt_two_natPow s)
      _ = 2 ^ (29 + s) := (natPow_add _ _ _).symm
      _ ≤ 2 ^ (42001 * s) := natPow_le_natPow_right (by decide) (by omega)
  have hX : 4 * 2 ^ (42001 * s) ≤ 2 ^ (50000 * s) :=
    calc 4 * 2 ^ (42001 * s) = 2 ^ (2 + 42001 * s) := by rw [natPow_add]; rfl
      _ ≤ 2 ^ (50000 * s) := natPow_le_natPow_right (by decide) (by omega)
  omega

/-- The estimate `2^(50000 D²) < Q^17`, for variables `d ≥ 300` and `g ≥ 1`. -/
theorem two_pow_lt_Q17_of {d g : ℕ} (hd : 300 ≤ d) (hg : 1 ≤ g) :
    2 ^ (50000 * d ^ 2) < (d ^ (10 * g ^ 2 * d ^ 3)) ^ 17 := by
  have hg2 : 1 ≤ g ^ 2 := one_le_natPow hg 2
  have he : 50000 * d ^ 2 < 10 * g ^ 2 * d ^ 3 * 17 := by
    have hd2 : 0 < d ^ 2 := natPow_pos (by omega) 2
    calc 50000 * d ^ 2 < 170 * 300 * d ^ 2 := Nat.mul_lt_mul_of_pos_right (by decide) hd2
      _ ≤ 170 * d * d ^ 2 := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hd)
      _ ≤ 170 * (g ^ 2 * d) * d ^ 2 :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left d hg2))
      _ = 10 * g ^ 2 * d ^ 3 * 17 := by ring
  calc 2 ^ (50000 * d ^ 2) < 2 ^ (10 * g ^ 2 * d ^ 3 * 17) := natPow_lt_natPow_right (by decide) he
    _ ≤ d ^ (10 * g ^ 2 * d ^ 3 * 17) := natPow_le_natPow_left (by omega) _
    _ = (d ^ (10 * g ^ 2 * d ^ 3)) ^ 17 := natPow_mul _ _ _

set_option exponentiation.threshold 8100 in
theorem three_hundred_le_D : 300 ≤ D :=
  (lt_D_of_lt (by decide)).le

/-- `C_cm < 2^(50000 D²) < Q^17`. -/
theorem Ccm_lt_Q17 (hCAT : CatalogueBound8) :
    Ccm < 2 ^ (50000 * D ^ 2) ∧ 2 ^ (50000 * D ^ 2) < Q ^ 17 := by
  constructor
  · rw [Ccm_eq, Bcm_eq]; exact Ccm_lt_of D_pos
  · rw [Q_eq_closed hCAT]; exact two_pow_lt_Q17_of three_hundred_le_D G0_pos

theorem max_one_eq_of {c q : ℕ} (hc : c ≤ q) (hq : 1 ≤ q) : max (max 1 c) q = q :=
  max_eq_right (max_le hq hc)

/-- `max(1, C_cm, Q^17) = Q^17`. -/
theorem max_Aht_eq (hCAT : CatalogueBound8) : max (max 1 Ccm) (Q ^ 17) = Q ^ 17 :=
  max_one_eq_of ((Ccm_lt_Q17 hCAT).1.trans (Ccm_lt_Q17 hCAT).2).le (one_le_natPow Q_pos 17)

theorem Aht_closed_of (d g : ℕ) :
    2 * 10 ^ 13 * (d ^ (10 * g ^ 2 * d ^ 3)) ^ 17 = 2 * 10 ^ 13 * d ^ (170 * g ^ 2 * d ^ 3) := by
  rw [← natPow_mul]; congr 2; ring

/-- `A_ht = 2·10^13 · Q^17 = 2·10^13 · D^(170 G₀² D³)`. -/
theorem Aht_eq_closed (hCAT : CatalogueBound8) :
    Aht = 2 * 10 ^ 13 * Q ^ 17 ∧ Aht = 2 * 10 ^ 13 * D ^ (170 * G0 ^ 2 * D ^ 3) := by
  have h : Aht = 2 * 10 ^ 13 * Q ^ 17 := by rw [Aht_eq, max_Aht_eq hCAT]
  refine ⟨h, ?_⟩
  rw [h, Q_eq_closed hCAT]
  exact Aht_closed_of D G0

theorem T_closed_of (d g : ℕ) :
    (48 * (2 * 10 ^ 13 * (d ^ (10 * g ^ 2 * d ^ 3)) ^ 17)) ^ 13 =
      (96 * 10 ^ 13) ^ 13 * d ^ (2210 * g ^ 2 * d ^ 3) := by
  have h : ∀ x : ℕ, 48 * (2 * 10 ^ 13 * x) = 96 * 10 ^ 13 * x := fun x => by ring
  rw [h, mul_natPow, ← natPow_mul, ← natPow_mul]
  congr 2
  ring

/-- `T = (48 A_ht)^13 = (96·10^13)^13 · D^(2210 G₀² D³)`. -/
theorem T_eq_closed (hCAT : CatalogueBound8) :
    T = (96 * 10 ^ 13) ^ 13 * D ^ (2210 * G0 ^ 2 * D ^ 3) := by
  rw [T_eq, (Aht_eq_closed hCAT).1, Q_eq_closed hCAT]
  exact T_closed_of D G0

/-- The closed form of `T` (the blueprint statement). -/
theorem t_identity (hCAT : CatalogueBound8) :
    Q = D ^ (10 * G0 ^ 2 * D ^ 3) ∧
    (Ccm < 2 ^ (50000 * D ^ 2) ∧ 2 ^ (50000 * D ^ 2) < Q ^ 17 ∧
      max (max 1 Ccm) (Q ^ 17) = Q ^ 17) ∧
    Aht = 2 * 10 ^ 13 * D ^ (170 * G0 ^ 2 * D ^ 3) ∧
    T = (96 * 10 ^ 13) ^ 13 * D ^ (2210 * G0 ^ 2 * D ^ 3) :=
  ⟨Q_eq_closed hCAT, ⟨(Ccm_lt_Q17 hCAT).1, (Ccm_lt_Q17 hCAT).2, max_Aht_eq hCAT⟩,
    (Aht_eq_closed hCAT).2, T_eq_closed hCAT⟩

/-! ### The triple-tower bound -/

set_option exponentiation.threshold 9100 in
/-- The triple-tower bound for the closed form, for variables `d` and `g` with
`2^(2^8008) < d < 2^(2^9010)` and `0 < 2210 g² < 2^86`. -/
theorem closedT_lt_of {d g : ℕ} (hd : 2 ^ 2 ^ 8008 < d) (hd' : d < 2 ^ 2 ^ 9010)
    (hg : 2210 * g ^ 2 < 2 ^ 86) (hg0 : 0 < g) :
    (96 * 10 ^ 13) ^ 13 * d ^ (2210 * g ^ 2 * d ^ 3) < 2 ^ d ^ 8 ∧
      2 ^ d ^ 8 < 2 ^ 2 ^ 2 ^ 9013 := by
  have hbig : ∀ {k : ℕ}, k < 8008 → 2 ^ k < d := fun hk =>
    (natPow_lt_natPow_right (by decide) ((lt_two_natPow _).trans (natPow_lt_natPow_right (by decide) hk))).trans hd
  have hd650 : 650 < d := (by decide : 650 < 2 ^ 10).trans (hbig (by decide))
  have hd0 : 0 < d := (by decide : 0 < 650).trans hd650
  have hC : 2210 * g ^ 2 < d := hg.trans (hbig (by decide))
  have hE : 2210 * g ^ 2 * d ^ 3 < d ^ 4 :=
    calc 2210 * g ^ 2 * d ^ 3 < d * d ^ 3 := Nat.mul_lt_mul_of_pos_right hC (natPow_pos hd0 3)
      _ = d ^ 4 := by ring
  have hEpos : 2210 * g ^ 2 * d ^ 3 ≠ 0 := by positivity
  have hDE : d * (2210 * g ^ 2 * d ^ 3) < d ^ 5 :=
    calc d * (2210 * g ^ 2 * d ^ 3) < d * d ^ 4 := Nat.mul_lt_mul_of_pos_left hE hd0
      _ = d ^ 5 := by ring
  have hDP : d ^ (2210 * g ^ 2 * d ^ 3) < 2 ^ d ^ 5 :=
    calc d ^ (2210 * g ^ 2 * d ^ 3) < (2 ^ d) ^ (2210 * g ^ 2 * d ^ 3) :=
          natPow_lt_natPow_left (lt_two_natPow d) hEpos
      _ = 2 ^ (d * (2210 * g ^ 2 * d ^ 3)) := (natPow_mul _ _ _).symm
      _ < 2 ^ d ^ 5 := natPow_lt_natPow_right (by decide) hDE
  have hSmall : 650 + d ^ 5 < d ^ 8 := by
    have h5 : 0 < d ^ 5 := natPow_pos hd0 5
    have h8 : d ^ 8 = d ^ 3 * d ^ 5 := by ring
    have h3 : d ≤ d ^ 3 := le_self_natPow (by decide)
    rw [h8]
    nlinarith
  refine ⟨?_, ?_⟩
  · calc (96 * 10 ^ 13) ^ 13 * d ^ (2210 * g ^ 2 * d ^ 3) < 2 ^ 650 * 2 ^ d ^ 5 :=
          Nat.mul_lt_mul_of_lt_of_lt closed_comparisons_5.1 hDP
      _ = 2 ^ (650 + d ^ 5) := (natPow_add _ _ _).symm
      _ < 2 ^ d ^ 8 := natPow_lt_natPow_right (by decide) hSmall
  · have h8 : d ^ 8 < 2 ^ 2 ^ 9013 :=
      calc d ^ 8 < (2 ^ 2 ^ 9010) ^ 8 := natPow_lt_natPow_left hd' (by decide)
        _ = 2 ^ (2 ^ 9010 * 8) := (natPow_mul _ _ _).symm
        _ = 2 ^ 2 ^ 9013 := congrArg (2 ^ ·) (by norm_num)
    exact natPow_lt_natPow_right (by decide) h8

/-- `(96·10^13)^13 · D^(2210 G₀² D³) < 2^(D^8) < 2^(2^(2^9013))` (the blueprint statement). -/
theorem closedT_lt :
    (96 * 10 ^ 13) ^ 13 * D ^ (2210 * G0 ^ 2 * D ^ 3) < 2 ^ D ^ 8 ∧
      2 ^ D ^ 8 < 2 ^ 2 ^ 2 ^ 9013 :=
  closedT_lt_of D_gt D_lt (by rw [G0_eq]; exact closed_comparisons_5.2) G0_pos

/-- `T < 2^(2^(2^9013))`. -/
theorem T_lt (hCAT : CatalogueBound8) : T < 2 ^ 2 ^ 2 ^ 9013 := by
  rw [T_eq_closed hCAT]; exact closedT_lt.1.trans closedT_lt.2

/-- Upstream's `triplePower a = 2^(2^(2^a))`, as an equation for a variable: upstream states
it with another power instance, so this bridge must not be checked on a closed `a`. -/
theorem triplePower_eq (a : ℕ) : NumericalTowerBounds.triplePower a = 2 ^ 2 ^ 2 ^ a := rfl

/-- `T < triplePower 9013`, in the form of upstream's `NumericalTowerBounds`. -/
theorem T_lt_triplePower (hCAT : CatalogueBound8) : T < NumericalTowerBounds.triplePower 9013 := by
  rw [triplePower_eq]; exact T_lt hCAT

end ZInQ.Size
