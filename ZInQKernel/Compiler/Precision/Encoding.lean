import Mathlib

/-!
# The signed encoding of integers

Blueprint: `compiler/natural/precision/signed-encoding.md` and
`compiler/natural/precision/signed-encoding-bijection.md`.

`enc : ℤ → ℕ` sends `n ≥ 0` to `2n` and `n < 0` to `-2n - 1`; `dec : ℕ → ℤ` inverts it. The five
precision inputs decode, in the fixed order `(n, κ, a, l, j)`, by `decode5`.
-/

namespace ZInQ.Compiler.Precision

/-- The signed encoding `enc(n) = 2n` for `n ≥ 0` and `-2n - 1` for `n < 0`. -/
def enc (n : ℤ) : ℕ := if 0 ≤ n then 2 * n.toNat else 2 * (-n).toNat - 1

/-- The signed decoding `dec(c) = c/2` for even `c` and `-(c+1)/2` for odd `c`. -/
def dec (c : ℕ) : ℤ := if c % 2 = 0 then ((c / 2 : ℕ) : ℤ) else -(((c + 1) / 2 : ℕ) : ℤ)

/-- The signed decoding of a tuple of five precision inputs; coordinates `0, …, 4` are
`n, κ, a, l, j`. -/
def decode5 (c : Fin 5 → ℕ) : Fin 5 → ℤ := fun i => dec (c i)

theorem enc_of_nonneg {n : ℤ} (h : 0 ≤ n) : (enc n : ℤ) = 2 * n := by
  unfold enc; rw [ite_eq_left h]; push_cast; rw [Int.toNat_of_nonneg h]

theorem enc_of_neg {n : ℤ} (h : n < 0) : (enc n : ℤ) = -2 * n - 1 := by
  unfold enc; rw [ite_eq_right (not_le.mpr h)]
  have : 1 ≤ 2 * (-n).toNat := by omega
  push_cast [this]; rw [Int.toNat_of_nonneg (by omega)]; ring

theorem dec_of_even {c : ℕ} (h : c % 2 = 0) : dec c = (c : ℤ) / 2 := by
  unfold dec; rw [ite_eq_left h]; omega

theorem dec_of_odd {c : ℕ} (h : c % 2 = 1) : dec c = -(((c : ℤ) + 1) / 2) := by
  unfold dec; rw [ite_eq_right (by omega)]; omega

/-- `dec (enc n) = n`. -/
theorem dec_enc (n : ℤ) : dec (enc n) = n := by
  unfold dec enc; split_ifs <;> omega

/-- `enc (dec c) = c`. -/
theorem enc_dec (c : ℕ) : enc (dec c) = c := by
  unfold dec enc; split_ifs <;> omega

/-- `enc n` is even exactly when `n ≥ 0`. -/
theorem even_enc_iff (n : ℤ) : Even (enc n) ↔ 0 ≤ n := by
  rw [Nat.even_iff]; unfold enc; split_ifs <;> omega

/-- `dec c ≥ 0` exactly when `c` is even. -/
theorem dec_nonneg_iff (c : ℕ) : 0 ≤ dec c ↔ Even c := by
  rw [Nat.even_iff]; unfold dec; split_ifs <;> omega

/-- `|dec c| = ⌈c/2⌉`, in natural-number form. -/
theorem natAbs_dec (c : ℕ) : (dec c).natAbs = (c + 1) / 2 := by
  unfold dec; split_ifs <;> omega

/-- `|dec c| = ⌈c/2⌉`. -/
theorem abs_dec (c : ℕ) : |dec c| = ⌈(c : ℚ) / 2⌉ := by
  have hc : ⌈(c : ℚ) / 2⌉ = (((c + 1) / 2 : ℕ) : ℤ) := by
    rw [Int.ceil_eq_iff]
    constructor
    · have h1 : (((c + 1) / 2 : ℕ) : ℤ) - 1 ≤ ((c : ℤ) - 1) / 2 := by omega
      have h2 : ((((c : ℤ) - 1) / 2 : ℤ) : ℚ) * 2 ≤ (c : ℚ) - 1 := by
        exact_mod_cast (by omega : (((c : ℤ) - 1) / 2) * 2 ≤ (c : ℤ) - 1)
      have h3 : (((((c + 1) / 2 : ℕ) : ℤ) - 1 : ℤ) : ℚ) ≤ ((((c : ℤ) - 1) / 2 : ℤ) : ℚ) := by
        exact_mod_cast h1
      push_cast at h3 ⊢
      linarith
    · have h1 : (c : ℤ) ≤ 2 * (((c + 1) / 2 : ℕ) : ℤ) := by omega
      have h2 : (c : ℚ) ≤ 2 * ((((c + 1) / 2 : ℕ) : ℤ) : ℚ) := by exact_mod_cast h1
      push_cast at h2 ⊢
      linarith
  rw [hc, Int.abs_eq_natAbs, natAbs_dec]

/-- The signed encoding as an equivalence `ℤ ≃ ℕ`. -/
def encEquiv : ℤ ≃ ℕ where
  toFun := enc
  invFun := dec
  left_inv := dec_enc
  right_inv := enc_dec

theorem enc_injective : Function.Injective enc := encEquiv.injective

theorem dec_injective : Function.Injective dec := encEquiv.symm.injective

end ZInQ.Compiler.Precision
