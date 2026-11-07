import Mathlib

/-!
# Power lemmas with the ambient instance

With Mathlib imported, `a ^ n` on `ℕ` elaborates through `Monoid.toNPow Nat.instMonoid`, while
the core lemmas `Nat.pow_lt_pow_right`, … are stated with `instPowNat`, and generic Mathlib
lemmas carry yet other instance paths. When the kernel compares two such terms that are not
syntactically equal, it unfolds both sides and tries to evaluate `Nat.pow`; on a closed term
such as `2 ^ 2 ^ 8008` this fails. The lemmas below are stated with the ambient instance and
proved for variables (where the instance mismatch is harmless), so that applying them to the
astronomically large closed terms of the size chapter produces syntactically matching types.
They live in `ZInQ.Size.AmbientPow`; open that namespace to use them.
-/

namespace ZInQ.Size.AmbientPow

theorem natPow_lt_natPow_right {a m n : ℕ} (ha : 1 < a) (h : m < n) : a ^ m < a ^ n :=
  Nat.pow_lt_pow_right ha h

theorem natPow_le_natPow_right {a m n : ℕ} (ha : 0 < a) (h : m ≤ n) : a ^ m ≤ a ^ n :=
  Nat.pow_le_pow_right ha h

theorem natPow_lt_natPow_left {a b : ℕ} (h : a < b) {n : ℕ} (hn : n ≠ 0) : a ^ n < b ^ n :=
  Nat.pow_lt_pow_left h hn

theorem natPow_le_natPow_left {a b : ℕ} (h : a ≤ b) (n : ℕ) : a ^ n ≤ b ^ n :=
  Nat.pow_le_pow_left h n

theorem lt_two_natPow (n : ℕ) : n < 2 ^ n :=
  Nat.lt_two_pow_self

theorem natPow_pos {a : ℕ} (ha : 0 < a) (n : ℕ) : 0 < a ^ n := by
  positivity

theorem natPow_add (a m n : ℕ) : a ^ (m + n) = a ^ m * a ^ n :=
  Nat.pow_add a m n

theorem natPow_mul (a m n : ℕ) : a ^ (m * n) = (a ^ m) ^ n :=
  Nat.pow_mul a m n

theorem mul_natPow (a b n : ℕ) : (a * b) ^ n = a ^ n * b ^ n :=
  Nat.mul_pow a b n

theorem le_self_natPow {a n : ℕ} (hn : n ≠ 0) : a ≤ a ^ n :=
  Nat.le_self_pow hn a

theorem one_le_natPow {a : ℕ} (ha : 0 < a) (n : ℕ) : 1 ≤ a ^ n :=
  Nat.one_le_pow n a ha

theorem prod_le_natPow_card {ι : Type*} (s : Finset ι) (f : ι → ℕ) (n : ℕ)
    (h : ∀ x ∈ s, f x ≤ n) : ∏ x ∈ s, f x ≤ n ^ s.card :=
  Finset.prod_le_pow_card s f n h

end ZInQ.Size.AmbientPow
