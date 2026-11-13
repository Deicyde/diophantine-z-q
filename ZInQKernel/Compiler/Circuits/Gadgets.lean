import Mathlib

/-!
# The equational gadgets over the naturals

For natural numbers `a, b, M, x`:

1. `(∃ d, b = a + 1 + d) ↔ a < b`;
2. `(∃ d, b = a d) ↔ a ∣ b`;
3. `(∃ u v, a + M u = b + M v) ↔ a ≡ b [MOD M]`, which for `M = 0` says `a = b`;
4. `(∃ h, x = 2 h + 1) ↔ x` is odd.

(Blueprint: `compiler/natural/formulas/natural-atom-gadgets.md`.)
-/

namespace ZInQ.Compiler.Natural

theorem lt_gadget_iff (a b : ℕ) : (∃ d : ℕ, b = a + 1 + d) ↔ a < b := by
  constructor
  · rintro ⟨d, rfl⟩; omega
  · intro h; exact ⟨b - a - 1, by omega⟩

theorem dvd_gadget_iff (a b : ℕ) : (∃ d : ℕ, b = a * d) ↔ a ∣ b := Iff.rfl

theorem congr_gadget_iff (a M b : ℕ) : (∃ u v : ℕ, a + M * u = b + M * v) ↔ a ≡ b [MOD M] := by
  constructor
  · rintro ⟨u, v, h⟩
    have : (a + M * u) % M = (b + M * v) % M := by rw [h]
    simpa [Nat.ModEq, Nat.add_mul_mod_self_left] using this
  · intro h
    rcases le_total a b with hab | hab
    · obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' hab).1 h
      exact ⟨k, 0, by omega⟩
    · obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' hab).1 h.symm
      exact ⟨0, k, by omega⟩

/-- For the zero modulus the congruence gadget says `a = b`. -/
theorem congr_gadget_zero_iff (a b : ℕ) : (∃ u v : ℕ, a + 0 * u = b + 0 * v) ↔ a = b := by
  simp

theorem odd_gadget_iff (x : ℕ) : (∃ h : ℕ, x = 2 * h + 1) ↔ Odd x := by
  constructor
  · rintro ⟨h, rfl⟩; exact ⟨h, rfl⟩
  · rintro ⟨h, rfl⟩; exact ⟨h, rfl⟩

end ZInQ.Compiler.Natural
