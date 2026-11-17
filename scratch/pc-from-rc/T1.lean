import Mathlib
def fSet : Finset ℕ := {1, 5, 7, 13, 35, 65, 91, 455}
set_option maxRecDepth 100000 in
theorem divs : Nat.divisors 2730 = {1, 2, 3, 5, 6, 7, 10, 13, 14, 15, 21, 26, 30, 35, 39, 42, 65, 70, 78, 91, 105, 130, 182, 195, 210, 273, 390, 455, 546, 910, 1365, 2730} := by decide
set_option maxRecDepth 100000 in
theorem fSet_dvd : ∀ f ∈ fSet, f ∣ 2730 := by decide
set_option maxRecDepth 100000 in
theorem m_of_r0f : ∀ r₀ ∈ Nat.divisors 2730, ∀ f ∈ fSet,
    r₀ * f / Nat.gcd r₀ f ^ 2 * Nat.gcd r₀ f ^ 2 = r₀ * f ∧ r₀ * f / Nat.gcd r₀ f ^ 2 ∣ 2730 := by
  rw [divs]; decide
set_option maxRecDepth 100000 in
theorem m_bits : ∀ m ∈ Nat.divisors 2730,
    m = (if 2 ∣ m then 2 else 1) * (if 3 ∣ m then 3 else 1) * (if 5 ∣ m then 5 else 1) *
      (if 7 ∣ m then 7 else 1) * (if 13 ∣ m then 13 else 1) := by
  rw [divs]; decide
theorem exists_f (x : ℕ) (h2 : ¬ 2 ∣ x) (h3 : ¬ 3 ∣ x) : ∃ f ∈ fSet, f * x % 24 = 17 := by
  have : x % 24 = 1 ∨ x % 24 = 5 ∨ x % 24 = 7 ∨ x % 24 = 11 ∨ x % 24 = 13 ∨ x % 24 = 17 ∨
      x % 24 = 19 ∨ x % 24 = 23 := by omega
  rcases this with h | h | h | h | h | h | h | h
  · exact ⟨65, by decide, by rw [Nat.mul_mod, h]⟩
  · exact ⟨13, by decide, by rw [Nat.mul_mod, h]⟩
  · exact ⟨91, by decide, by rw [Nat.mul_mod, h]⟩
  · exact ⟨7, by decide, by rw [Nat.mul_mod, h]⟩
  · exact ⟨5, by decide, by rw [Nat.mul_mod, h]⟩
  · exact ⟨1, by decide, by rw [Nat.mul_mod, h]⟩
  · exact ⟨35, by decide, by rw [Nat.mul_mod, h]⟩
  · exact ⟨455, by decide, by rw [Nat.mul_mod, h]⟩
