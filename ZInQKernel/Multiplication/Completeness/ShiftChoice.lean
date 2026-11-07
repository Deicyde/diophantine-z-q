import Mathlib

/-!
# Choice of the shift at a selected prime

For `M ≥ 1` and `d₁, d₂ ≥ 1` with `gcd(d₁, d₂) = 4` the congruences `h ≡ 0 (mod lcm(M, d₁))`
and `h ≡ 4M (mod d₂)` are compatible, since `gcd(lcm(M, d₁), d₂)` divides
`gcd(M d₁, M d₂) = 4M`; the Chinese remainder theorem gives solutions `h > 4M`.
-/

namespace ZInQ.Mult

/-- **Choice of the shift at a selected prime.** -/
theorem shift_choice (M d₁ d₂ : ℕ) (hM : 1 ≤ M) (hd₁ : 1 ≤ d₁) (hd₂ : 1 ≤ d₂)
    (hg : Nat.gcd d₁ d₂ = 4) :
    ∃ h : ℤ, 4 * (M : ℤ) < h ∧ ((Nat.lcm M d₁ : ℕ) : ℤ) ∣ h ∧ (d₂ : ℤ) ∣ h - 4 * M := by
  set n := Nat.lcm M d₁ with hn
  have hcompat : 0 ≡ 4 * M [MOD Nat.gcd n d₂] := by
    refine (Nat.modEq_zero_iff_dvd.mpr ?_).symm
    have h1 : Nat.gcd n d₂ ∣ M * d₁ :=
      (Nat.gcd_dvd_left _ _).trans (Nat.lcm_dvd_mul M d₁)
    have h2 : Nat.gcd n d₂ ∣ M * d₂ := (Nat.gcd_dvd_right _ _).trans (dvd_mul_left _ _)
    have h3 := Nat.dvd_gcd h1 h2
    rwa [Nat.gcd_mul_left, hg, mul_comm] at h3
  obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder' hcompat
  have hnpos : 0 < n := Nat.lcm_pos (by omega) (by omega)
  refine ⟨(k : ℤ) + n * d₂ * (4 * M + 1), ?_, ?_, ?_⟩
  · have : (1 : ℤ) ≤ n * d₂ := by
      have : 1 ≤ n * d₂ := Nat.mul_pos hnpos (by omega)
      exact_mod_cast this
    nlinarith [Int.natCast_nonneg k]
  · refine dvd_add ?_ (Dvd.intro (d₂ * (4 * M + 1) : ℤ) (by ring))
    exact Int.natCast_dvd_natCast.mpr (Nat.modEq_zero_iff_dvd.mp hk1)
  · have h := (Nat.ModEq.dvd hk2.symm)
    push_cast at h
    have : (k : ℤ) + n * d₂ * (4 * M + 1) - 4 * M = ((k : ℤ) - 4 * M) + d₂ * (n * (4 * M + 1)) := by
      ring
    rw [this]
    exact dvd_add h (dvd_mul_right _ _)

/-- The consequences used in the completeness proof: `h ≠ 0`, `h ≠ 4M`, `M ∣ h`, `d₁ ∣ h` and
`d₂ ∣ h - 4M`. -/
theorem shift_choice' (M d₁ d₂ : ℕ) (hM : 1 ≤ M) (hd₁ : 1 ≤ d₁) (hd₂ : 1 ≤ d₂)
    (hg : Nat.gcd d₁ d₂ = 4) :
    ∃ h : ℤ, h ≠ 0 ∧ h ≠ 4 * M ∧ (M : ℤ) ∣ h ∧ (d₁ : ℤ) ∣ h ∧ (d₂ : ℤ) ∣ h - 4 * M := by
  obtain ⟨h, hlt, hl, hd⟩ := shift_choice M d₁ d₂ hM hd₁ hd₂ hg
  refine ⟨h, by omega, by omega, ?_, ?_, hd⟩
  · exact (Int.natCast_dvd_natCast.mpr (Nat.dvd_lcm_left M d₁)).trans hl
  · exact (Int.natCast_dvd_natCast.mpr (Nat.dvd_lcm_right M d₁)).trans hl

end ZInQ.Mult
