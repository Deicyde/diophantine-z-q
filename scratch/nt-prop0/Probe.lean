import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.NumberTheory.Padics.RingHoms

/-! Probe for Lemma SQ(b) of docs/research/nt-prop0.md §2.1: a unit of `ℤ₂` that is `1 mod 8`
is a square. Tests the Hensel API (`hensels_lemma`) and the residue maps. -/

open Polynomial PadicInt

theorem probe_isSquare_of_toZModPow_three (u : ℤ_[2]) (h : toZModPow 3 u = 1) : IsSquare u := by
  set F : Polynomial ℤ_[2] := X ^ 2 - C u
  have hF1 : F.aeval (1 : ℤ_[2]) = 1 - u := by simp [F]
  have hD1 : F.derivative.aeval (1 : ℤ_[2]) = 2 := by
    simp [F]; norm_num
  have h8 : ‖(1 : ℤ_[2]) - u‖ ≤ ((2 : ℕ) : ℝ) ^ (-(3 : ℕ) : ℤ) := by
    rw [norm_le_pow_iff_mem_span_pow, ← ker_toZModPow, RingHom.mem_ker, map_sub, map_one, h,
      sub_self]
  have h2 : ‖(2 : ℤ_[2])‖ = (2 : ℝ)⁻¹ := by
    have := norm_p (p := 2); exact_mod_cast this
  have hnorm : ‖F.aeval (1 : ℤ_[2])‖ < ‖F.derivative.aeval (1 : ℤ_[2])‖ ^ 2 := by
    rw [hF1, hD1, h2]
    refine lt_of_le_of_lt h8 ?_
    norm_num
  obtain ⟨z, hz, -⟩ := hensels_lemma hnorm
  refine ⟨z, ?_⟩
  have : z ^ 2 - u = 0 := by simpa [F] using hz
  rw [← sq]; linear_combination -this

/-- The odd-prime half, Lemma SQ(a) (⇐), from a residue square root. -/
theorem probe_isSquare_of_toZMod {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (u : ℤ_[p])
    (hu : IsUnit u) (h : IsSquare (toZMod u)) : IsSquare u := by
  obtain ⟨s, hs⟩ := h
  set a : ℤ_[p] := ((s.val : ℕ) : ℤ_[p])
  have ha : toZMod a = s := by simp [a]
  set F : Polynomial ℤ_[p] := X ^ 2 - C u
  have hFa : F.aeval a = a ^ 2 - u := by simp [F]
  have hDa : F.derivative.aeval a = 2 * a := by simp [F]; left; norm_num
  have hres : toZMod (a ^ 2 - u) = 0 := by
    rw [map_sub, map_pow, ha, hs, sq, sub_self]
  have hlt : ‖a ^ 2 - u‖ < 1 := by
    have : a ^ 2 - u ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
      rw [← ker_toZMod, RingHom.mem_ker]; exact hres
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits] at this; exact this
  have hs0 : s ≠ 0 := by
    rintro rfl
    have : toZMod u = 0 := by rw [hs, mul_zero]
    have hm : u ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
      rw [← ker_toZMod, RingHom.mem_ker]; exact this
    exact (IsLocalRing.mem_maximalIdeal _).mp hm hu
  have h2a : ‖(2 : ℤ_[p]) * a‖ = 1 := by
    rw [← PadicInt.isUnit_iff]
    by_contra hn
    have hm : (2 : ℤ_[p]) * a ∈ IsLocalRing.maximalIdeal ℤ_[p] := hn
    rw [← ker_toZMod, RingHom.mem_ker, map_mul, ha, map_ofNat] at hm
    rcases mul_eq_zero.mp hm with h0 | h0
    · have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h0
      rw [ZMod.natCast_eq_zero_iff] at this
      exact hp ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).mp this)
    · exact hs0 h0
  have hnorm : ‖F.aeval a‖ < ‖F.derivative.aeval a‖ ^ 2 := by
    rw [hFa, hDa, h2a, one_pow]; exact hlt
  obtain ⟨z, hz, -⟩ := hensels_lemma hnorm
  refine ⟨z, ?_⟩
  have : z ^ 2 - u = 0 := by simpa [F] using hz
  rw [← sq]; linear_combination -this

#print axioms probe_isSquare_of_toZModPow_three
#print axioms probe_isSquare_of_toZMod
