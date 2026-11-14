import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.FieldTheory.Finite.Basic

/-! # shimura-glue, local part: `nrd(𝒪_p^×) = ℤ_p^×` and `nrd(1 + 3𝒪_3) ⊇ 1 + 3ℤ_3`

In the basis `1, i, (1+j)/2, (i+k)/2` of the maximal order `𝒪` of `B = (2,−3 | ℚ)` (the kernel's
`LeafQM.ofInt`), the reduced norm is the quaternary form
`N4 n = (n₀² + n₀n₂ + n₂²) − 2(n₁² + n₁n₃ + n₃²)`. This file proves, over Mathlib's `ℤ_[p]`, that `N4`
represents every unit of `ℤ_p` (every prime `p`), and that a unit `u ≡ 1 mod 3` of `ℤ_3` is a square
`x²` with `x ≡ 1 mod 3`. -/

set_option linter.all false

noncomputable section

namespace ShimuraGlue

open Polynomial

/-- The reduced norm of `𝒪` in the coordinates of `LeafQM.ofInt`. -/
def N4 {R : Type*} [CommRing R] (n : Fin 4 → R) : R :=
  n 0 ^ 2 + n 0 * n 2 + n 2 ^ 2 - 2 * (n 1 ^ 2 + n 1 * n 3 + n 3 ^ 2)

theorem map_N4 {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (n : Fin 4 → R) :
    f (N4 n) = N4 (fun i => f (n i)) := by
  simp only [N4, map_sub, map_add, map_mul, map_pow, map_ofNat]

variable {p : ℕ} [hp : Fact p.Prime]

theorem norm_lt_one_iff_toZMod (x : ℤ_[p]) : ‖x‖ < 1 ↔ PadicInt.toZMod x = 0 := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]

theorem norm_eq_one_iff_toZMod (x : ℤ_[p]) : ‖x‖ = 1 ↔ PadicInt.toZMod x ≠ 0 := by
  rw [ne_eq, ← norm_lt_one_iff_toZMod]
  have := PadicInt.norm_le_one x
  constructor
  · intro h; rw [h]; exact lt_irrefl 1
  · intro h; exact le_antisymm this (not_lt.1 h)

theorem isUnit_iff_toZMod (x : ℤ_[p]) : IsUnit x ↔ PadicInt.toZMod x ≠ 0 := by
  rw [PadicInt.isUnit_iff, norm_eq_one_iff_toZMod]

/-- Hensel's lemma in the simple-root form. -/
theorem hensel_simple (F : ℤ_[p][X]) (a : ℤ_[p])
    (h0 : PadicInt.toZMod (F.eval a) = 0) (h1 : PadicInt.toZMod (F.derivative.eval a) ≠ 0) :
    ∃ z : ℤ_[p], F.eval z = 0 ∧ PadicInt.toZMod z = PadicInt.toZMod a := by
  have hn0 : ‖F.eval a‖ < 1 := (norm_lt_one_iff_toZMod _).2 h0
  have hn1 : ‖F.derivative.eval a‖ = 1 := (norm_eq_one_iff_toZMod _).2 h1
  obtain ⟨z, hz, hza, -⟩ := hensels_lemma (F := F) (a := a) (by
    simp only [Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id]
    rw [hn1]; simpa using hn0)
  simp only [Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id] at hz hza
  refine ⟨z, hz, ?_⟩
  rw [hn1, norm_lt_one_iff_toZMod, map_sub, sub_eq_zero] at hza
  exact hza

/-- The canonical lift `ZMod p → ℤ_[p]` (by `val`) is a section of `toZMod`. -/
theorem toZMod_lift (x : ZMod p) : PadicInt.toZMod ((x.val : ℕ) : ℤ_[p]) = x := by
  rw [map_natCast, ZMod.natCast_zmod_val]

/-- **`p = 3`: `N4` represents every unit of `ℤ_3`** (with `n₂ = n₃ = 0`: `x² − 2y²`). -/
theorem rep_three (u : ℤ_[3]) (hu : IsUnit u) : ∃ n : Fin 4 → ℤ_[3], N4 n = u := by
  have hu' := (isUnit_iff_toZMod u).1 hu
  -- choose `y = 0` if `u ≡ 1`, `y = 1` if `u ≡ 2`
  obtain ⟨y, hy⟩ : ∃ y : ℤ_[3], PadicInt.toZMod (1 - 2 * y ^ 2 - u) = 0 := by
    have : ∀ t : ZMod 3, t ≠ 0 → ∃ s : ZMod 3, 1 - 2 * s ^ 2 - t = 0 := by decide
    obtain ⟨s, hs⟩ := this _ hu'
    refine ⟨(s.val : ℤ_[3]), ?_⟩
    simp only [map_sub, map_mul, map_pow, map_one, map_ofNat, toZMod_lift]; exact hs
  obtain ⟨x, hx, -⟩ := hensel_simple (X ^ 2 - C (2 * y ^ 2 + u)) 1 (by
      simp only [eval_sub, eval_pow, eval_X, eval_C, one_pow]
      rw [← hy]; congr 1; ring)
    (by
      simp only [derivative_sub, derivative_X_pow, derivative_C, sub_zero, eval_mul, eval_C,
        eval_pow, eval_X, one_pow, mul_one]
      simp only [map_natCast]; decide)
  refine ⟨![x, y, 0, 0], ?_⟩
  simp only [eval_sub, eval_pow, eval_X, eval_C] at hx
  simp [N4]; linear_combination hx

/-- **`p = 2`: `N4` represents every unit of `ℤ_2`** (`a² + a + 1`, Hensel at `a = 0`). -/
theorem rep_two (u : ℤ_[2]) (hu : IsUnit u) : ∃ n : Fin 4 → ℤ_[2], N4 n = u := by
  have hu' := (isUnit_iff_toZMod u).1 hu
  have h1 : PadicInt.toZMod u = 1 := by revert hu'; generalize PadicInt.toZMod u = t; decide +revert
  obtain ⟨a, ha, -⟩ := hensel_simple (X ^ 2 + X + C (1 - u)) 0 (by
      simp only [eval_add, eval_pow, eval_X, eval_C, map_add, map_sub, map_one, h1]; simp [h1])
    (by
      simp only [derivative_add, derivative_X_pow, derivative_X, derivative_C, add_zero, eval_add,
        eval_mul, eval_C, eval_pow, eval_X, eval_one]
      simp)
  refine ⟨![a, 0, 1, 0], ?_⟩
  simp only [eval_add, eval_pow, eval_X, eval_C] at ha
  simp [N4]; linear_combination ha

/-- **`p ≥ 5`: `N4` represents every unit of `ℤ_p`** (`4(a² + ab + b²) = (2a + b)² + 3b²`; solve
`x² + 3y² = 4u` mod `p` by counting, then lift in a variable with nonzero residue). -/
theorem rep_ge5 (h5 : 5 ≤ p) (u : ℤ_[p]) (hu : IsUnit u) : ∃ n : Fin 4 → ℤ_[p], N4 n = u := by
  have hu' := (isUnit_iff_toZMod u).1 hu
  have hne : ∀ m : ℕ, 0 < m → m < 5 → ((m : ℕ) : ZMod p) ≠ 0 := by
    intro m hm0 hm5 h
    rw [ZMod.natCast_eq_zero_iff] at h
    have := Nat.le_of_dvd hm0 h; omega
  have h2 : (2 : ZMod p) ≠ 0 := by exact_mod_cast hne 2 (by norm_num) (by norm_num)
  have h3 : (3 : ZMod p) ≠ 0 := by exact_mod_cast hne 3 (by norm_num) (by norm_num)
  have h4 : (4 : ZMod p) ≠ 0 := by exact_mod_cast hne 4 (by norm_num) (by norm_num)
  have hodd : Fintype.card (ZMod p) % 2 = 1 := by
    rw [ZMod.card]
    exact Nat.odd_iff.1 (hp.out.odd_of_ne_two (by omega))
  set ub := PadicInt.toZMod u with hub
  -- solve `a² + 3b² = 4ū` in `ZMod p`
  have hg : (C (3 : ZMod p) * X ^ 2 - C (4 * ub)).degree = 2 := by
    rw [degree_sub_C (by rw [degree_C_mul_X_pow 2 h3]; norm_num), degree_C_mul_X_pow 2 h3]; rfl
  obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic (f := X ^ 2) (g := _)
    (by simp) hg hodd
  simp only [eval_pow, eval_X, eval_sub, eval_mul, eval_C] at hab
  set x₀ : ℤ_[p] := (a.val : ℤ_[p])
  set y₀ : ℤ_[p] := (b.val : ℤ_[p])
  -- lift to `x² + 3y² = 4u` in `ℤ_p`
  obtain ⟨x, y, hxy⟩ : ∃ x y : ℤ_[p], x ^ 2 + 3 * y ^ 2 = 4 * u := by
    by_cases ha : a = 0
    · have hb : b ≠ 0 := by
        rintro rfl; apply hu'; rw [ha] at hab
        have : 4 * ub = 0 := by linear_combination -hab
        exact (mul_eq_zero.1 this).resolve_left h4
      have e0 : (C 3 * X ^ 2 + C (x₀ ^ 2 - 4 * u)).eval y₀ = 3 * y₀ ^ 2 + (x₀ ^ 2 - 4 * u) := by
        simp
      have e1 : (C 3 * X ^ 2 + C (x₀ ^ 2 - 4 * u)).derivative.eval y₀ = 6 * y₀ := by
        rw [derivative_add, derivative_C, add_zero, derivative_C_mul_X_pow]
        simp only [eval_mul, eval_C, eval_pow, eval_X, Nat.cast_ofNat]
        norm_num
      obtain ⟨y, hy, -⟩ := hensel_simple (C 3 * X ^ 2 + C (x₀ ^ 2 - 4 * u)) y₀ (by
          rw [e0]
          simp only [map_add, map_mul, map_sub, map_pow, map_ofNat, toZMod_lift, x₀, y₀]
          rw [← hub]; linear_combination hab)
        (by
          rw [e1]
          simp only [map_mul, map_ofNat, toZMod_lift, y₀]
          refine mul_ne_zero ?_ hb
          have : (6 : ZMod p) = 2 * 3 := by norm_num
          rw [this]; exact mul_ne_zero h2 h3)
      refine ⟨x₀, y, ?_⟩
      simp at hy
      linear_combination hy
    · have e0 : (X ^ 2 + C (3 * y₀ ^ 2 - 4 * u)).eval x₀ = x₀ ^ 2 + (3 * y₀ ^ 2 - 4 * u) := by
        simp
      have e1 : (X ^ 2 + C (3 * y₀ ^ 2 - 4 * u)).derivative.eval x₀ = 2 * x₀ := by
        rw [derivative_add, derivative_C, add_zero, derivative_X_pow]; simp
      obtain ⟨x, hx, -⟩ := hensel_simple (X ^ 2 + C (3 * y₀ ^ 2 - 4 * u)) x₀ (by
          rw [e0]
          simp only [map_add, map_mul, map_sub, map_pow, map_ofNat, toZMod_lift, x₀, y₀]
          rw [← hub]; linear_combination hab)
        (by
          rw [e1]
          simp only [map_mul, map_ofNat, toZMod_lift, x₀]
          exact mul_ne_zero h2 ha)
      refine ⟨x, y₀, ?_⟩
      simp at hx
      linear_combination hx
  -- `2` is a unit of `ℤ_p`
  obtain ⟨t, ht⟩ : ∃ t : ℤ_[p], 2 * t = 1 := by
    have : IsUnit (2 : ℤ_[p]) := (isUnit_iff_toZMod _).2 (by rw [map_ofNat]; exact h2)
    obtain ⟨v, hv⟩ := this
    exact ⟨↑v⁻¹, by rw [← hv]; simp⟩
  refine ⟨![(x - y) * t, 0, y, 0], ?_⟩
  simp [N4]
  linear_combination t ^ 2 * hxy + (-t * x * y - y ^ 2 * (1 + t) + u * (2 * t + 1)) * ht

/-- **Every unit of `ℤ_p` is a value of the reduced norm of `𝒪_p`** (every prime `p`). -/
theorem rep_unit (u : ℤ_[p]) (hu : IsUnit u) : ∃ n : Fin 4 → ℤ_[p], N4 n = u := by
  rcases (show p = 2 ∨ p = 3 ∨ 5 ≤ p by
    have := hp.out.two_le
    rcases (show p = 2 ∨ p = 3 ∨ p = 4 ∨ 5 ≤ p by omega) with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact absurd (h ▸ hp.out) (by decide)
    · exact Or.inr (Or.inr h)) with h | h | h
  · subst h; exact rep_two u hu
  · subst h; exact rep_three u hu
  · exact rep_ge5 h u hu

/-- **`1 + 3ℤ_3 ⊆ nrd(1 + 3𝒪_3)`**: a unit `u ≡ 1 mod 3` of `ℤ_3` is `x²` with `x ≡ 1 mod 3`. -/
theorem sq_three (u : ℤ_[3]) (hu : PadicInt.toZMod u = 1) :
    ∃ x : ℤ_[3], x ^ 2 = u ∧ PadicInt.toZMod x = 1 := by
  obtain ⟨x, hx, hx1⟩ := hensel_simple (X ^ 2 - C u) 1 (by simp [hu])
    (by simp only [derivative_sub, derivative_X_pow, derivative_C, sub_zero, eval_mul, eval_C,
          eval_pow, eval_X, one_pow, mul_one]; simp only [map_natCast]; decide)
  refine ⟨x, ?_, by simpa using hx1⟩
  simp only [eval_sub, eval_pow, eval_X, eval_C] at hx
  linear_combination hx

end ShimuraGlue
