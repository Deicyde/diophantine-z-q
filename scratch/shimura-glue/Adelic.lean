import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.Algebra.Quaternion
import Mathlib.Tactic.NoncommRing
import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter

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


/-! ## Adelic part: `B ⊗ 𝔸_f`, `𝒪̂`, the level groups and the reduced norm -/

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Rat.HeightOneSpectrum

instance instFactPrimes (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

/-- The finite places of `ℚ` (Mathlib's height-one primes of `ℤ`). -/
abbrev Place := HeightOneSpectrum ℤ

/-- **The finite adeles `𝔸_f` of `ℚ`** (Mathlib's `FiniteAdeleRing ℤ ℚ`). -/
abbrev Af := FiniteAdeleRing ℤ ℚ

/-- **`B ⊗_ℚ R` for `B = (2, −3 | ℚ)`**, as the quaternion algebra over `R` with the same structure
constants (for `R = ℚ` this is the kernel's `LeafQM.B`). -/
abbrev BR (R : Type*) [CommRing R] := QuaternionAlgebra R 2 0 (-3)

/-- `B ⊗_ℚ 𝔸_f`. -/
abbrev BAf := BR Af

/-- **The reduced norm** `nrd(x) = x·x̄` of `B ⊗ R` (`nrdQ_eq_mul_star`), as a monoid hom. -/
def nrdQ (R : Type*) [CommRing R] : BR R →* R where
  toFun x := x.re ^ 2 - 2 * x.imI ^ 2 + 3 * x.imJ ^ 2 - 6 * x.imK ^ 2
  map_one' := by simp
  map_mul' x y := by simp; ring

theorem nrdQ_apply {R : Type*} [CommRing R] (x : BR R) :
    nrdQ R x = x.re ^ 2 - 2 * x.imI ^ 2 + 3 * x.imJ ^ 2 - 6 * x.imK ^ 2 := rfl

/-- `nrd(x) = x x̄`: `nrdQ` is the reduced norm. -/
theorem nrdQ_eq_mul_star {R : Type*} [CommRing R] (x : BR R) :
    ((nrdQ R x : R) : BR R) = x * star x := by
  ext <;> simp only [QuaternionAlgebra.re_coe, QuaternionAlgebra.imI_coe, QuaternionAlgebra.imJ_coe,
    QuaternionAlgebra.imK_coe] <;> simp [nrdQ_apply] <;> ring

/-- `1/2` in a `ℚ`-algebra. -/
def half (R : Type*) [CommRing R] [Algebra ℚ R] : R := algebraMap ℚ R (1 / 2)

theorem two_mul_half (R : Type*) [CommRing R] [Algebra ℚ R] : 2 * half R = 1 := by
  rw [half, ← map_ofNat (algebraMap ℚ R) 2, ← map_mul]; norm_num

/-- The element `n₀ + n₁ i + n₂ (1+j)/2 + n₃ (i+k)/2` (the kernel's `LeafQM.ofInt` over `R`). -/
def ofQ {R : Type*} [CommRing R] [Algebra ℚ R] (n : Fin 4 → R) : BR R :=
  ⟨n 0 + half R * n 2, n 1 + half R * n 3, half R * n 2, half R * n 3⟩

/-- The multiplication table of `𝒪` in these coordinates (the kernel's `LeafQM.mulCoord` over `R`). -/
def mulCoordR {R : Type*} [CommRing R] (n m : Fin 4 → R) : Fin 4 → R :=
  ![m 0 * n 0 + (m 1 + m 1) * n 1 + (m 1 + m 1) * n 3 - m 2 * n 2 + (m 3 + m 3) * n 3,
    m 0 * n 1 + m 1 * n 0 + m 1 * n 2 - m 2 * n 3 + m 3 * n 2,
    m 0 * n 2 - (m 1 + m 1) * n 3 + m 2 * n 0 + m 2 * n 2 + (m 3 + m 3) * n 1,
    m 0 * n 3 - m 1 * n 2 + m 2 * n 1 + m 2 * n 3 + m 3 * n 0]

theorem ofQ_mul {R : Type*} [CommRing R] [Algebra ℚ R] (n m : Fin 4 → R) :
    ofQ n * ofQ m = ofQ (mulCoordR n m) := by
  have hh := two_mul_half R
  set h := half R
  ext <;> simp [ofQ, mulCoordR, h]
  · linear_combination (2 * n 3 * m 3 + 2 * n 3 * m 1 - n 2 * m 2 + 4 * h * n 3 * m 3
      - h * n 2 * m 2) * hh
  · linear_combination (-n 3 * m 2 + n 2 * m 3 + n 2 * m 1 - h * n 3 * m 2 + 2 * h * n 2 * m 3) * hh
  · linear_combination (h * n 2 * m 2) * hh
  · linear_combination (h * n 3 * m 2) * hh

theorem ofQ_add {R : Type*} [CommRing R] [Algebra ℚ R] (n m : Fin 4 → R) :
    ofQ n + ofQ m = ofQ (n + m) := by
  ext <;> simp [ofQ] <;> ring

theorem ofQ_neg {R : Type*} [CommRing R] [Algebra ℚ R] (n : Fin 4 → R) :
    -ofQ n = ofQ (-n) := by
  ext <;> simp [ofQ] <;> ring

theorem ofQ_one {R : Type*} [CommRing R] [Algebra ℚ R] : ofQ ![(1 : R), 0, 0, 0] = 1 := by
  ext <;> simp [ofQ]

theorem ofQ_zero {R : Type*} [CommRing R] [Algebra ℚ R] : ofQ (0 : Fin 4 → R) = 0 := by
  ext <;> simp [ofQ]

/-- The reduced norm in the coordinates of `ofQ` is `N4`. -/
theorem nrdQ_ofQ {R : Type*} [CommRing R] [Algebra ℚ R] (n : Fin 4 → R) :
    nrdQ R (ofQ n) = N4 n := by
  have hh := two_mul_half R
  set h := half R
  simp only [nrdQ_apply, ofQ, N4]
  linear_combination (-2 * n 3 ^ 2 + n 2 ^ 2 - 2 * n 1 * n 3 + n 0 * n 2 - 4 * h * n 3 ^ 2
    + 2 * h * n 2 ^ 2) * hh

/-- The conjugate in coordinates. -/
theorem star_ofQ {R : Type*} [CommRing R] [Algebra ℚ R] (n : Fin 4 → R) :
    star (ofQ n) = ofQ ![n 0 + n 2, -n 1, -n 2, -n 3] := by
  have hh := two_mul_half R
  set h := half R
  ext <;> simp [ofQ, h]
  · linear_combination (n 2) * hh
  · ring

/-- `x = ofQ n` recovers `n` (coordinates are unique). -/
theorem ofQ_coords {R : Type*} [CommRing R] [Algebra ℚ R] (x : BR R) :
    x = ofQ ![x.re - x.imJ, x.imI - x.imK, 2 * x.imJ, 2 * x.imK] := by
  have hh := two_mul_half R
  set h := half R
  ext <;> simp [ofQ, h]
  · linear_combination (-x.imJ) * hh
  · linear_combination (-x.imK) * hh
  · linear_combination (-x.imJ) * hh
  · linear_combination (-x.imK) * hh

/-! ### `ℤ̂`, `𝒪̂ = 𝒪 ⊗ ℤ̂` and the level groups -/

/-- **`ℤ̂ ⊆ 𝔸_f`**: the adeles integral at every place. -/
def Zhat : Subring Af where
  carrier := {a | ∀ v : Place, a v ∈ v.adicCompletionIntegers ℚ}
  mul_mem' ha hb v := mul_mem (ha v) (hb v)
  one_mem' v := one_mem _
  add_mem' ha hb v := add_mem (ha v) (hb v)
  zero_mem' v := zero_mem _
  neg_mem' ha v := neg_mem (ha v)

/-- Elements of a subring are coordinates of a family in it. -/
theorem exists_lift {S : Subring Af} {n : Fin 4 → Af} (hn : ∀ i, n i ∈ S) :
    ∃ n' : Fin 4 → S, n = fun i => S.subtype (n' i) :=
  ⟨fun i => ⟨n i, hn i⟩, rfl⟩

theorem mulCoordR_mem {n m : Fin 4 → Af} (hn : ∀ i, n i ∈ Zhat) (hm : ∀ i, m i ∈ Zhat) (j : Fin 4) :
    mulCoordR n m j ∈ Zhat := by
  obtain ⟨n', rfl⟩ := exists_lift hn
  obtain ⟨m', rfl⟩ := exists_lift hm
  have : mulCoordR (fun i => Zhat.subtype (n' i)) (fun i => Zhat.subtype (m' i)) j =
      Zhat.subtype (mulCoordR n' m' j) := by
    fin_cases j <;> simp [mulCoordR]
  rw [this]; exact (mulCoordR n' m' j).2

theorem N4_mem {S : Subring Af} {n : Fin 4 → Af} (hn : ∀ i, n i ∈ S) : N4 n ∈ S := by
  obtain ⟨n', rfl⟩ := exists_lift hn
  rw [← map_N4]; exact (N4 n').2

/-- **`𝒪̂ = 𝒪 ⊗ ℤ̂ ⊆ B ⊗ 𝔸_f`**: the `ℤ̂`-span of the basis `1, i, (1+j)/2, (i+k)/2` of `𝒪`. -/
def Ohat : Subring BAf where
  carrier := {x | ∃ n : Fin 4 → Af, (∀ i, n i ∈ Zhat) ∧ x = ofQ n}
  mul_mem' := by
    rintro _ _ ⟨n, hn, rfl⟩ ⟨m, hm, rfl⟩
    exact ⟨_, mulCoordR_mem hn hm, ofQ_mul n m⟩
  one_mem' := ⟨![1, 0, 0, 0], fun i => by fin_cases i <;> simp [Zhat.one_mem, Zhat.zero_mem],
    ofQ_one.symm⟩
  add_mem' := by
    rintro _ _ ⟨n, hn, rfl⟩ ⟨m, hm, rfl⟩
    exact ⟨n + m, fun i => Zhat.add_mem (hn i) (hm i), ofQ_add n m⟩
  zero_mem' := ⟨0, fun i => Zhat.zero_mem, ofQ_zero.symm⟩
  neg_mem' := by
    rintro _ ⟨n, hn, rfl⟩
    exact ⟨-n, fun i => Zhat.neg_mem (hn i), ofQ_neg n⟩


/-- **`ℤ̂^× ⊆ 𝔸_f^×`**. -/
def ZhatU : Subgroup Afˣ where
  carrier := {u | (u : Af) ∈ Zhat ∧ ((u⁻¹ : Afˣ) : Af) ∈ Zhat}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨by rw [Units.val_mul]; exact Zhat.mul_mem ha hb, ?_⟩
    rw [mul_inv_rev, Units.val_mul]; exact Zhat.mul_mem hb' ha'
  one_mem' := ⟨by simpa using Zhat.one_mem, by simpa using Zhat.one_mem⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    exact ⟨ha', by rw [inv_inv]; exact ha⟩

/-- **`U₃ = {u ∈ ℤ̂^× : u ≡ 1 mod 3ℤ̂}`** (at `p ≠ 3` the congruence is empty: `3 ∈ ℤ_p^×`). -/
def U3 : Subgroup Afˣ where
  carrier := {u | u ∈ ZhatU ∧ ∃ t ∈ Zhat, (u : Af) = 1 + 3 * t}
  mul_mem' := by
    rintro a b ⟨ha, s, hs, has⟩ ⟨hb, t, ht, hbt⟩
    refine ⟨ZhatU.mul_mem ha hb, s + t + 3 * s * t, ?_, ?_⟩
    · exact Zhat.add_mem (Zhat.add_mem hs ht)
        (Zhat.mul_mem (Zhat.mul_mem (by simpa using Zhat.natCast_mem 3) hs) ht)
    · rw [Units.val_mul, has, hbt]; ring
  one_mem' := ⟨ZhatU.one_mem, 0, Zhat.zero_mem, by simp⟩
  inv_mem' := by
    rintro a ⟨ha, t, ht, hat⟩
    refine ⟨ZhatU.inv_mem ha, -(((a⁻¹ : Afˣ) : Af) * t), Zhat.neg_mem (Zhat.mul_mem ha.2 ht), ?_⟩
    have : ((a⁻¹ : Afˣ) : Af) * (a : Af) = 1 := by simp
    linear_combination (-((a⁻¹ : Afˣ) : Af)) * hat + this

/-- **`𝒪̂^× ⊆ (B ⊗ 𝔸_f)^×`**: the level group of `X₆ = X₀(6,1)`. -/
def Kfull : Subgroup BAfˣ where
  carrier := {k | (k : BAf) ∈ Ohat ∧ ((k⁻¹ : BAfˣ) : BAf) ∈ Ohat}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨by rw [Units.val_mul]; exact Ohat.mul_mem ha hb, ?_⟩
    rw [mul_inv_rev, Units.val_mul]; exact Ohat.mul_mem hb' ha'
  one_mem' := ⟨by simpa using Ohat.one_mem, by simpa using Ohat.one_mem⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    exact ⟨ha', by rw [inv_inv]; exact ha⟩

/-- **`K₃ = ker(𝒪̂^× → (𝒪̂/3𝒪̂)^×) = {k ∈ 𝒪̂^× : k ≡ 1 mod 3𝒪̂}`**: the level group of `Y₃` (the
level-3 structures of the kernel's `Level3`: `η : 𝒪/3𝒪 ≅ A[3]`, `𝒪`-linear). -/
def K3 : Subgroup BAfˣ where
  carrier := {k | k ∈ Kfull ∧ ∃ y ∈ Ohat, (k : BAf) = 1 + 3 * y}
  mul_mem' := by
    rintro a b ⟨ha, y, hy, hay⟩ ⟨hb, z, hz, hbz⟩
    refine ⟨Kfull.mul_mem ha hb, y + z + 3 * (y * z), ?_, ?_⟩
    · exact Ohat.add_mem (Ohat.add_mem hy hz)
        (Ohat.mul_mem (by simpa using Ohat.natCast_mem 3) (Ohat.mul_mem hy hz))
    · rw [Units.val_mul, hay, hbz]; noncomm_ring
  one_mem' := ⟨Kfull.one_mem, 0, Ohat.zero_mem, by simp⟩
  inv_mem' := by
    rintro a ⟨ha, y, hy, hay⟩
    refine ⟨Kfull.inv_mem ha, -(((a⁻¹ : BAfˣ) : BAf) * y), Ohat.neg_mem (Ohat.mul_mem ha.2 hy), ?_⟩
    have h1 : ((a⁻¹ : BAfˣ) : BAf) * (a : BAf) = 1 := by simp
    calc ((a⁻¹ : BAfˣ) : BAf) = ((a⁻¹ : BAfˣ) : BAf) * (1 + 3 * y) - ((a⁻¹ : BAfˣ) : BAf) * (3 * y) := by
          noncomm_ring
      _ = 1 + 3 * -(((a⁻¹ : BAfˣ) : BAf) * y) := by
          rw [← hay, h1]
          have : ((a⁻¹ : BAfˣ) : BAf) * (3 * y) = 3 * (((a⁻¹ : BAfˣ) : BAf) * y) := by
            rw [← mul_assoc, ← mul_assoc, (Commute.ofNat_right _ 3).eq]
          rw [this]; noncomm_ring

/-- The positive rationals `ℚ^×_{>0} ⊆ 𝔸_f^×`. -/
def posQ : Subgroup ℚˣ where
  carrier := {q | 0 < (q : ℚ)}
  mul_mem' ha hb := by simp only [Set.mem_setOf_eq, Units.val_mul]; exact mul_pos ha hb
  one_mem' := by simp
  inv_mem' ha := by simp only [Set.mem_setOf_eq, Units.val_inv_eq_inv_val]; exact inv_pos.2 ha

def posRat : Subgroup Afˣ := posQ.map (FiniteAdeleRing.unitEmbedding ℤ ℚ)

/-- The reduced norm on units, `(B ⊗ 𝔸_f)^× → 𝔸_f^×`. -/
def nrdU : BAfˣ →* Afˣ := Units.map (nrdQ Af)

/-- **The double coset space `ℚ^×_{>0} \ 𝔸_f^× / nrd(K)`** (an abelian group: `𝔸_f^×` is commutative). -/
abbrev Pi0 (K : Subgroup BAfˣ) := Afˣ ⧸ (posRat ⊔ K.map nrdU)

/-! ### `nrd(𝒪̂^×) ⊆ ℤ̂^×`, `nrd(K₃) ⊆ U₃` -/

theorem nrd_mem_Zhat {x : BAf} (hx : x ∈ Ohat) : nrdQ Af x ∈ Zhat := by
  obtain ⟨n, hn, rfl⟩ := hx
  rw [nrdQ_ofQ]; exact N4_mem hn

theorem nrd_Kfull_le : Kfull.map nrdU ≤ ZhatU := by
  rintro _ ⟨k, ⟨hk, hk'⟩, rfl⟩
  refine ⟨nrd_mem_Zhat hk, ?_⟩
  rw [← map_inv]; exact nrd_mem_Zhat hk'

theorem nrd_one_add_three {R : Type*} [CommRing R] [Algebra ℚ R] (m : Fin 4 → R) :
    nrdQ R (1 + 3 * ofQ m) = 1 + 3 * (2 * m 0 + m 2 + 3 * N4 m) := by
  have hh := two_mul_half R
  set h := half R
  have e : (1 + 3 * ofQ m : BR R) = ⟨1 + 3 * (m 0 + h * m 2), 3 * (m 1 + h * m 3), 3 * (h * m 2),
      3 * (h * m 3)⟩ := by
    ext <;> simp [ofQ, h, QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
      QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  rw [e, nrdQ_apply]; simp only [N4]
  linear_combination (-18 * m 3 ^ 2 + 3 * m 2 + 9 * m 2 ^ 2 - 18 * m 1 * m 3 + 9 * m 0 * m 2
    - 36 * h * m 3 ^ 2 + 18 * h * m 2 ^ 2) * hh

theorem nrd_K3_le : K3.map nrdU ≤ U3 := by
  rintro _ ⟨k, ⟨hk, y, ⟨m, hm, rfl⟩, hky⟩, rfl⟩
  refine ⟨nrd_Kfull_le ⟨k, hk, rfl⟩, 2 * m 0 + m 2 + 3 * N4 m, ?_, ?_⟩
  · have h2 : (2 : Af) ∈ Zhat := by simpa using Zhat.natCast_mem 2
    have h3 : (3 : Af) ∈ Zhat := by simpa using Zhat.natCast_mem 3
    exact Zhat.add_mem (Zhat.add_mem (Zhat.mul_mem h2 (hm 0)) (hm 2)) (Zhat.mul_mem h3 (N4_mem hm))
  · change nrdQ Af (k : BAf) = _
    rw [hky, nrd_one_add_three]


/-! ### Local coordinates and the surjectivity of `nrd` -/

/-- Evaluation of a finite adele at a place, as a ring hom. -/
def ev (v : Place) : Af →+* v.adicCompletion ℚ where
  toFun a := a v
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem ev_apply (v : Place) (a : Af) : ev v a = a v := rfl

/-- The local isomorphism `𝒪_v ≅ ℤ_p` (Mathlib's `padicIntEquiv`), as a ring isomorphism. -/
def locZ (v : Place) : v.adicCompletionIntegers ℚ ≃+* ℤ_[primesEquiv v] :=
  (adicCompletionIntegers.padicIntEquiv (R := ℤ) v : v.adicCompletionIntegers ℚ ≃+* ℤ_[primesEquiv v])

/-- An integral adele from a family of `p`-adic integers. -/
def adeleHom : (∀ v : Place, ℤ_[primesEquiv v]) →+* Af where
  toFun f := ⟨fun v => (((locZ v).symm (f v) : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ),
    Filter.Eventually.of_forall fun v => ((locZ v).symm (f v)).2⟩
  map_one' := by
    apply FiniteAdeleRing.ext; intro v
    change (((locZ v).symm 1 : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ) = 1
    simp
  map_mul' f g := by
    apply FiniteAdeleRing.ext; intro v
    change (((locZ v).symm (f v * g v) : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ) = _
    simp; rfl
  map_zero' := by
    apply FiniteAdeleRing.ext; intro v
    change (((locZ v).symm 0 : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ) = 0
    simp
  map_add' f g := by
    apply FiniteAdeleRing.ext; intro v
    change (((locZ v).symm (f v + g v) : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ) = _
    simp; rfl

theorem adeleHom_apply (f : ∀ v : Place, ℤ_[primesEquiv v]) (v : Place) :
    adeleHom f v = (((locZ v).symm (f v) : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ) := rfl

theorem adeleHom_mem (f : ∀ v : Place, ℤ_[primesEquiv v]) : adeleHom f ∈ Zhat :=
  fun v => ((locZ v).symm (f v)).2

/-- The `p`-adic coordinate of an integral adele. -/
def locA {a : Af} (ha : a ∈ Zhat) (v : Place) : ℤ_[primesEquiv v] := locZ v ⟨a v, ha v⟩

theorem adeleHom_locA {a : Af} (ha : a ∈ Zhat) : adeleHom (locA ha) = a := by
  apply FiniteAdeleRing.ext; intro v
  simp [adeleHom_apply, locA]

theorem isUnit_locA {u : Afˣ} (hu : u ∈ ZhatU) (v : Place) : IsUnit (locA hu.1 v) := by
  refine IsUnit.of_mul_eq_one (locA hu.2 v) ?_
  rw [locA, locA, ← map_mul]
  have : (⟨(u : Af) v, hu.1 v⟩ * ⟨((u⁻¹ : Afˣ) : Af) v, hu.2 v⟩ : v.adicCompletionIntegers ℚ) = 1 := by
    apply Subtype.ext
    change (u : Af) v * ((u⁻¹ : Afˣ) : Af) v = 1
    rw [← ev_apply, ← ev_apply, ← map_mul, Units.mul_inv, map_one]
  rw [this, map_one]

theorem N4_adeleHom (n : ∀ v : Place, Fin 4 → ℤ_[primesEquiv v]) :
    N4 (fun i => adeleHom (fun v => n v i)) = adeleHom (fun v => N4 (n v)) := by
  rw [show (fun v => N4 (n v)) = N4 (fun i => fun v => n v i) from rfl, map_N4]

theorem coe_eq_ofQ {R : Type*} [CommRing R] [Algebra ℚ R] (a : R) :
    (a : BR R) = ofQ ![a, 0, 0, 0] := by
  ext <;> simp [ofQ]

theorem nrdQ_star {R : Type*} [CommRing R] (x : BR R) : nrdQ R (star x) = nrdQ R x := by
  simp [nrdQ_apply]

theorem vec4_mem {S : Subring Af} {a b c d : Af} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (hd : d ∈ S) : ∀ i, ![a, b, c, d] i ∈ S := by
  intro i; fin_cases i
  exacts [ha, hb, hc, hd]

/-- A unit of `B ⊗ 𝔸_f` in `𝒪̂^×` from an element of `𝒪̂` whose reduced norm is in `ℤ̂^×`. -/
theorem exists_unit_of_nrd {k : BAf} (hk : k ∈ Ohat) {u : Afˣ} (hu : u ∈ ZhatU)
    (hnk : nrdQ Af k = u) : ∃ k' : BAfˣ, k' ∈ Kfull ∧ (k' : BAf) = k ∧ nrdU k' = u := by
  set a : Af := ((u⁻¹ : Afˣ) : Af)
  have h1 : k * (star k * (a : BAf)) = 1 := by
    rw [← mul_assoc, ← nrdQ_eq_mul_star, hnk, ← QuaternionAlgebra.coe_mul, Units.mul_inv]; rfl
  have h2 : (star k * (a : BAf)) * k = 1 := by
    rw [mul_assoc, QuaternionAlgebra.coe_commutes a k, ← mul_assoc]
    have : star k * k = ((nrdQ Af k : Af) : BAf) := by
      rw [← nrdQ_star, nrdQ_eq_mul_star, star_star]
    rw [this, hnk, ← QuaternionAlgebra.coe_mul, Units.mul_inv]; rfl
  refine ⟨⟨k, star k * (a : BAf), h1, h2⟩, ⟨hk, ?_⟩, rfl, ?_⟩
  · change star k * (a : BAf) ∈ Ohat
    obtain ⟨n, hn, rfl⟩ := hk
    exact Ohat.mul_mem ⟨_, vec4_mem (Zhat.add_mem (hn 0) (hn 2)) (Zhat.neg_mem (hn 1))
      (Zhat.neg_mem (hn 2)) (Zhat.neg_mem (hn 3)), star_ofQ n⟩
      ⟨_, vec4_mem hu.2 Zhat.zero_mem Zhat.zero_mem Zhat.zero_mem, coe_eq_ofQ a⟩
  · apply Units.ext; exact hnk

/-- **`nrd(𝒪̂^×) ⊇ ℤ̂^×`** (local representations `rep_unit` at every place). -/
theorem ZhatU_le : ZhatU ≤ Kfull.map nrdU := by
  intro u hu
  choose n hn using fun v => rep_unit (p := primesEquiv v) (locA hu.1 v) (isUnit_locA hu v)
  set m : Fin 4 → Af := fun i => adeleHom (fun v => n v i)
  have hN : nrdQ Af (ofQ m) = u := by
    rw [nrdQ_ofQ, N4_adeleHom]
    simp only [hn]; exact adeleHom_locA hu.1
  obtain ⟨k, hk, -, hku⟩ := exists_unit_of_nrd ⟨m, fun i => adeleHom_mem _, rfl⟩ hu hN
  exact ⟨k, hk, hku⟩


/-- `e₀ = (1, 0, 0, 0)`, the coordinates of `1`. -/
def e0 : Fin 4 → ℤ := ![1, 0, 0, 0]

/-- **Local representations congruent to `1` mod 3**: a unit `u` of `ℤ_p` (with `u ≡ 1 mod 3` if
`p = 3`) is `N4(e₀ + 3n')` for some `n'` (for `p ≠ 3`, `3 ∈ ℤ_p^×`; for `p = 3`, `sq_three`). -/
theorem rep_unit3 {p : ℕ} [Fact p.Prime] (u : ℤ_[p]) (hu : IsUnit u)
    (h3 : p = 3 → PadicInt.toZMod u = 1) :
    ∃ n' : Fin 4 → ℤ_[p], N4 (fun i => ((e0 i : ℤ) : ℤ_[p]) + 3 * n' i) = u := by
  by_cases hp3 : p = 3
  · subst hp3
    obtain ⟨x, hx, hx1⟩ := sq_three u (h3 rfl)
    have : PadicInt.toZMod (x - 1) = 0 := by rw [map_sub, hx1, map_one, sub_self]
    obtain ⟨y, hy⟩ := (PadicInt.norm_lt_one_iff_dvd _).1 ((norm_lt_one_iff_toZMod _).2 this)
    refine ⟨![y, 0, 0, 0], ?_⟩
    simp only [N4, e0]
    simp
    push_cast at hy
    linear_combination hx - (1 + 3 * y + x) * hy
  · obtain ⟨n, hn⟩ := rep_unit u hu
    have h3u : IsUnit (3 : ℤ_[p]) := by
      rw [isUnit_iff_toZMod, map_ofNat, ← Nat.cast_ofNat, Ne, ZMod.natCast_eq_zero_iff]
      intro hd
      exact hp3 ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_three).1 hd)
    obtain ⟨w, hw⟩ := h3u
    refine ⟨fun i => (n i - ((e0 i : ℤ) : ℤ_[p])) * ↑w⁻¹, ?_⟩
    convert hn using 2
    funext i
    have : (3 : ℤ_[p]) * ↑w⁻¹ = 1 := by rw [← hw]; simp
    linear_combination (n i - ((e0 i : ℤ) : ℤ_[p])) * this

theorem ofQ_e0 {R : Type*} [CommRing R] [Algebra ℚ R] (m : Fin 4 → R) :
    ofQ (fun i => ((e0 i : ℤ) : R) + 3 * m i) = 1 + 3 * ofQ m := by
  ext <;> simp [ofQ, e0, QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
      QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] <;> ring

theorem three_mem_Zhat : (3 : Af) ∈ Zhat := by simpa using Zhat.natCast_mem 3

/-- **`nrd(K₃) ⊇ U₃`**. -/
theorem U3_le : U3 ≤ K3.map nrdU := by
  rintro u ⟨hu, t, ht, hut⟩
  have hloc : ∀ v : Place, (primesEquiv v : ℕ) = 3 → PadicInt.toZMod (locA hu.1 v) = 1 := by
    intro v hv
    have : locA hu.1 v = 1 + 3 * locA ht v := by
      rw [locA, locA, ← map_ofNat (locZ v) 3, ← map_one (locZ v), ← map_mul, ← map_add]
      congr 1; apply Subtype.ext
      change (u : Af) v = 1 + 3 * t v
      rw [hut]; change ev v (1 + 3 * t) = 1 + 3 * ev v t
      rw [map_add, map_mul, map_one, map_ofNat]
    rw [this, map_add, map_mul, map_one, map_ofNat]
    have h30 : (3 : ZMod (primesEquiv v : ℕ)) = 0 := by
      rw [← Nat.cast_ofNat, ZMod.natCast_eq_zero_iff, hv]
    rw [h30, zero_mul, add_zero]
  choose n' hn' using fun v => rep_unit3 (p := primesEquiv v) (locA hu.1 v) (isUnit_locA hu v) (hloc v)
  set m' : Fin 4 → Af := fun i => adeleHom (fun v => n' v i)
  have hm : (fun i => ((e0 i : ℤ) : Af) + 3 * m' i) =
      fun i => adeleHom (fun v => ((e0 i : ℤ) : ℤ_[primesEquiv v]) + 3 * n' v i) := by
    funext i
    rw [show (fun v => ((e0 i : ℤ) : ℤ_[primesEquiv v]) + 3 * n' v i) =
      (((e0 i : ℤ) : ∀ v : Place, ℤ_[primesEquiv v]) + 3 * fun v => n' v i) from rfl]
    rw [map_add, map_mul, map_intCast, map_ofNat]
  have hN : nrdQ Af (ofQ (fun i => ((e0 i : ℤ) : Af) + 3 * m' i)) = u := by
    rw [nrdQ_ofQ, hm, N4_adeleHom]; simp only [hn']; exact adeleHom_locA hu.1
  have hmem : ∀ i, ((e0 i : ℤ) : Af) + 3 * m' i ∈ Zhat := fun i =>
    Zhat.add_mem (intCast_mem Zhat _) (Zhat.mul_mem three_mem_Zhat (adeleHom_mem _))
  obtain ⟨k, hk, hkk, hku⟩ := exists_unit_of_nrd ⟨_, hmem, rfl⟩ hu hN
  refine ⟨k, ⟨hk, ofQ m', ⟨m', fun i => adeleHom_mem _, rfl⟩, ?_⟩, hku⟩
  rw [hkk, ofQ_e0]


/-! ### `𝔸_f^× = ℚ^×_{>0} · ℤ̂^×`, with unique factors -/

/-- The local isomorphism `ℚ_v ≅ ℚ_p` (Mathlib's `padicEquiv`), as a ring isomorphism. -/
def locQ (v : Place) : v.adicCompletion ℚ ≃+* ℚ_[primesEquiv v] :=
  (adicCompletion.padicEquiv (R := ℤ) v : v.adicCompletion ℚ ≃+* ℚ_[primesEquiv v])

theorem locQ_rat (v : Place) (q : ℚ) :
    locQ v (algebraMap ℚ (v.adicCompletion ℚ) q) = (q : ℚ_[primesEquiv v]) := by
  change adicCompletion.padicEquiv (R := ℤ) v (algebraMap ℚ _ q) = _
  rw [AlgHomClass.commutes, eq_ratCast]

theorem mem_iff_norm (v : Place) (x : v.adicCompletion ℚ) :
    x ∈ v.adicCompletionIntegers ℚ ↔ ‖locQ v x‖ ≤ 1 := by
  constructor
  · intro hx; exact (adicCompletion.padicEquiv_bijOn (R := ℤ) v).mapsTo hx
  · intro hx
    obtain ⟨x', hx', he⟩ := (adicCompletion.padicEquiv_bijOn (R := ℤ) v).surjOn
      (show locQ v x ∈ PadicInt.subring (primesEquiv v) from hx)
    rwa [(adicCompletion.padicEquiv (R := ℤ) v).injective he] at hx'

/-- `‖a_v‖_v` (the `p`-adic norm of the `v`-component). -/
def nrm (v : Place) (a : Af) : ℝ := ‖locQ v (a v)‖

theorem nrm_mul (v : Place) (a b : Af) : nrm v (a * b) = nrm v a * nrm v b := by
  simp only [nrm, ← ev_apply, map_mul, norm_mul]

theorem nrm_one (v : Place) : nrm v 1 = 1 := by
  simp only [nrm, ← ev_apply, map_one, norm_one]

theorem nrm_unit (s : Afˣ) (v : Place) : nrm v s * nrm v ↑s⁻¹ = 1 := by
  rw [← nrm_mul, Units.mul_inv, nrm_one]

theorem nrm_eq_one_of_mem {s : Afˣ} {v : Place} (h1 : (s : Af) v ∈ v.adicCompletionIntegers ℚ)
    (h2 : ((s⁻¹ : Afˣ) : Af) v ∈ v.adicCompletionIntegers ℚ) : nrm v s = 1 := by
  have a := (mem_iff_norm v _).1 h1
  have b := (mem_iff_norm v _).1 h2
  have c := nrm_unit s v
  have d : 0 ≤ nrm v ↑s⁻¹ := norm_nonneg _
  change nrm v s ≤ 1 at a
  change nrm v ↑s⁻¹ ≤ 1 at b
  by_contra hne
  have hlt : nrm v s < 1 := lt_of_le_of_ne a hne
  have : nrm v s * nrm v ↑s⁻¹ < 1 :=
    calc _ ≤ nrm v s * 1 := mul_le_mul_of_nonneg_left b (norm_nonneg _)
      _ < 1 := by linarith
  linarith

theorem mem_ZhatU_iff (s : Afˣ) : s ∈ ZhatU ↔ ∀ v, nrm v s = 1 := by
  constructor
  · rintro ⟨h1, h2⟩ v; exact nrm_eq_one_of_mem (h1 v) (h2 v)
  · intro h
    refine ⟨fun v => (mem_iff_norm v _).2 (h v).le, fun v => (mem_iff_norm v _).2 ?_⟩
    have := nrm_unit s v; rw [h v, one_mul] at this; exact this.le

/-- The embedding `ℚ^× → 𝔸_f^×`. -/
abbrev emb : ℚˣ →* Afˣ := FiniteAdeleRing.unitEmbedding ℤ ℚ

theorem nrm_emb (v : Place) (q : ℚˣ) : nrm v (emb q) = ‖((q : ℚ) : ℚ_[primesEquiv v])‖ := by
  unfold nrm
  rw [show ((emb q : Afˣ) : Af) v = algebraMap ℚ (v.adicCompletion ℚ) (q : ℚ) from rfl, locQ_rat]

theorem norm_prime_ne {p q : Nat.Primes} (h : p ≠ q) : ‖((q : ℕ) : ℚ_[p])‖ = 1 := by
  rw [Padic.norm_natCast_eq_one_iff]
  exact (Nat.coprime_primes p.2 q.2).2 fun e => h (Subtype.ext e)

/-- **Existence**: every `s ∈ 𝔸_f^×` is `q·u` with `q ∈ ℚ^×_{>0}`, `u ∈ ℤ̂^×`. -/
theorem exists_decomp (s : Afˣ) : ∃ q : ℚˣ, q ∈ posQ ∧ s * (emb q)⁻¹ ∈ ZhatU := by
  classical
  have hfin : {v : Place | ¬ ((s : Af) v ∈ v.adicCompletionIntegers ℚ ∧
      ((s⁻¹ : Afˣ) : Af) v ∈ v.adicCompletionIntegers ℚ)}.Finite :=
    Filter.eventually_cofinite.1 ((FiniteAdeleRing.cofinite_mem_adicCompletionIntegers (s : Af)).and
      (FiniteAdeleRing.cofinite_mem_adicCompletionIntegers ((s⁻¹ : Afˣ) : Af)))
  set S := hfin.toFinset
  set e : Place → ℤ := fun v => Padic.valuation (locQ v ((s : Af) v))
  set q : ℚ := ∏ v ∈ S, (((primesEquiv v : ℕ) : ℚ) ^ (e v)) with hqdef
  have hq : 0 < q := Finset.prod_pos fun v _ => zpow_pos (by exact_mod_cast (primesEquiv v).2.pos) _
  refine ⟨Units.mk0 q hq.ne', hq, ?_⟩
  rw [mem_ZhatU_iff]; intro w
  have hqw : ‖((q : ℚ) : ℚ_[primesEquiv w])‖ =
      if w ∈ S then ((primesEquiv w : ℕ) : ℝ) ^ (-e w) else 1 := by
    rw [hqdef]; push_cast; rw [norm_prod]
    rw [Finset.prod_congr rfl (g := fun v => if v = w then ((primesEquiv w : ℕ) : ℝ) ^ (-e w) else 1)]
    · exact Finset.prod_ite_eq' S w _
    · intro v _
      by_cases hvw : v = w
      · subst hvw; simp only [if_true]; exact Padic.norm_p_zpow _
      · rw [if_neg hvw, norm_zpow, norm_prime_ne, one_zpow]
        exact fun h => hvw (primesEquiv.injective h.symm)
  have hsw : (s : Af) w ≠ 0 := by
    intro h0
    have := congrArg (ev w) (Units.mul_inv s)
    rw [map_mul, map_one, ev_apply, ev_apply, h0, zero_mul] at this
    exact zero_ne_one this
  have hinv : nrm w ((emb (Units.mk0 q hq.ne'))⁻¹ : Afˣ) = ‖((q : ℚ) : ℚ_[primesEquiv w])‖⁻¹ := by
    rw [← map_inv, nrm_emb]; simp
  rw [Units.val_mul, nrm_mul, hinv, hqw]
  by_cases hw : w ∈ S
  · rw [if_pos hw]
    have : nrm w s = ((primesEquiv w : ℕ) : ℝ) ^ (-e w) := by
      simp only [nrm, e]
      exact Padic.norm_eq_zpow_neg_valuation ((_root_.map_ne_zero _).2 hsw)
    rw [this, mul_inv_cancel₀ (_root_.zpow_ne_zero _ (by exact_mod_cast (primesEquiv w).2.ne_zero))]
  · rw [if_neg hw, inv_one, mul_one]
    have hw' : w ∉ {v : Place | ¬ ((s : Af) v ∈ v.adicCompletionIntegers ℚ ∧
        ((s⁻¹ : Afˣ) : Af) v ∈ v.adicCompletionIntegers ℚ)} := by
      simpa [S] using hw
    simp only [Set.mem_setOf_eq, not_not] at hw'
    exact nrm_eq_one_of_mem hw'.1 hw'.2

/-- **Uniqueness**: `ℚ^×_{>0} ∩ ℤ̂^× = 1`. -/
theorem posQ_ZhatU {q : ℚˣ} (hq : q ∈ posQ) (h : emb q ∈ ZhatU) : q = 1 := by
  have key : ∀ p : Nat.Primes, ‖((q : ℚ) : ℚ_[p])‖ = 1 := by
    intro p
    obtain ⟨w, rfl⟩ := (primesEquiv (R := ℤ)).surjective p
    rw [← nrm_emb]; exact (mem_ZhatU_iff _).1 h w
  have hq0 : 0 < (q : ℚ) := hq
  have hnorm : ∀ p : Nat.Primes, ‖(((q : ℚ).num : ℤ) : ℚ_[p])‖ = ‖(((q : ℚ).den : ℕ) : ℚ_[p])‖ := by
    intro p
    have h1 := key p
    rw [Rat.cast_def, norm_div] at h1
    have hd : ‖(((q : ℚ).den : ℕ) : ℚ_[p])‖ ≠ 0 := by
      rw [norm_ne_zero_iff]; exact_mod_cast (q : ℚ).den_nz
    field_simp at h1; linarith
  have hnum : (q : ℚ).num.natAbs = 1 := by
    by_contra hne
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
    haveI : Fact p.Prime := ⟨hp⟩
    have h1 : ‖(((q : ℚ).num : ℤ) : ℚ_[p])‖ < 1 := by
      rw [Padic.norm_intCast_lt_one_iff]; exact Int.natCast_dvd.2 hpd
    have h2 : ‖(((q : ℚ).den : ℕ) : ℚ_[p])‖ = 1 := by
      rw [Padic.norm_natCast_eq_one_iff]
      exact Nat.Coprime.coprime_dvd_left hpd (q : ℚ).reduced
    have : ‖(((q : ℚ).num : ℤ) : ℚ_[p])‖ = ‖(((q : ℚ).den : ℕ) : ℚ_[p])‖ := hnorm ⟨p, hp⟩
    rw [h2] at this; linarith
  have hden : (q : ℚ).den = 1 := by
    by_contra hne
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
    haveI : Fact p.Prime := ⟨hp⟩
    have h1 : ‖(((q : ℚ).den : ℕ) : ℚ_[p])‖ < 1 := by
      rw [Padic.norm_natCast_lt_one_iff]; exact hpd
    have h2 : ‖(((q : ℚ).num : ℤ) : ℚ_[p])‖ = 1 := by
      have : ((q : ℚ).num : ℤ) = 1 ∨ ((q : ℚ).num : ℤ) = -1 := Int.natAbs_eq_iff.1 hnum |>.imp
        (by simp) (by simp)
      rcases this with h | h <;> rw [h] <;> simp
    have : ‖(((q : ℚ).num : ℤ) : ℚ_[p])‖ = ‖(((q : ℚ).den : ℕ) : ℚ_[p])‖ := hnorm ⟨p, hp⟩
    rw [h2] at this; linarith
  have hnum' : (q : ℚ).num = 1 := by
    have := Rat.num_pos.2 hq0
    omega
  apply Units.ext
  rw [Units.val_one, ← Rat.num_div_den (q : ℚ), hnum', hden]; norm_num

theorem posQ_div {q q' : ℚˣ} (hq : q ∈ posQ) (hq' : q' ∈ posQ) : q * q'⁻¹ ∈ posQ :=
  posQ.mul_mem hq (posQ.inv_mem hq')

/-- Uniqueness of the factorization `s = q·u`. -/
theorem decomp_unique {q q' : ℚˣ} (hq : q ∈ posQ) (hq' : q' ∈ posQ) {u u' : Afˣ} (hu : u ∈ ZhatU)
    (hu' : u' ∈ ZhatU) (h : emb q * u = emb q' * u') : q = q' := by
  have : emb (q * q'⁻¹) = u' * u⁻¹ := by
    rw [map_mul, map_inv, eq_mul_inv_iff_mul_eq, mul_right_comm, h, mul_comm (emb q') u', mul_assoc,
      mul_inv_cancel, mul_one]
  have h1 := posQ_ZhatU (posQ_div hq hq') (this ▸ ZhatU.mul_mem hu' (ZhatU.inv_mem hu))
  rw [mul_inv_eq_one] at h1; exact h1

end ShimuraGlue
