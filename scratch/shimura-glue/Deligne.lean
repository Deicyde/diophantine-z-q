import ZInQKernel.HDecomp.QM.Leaves
import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.Algebra.Quaternion
import Mathlib.Tactic.NoncommRing
import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed


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

/- Over the full kernel (e.g. `ZInQKernel.OneProof.H.TailK`) instance search finds
`DivisionRing.toRatAlgebra` for `Algebra ℚ (v.adicCompletion ℚ)`, which is not reducibly defeq to the
instance `instAlgebraAdicCompletion` in the type of Mathlib's `padicEquiv`; prefer the latter here. -/
attribute [local instance 2000] instAlgebraAdicCompletion

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
    locQ v ((algebraMap ℚ Af q) v) = (q : ℚ_[primesEquiv v]) := by
  have : (algebraMap ℚ Af q) v = (q : v.adicCompletion ℚ) :=
    eq_ratCast ((ev v).comp (algebraMap ℚ Af)) q
  rw [this, map_ratCast]

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
  rw [show ((emb q : Afˣ) : Af) = algebraMap ℚ Af (q : ℚ) from rfl, locQ_rat]

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


/-! ### The factor maps `s ↦ (q, u)` -/

/-- The `ℚ^×_{>0}`-factor of `s ∈ 𝔸_f^×`. -/
noncomputable def dq (s : Afˣ) : ℚˣ := (exists_decomp s).choose

theorem dq_pos (s : Afˣ) : dq s ∈ posQ := (exists_decomp s).choose_spec.1

/-- The `ℤ̂^×`-factor of `s ∈ 𝔸_f^×`. -/
noncomputable def du (s : Afˣ) : Afˣ := s * (emb (dq s))⁻¹

theorem du_mem (s : Afˣ) : du s ∈ ZhatU := (exists_decomp s).choose_spec.2

theorem emb_dq_mul_du (s : Afˣ) : emb (dq s) * du s = s := by
  rw [du, mul_comm s, ← mul_assoc, mul_inv_cancel, one_mul]

theorem dq_mul (s t : Afˣ) : dq (s * t) = dq s * dq t :=
  decomp_unique (dq_pos _) (posQ.mul_mem (dq_pos s) (dq_pos t)) (du_mem _)
    (ZhatU.mul_mem (du_mem s) (du_mem t)) (by
      rw [emb_dq_mul_du, map_mul, mul_mul_mul_comm, emb_dq_mul_du, emb_dq_mul_du])

theorem du_mul (s t : Afˣ) : du (s * t) = du s * du t := by
  rw [du, du, du, dq_mul, map_mul, mul_inv]; ac_rfl

theorem dq_of_mem {u : Afˣ} (hu : u ∈ ZhatU) : dq u = 1 :=
  decomp_unique (dq_pos u) posQ.one_mem (du_mem u) hu (by rw [emb_dq_mul_du, map_one, one_mul])

theorem du_of_mem {u : Afˣ} (hu : u ∈ ZhatU) : du u = u := by
  rw [du, dq_of_mem hu, map_one, inv_one, mul_one]

theorem du_emb {q : ℚˣ} (hq : q ∈ posQ) : du (emb q) = 1 := by
  have : dq (emb q) = q :=
    decomp_unique (dq_pos _) hq (du_mem _) ZhatU.one_mem (by rw [emb_dq_mul_du, mul_one])
  rw [du, this, mul_inv_cancel]

/-- `s ↦ u` as a hom `𝔸_f^× → ℤ̂^×`. -/
noncomputable def duHom : Afˣ →* ZhatU where
  toFun s := ⟨du s, du_mem s⟩
  map_one' := Subtype.ext (du_of_mem ZhatU.one_mem)
  map_mul' s t := Subtype.ext (du_mul s t)

/-! ### Reduction mod 3 and the character `χ : 𝔸_f^× → (ℤ/3)^×` -/

/-- The place `3`. -/
noncomputable def v3 : Place := primesEquiv.symm ⟨3, Nat.prime_three⟩

theorem v3_spec : (primesEquiv v3 : ℕ) = 3 :=
  congrArg Subtype.val ((primesEquiv (R := ℤ)).apply_symm_apply ⟨3, Nat.prime_three⟩)

/-- Restriction of an integral adele to `𝒪_v`. -/
def evZ (v : Place) : Zhat →+* v.adicCompletionIntegers ℚ where
  toFun a := ⟨(a : Af) v, a.2 v⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl
  map_zero' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl

/-- **Reduction mod 3**: `ℤ̂ → ℤ_3 → ℤ/3`. -/
noncomputable def r3 : Zhat →+* ZMod 3 :=
  (ZMod.ringEquivCongr v3_spec : ZMod (primesEquiv v3 : ℕ) →+* ZMod 3).comp
    (PadicInt.toZMod.comp ((locZ v3 : _ →+* ℤ_[primesEquiv v3]).comp (evZ v3)))

theorem r3_apply (a : Zhat) : r3 a = ZMod.ringEquivCongr v3_spec (PadicInt.toZMod (locA a.2 v3)) := rfl

/-- `ℤ̂^× → ℤ̂ˣ` (units of the subring). -/
def toZhatUnits : ZhatU →* Zhatˣ where
  toFun u := ⟨⟨u.1, u.2.1⟩, ⟨((u.1)⁻¹ : Afˣ), u.2.2⟩, Subtype.ext (by simp), Subtype.ext (by simp)⟩
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp

/-- **The character `χ : 𝔸_f^× → (ℤ/3)^×`, `q·u ↦ u mod 3`.** -/
noncomputable def chi : Afˣ →* (ZMod 3)ˣ := (Units.map r3).comp (toZhatUnits.comp duHom)

theorem chi_val (s : Afˣ) : (chi s : ZMod 3) = r3 ⟨du s, (du_mem s).1⟩ := rfl

theorem chi_of_mem {u : Afˣ} (hu : u ∈ ZhatU) : (chi u : ZMod 3) = r3 ⟨u, hu.1⟩ := by
  rw [chi_val]; congr 1; apply Subtype.ext; show ((du u : Afˣ) : Af) = u; rw [du_of_mem hu]

theorem r3_one_add_three (t : Af) (ht : t ∈ Zhat) (h : 1 + 3 * t ∈ Zhat) :
    r3 ⟨1 + 3 * t, h⟩ = 1 := by
  have : (⟨1 + 3 * t, h⟩ : Zhat) = 1 + 3 * ⟨t, ht⟩ :=
    Subtype.ext (by rw [Subring.coe_add, Subring.coe_mul, Subring.coe_one]; rfl)
  rw [this, map_add, map_mul, map_one, map_ofNat]
  have : (3 : ZMod 3) = 0 := rfl
  rw [this, zero_mul, add_zero]

theorem mem_U3_of_r3 {u : Afˣ} (hu : u ∈ ZhatU) (h : r3 ⟨u, hu.1⟩ = 1) : u ∈ U3 := by
  -- local `y_v` with `u_v − 1 = 3 y_v`
  have hloc : ∀ v : Place, ∃ y : ℤ_[primesEquiv v], locA hu.1 v - 1 = 3 * y := by
    intro v
    by_cases hv : v = v3
    · subst hv
      have h1 : PadicInt.toZMod (locA hu.1 v3 - 1) = 0 := by
        rw [r3_apply] at h
        have h' : PadicInt.toZMod (locA hu.1 v3) = 1 := by
          have := congrArg (ZMod.ringEquivCongr v3_spec.symm) h
          rwa [map_one, ← RingEquiv.trans_apply, ZMod.ringEquivCongr_trans,
            ZMod.ringEquivCongr_refl_apply] at this
        rw [map_sub, h', map_one, sub_self]
      obtain ⟨y, hy⟩ := (PadicInt.norm_lt_one_iff_dvd _).1 ((norm_lt_one_iff_toZMod _).2 h1)
      refine ⟨y, ?_⟩
      rw [hy]; congr 1
      exact_mod_cast v3_spec
    · have hp3 : (primesEquiv v : ℕ) ≠ 3 := by
        intro e; apply hv; apply primesEquiv.injective; apply Subtype.ext; rw [e, v3_spec]
      have h3u : IsUnit (3 : ℤ_[primesEquiv v]) := by
        rw [isUnit_iff_toZMod, map_ofNat, ← Nat.cast_ofNat, Ne, ZMod.natCast_eq_zero_iff]
        intro hd
        exact hp3 ((Nat.prime_dvd_prime_iff_eq (primesEquiv v).2 Nat.prime_three).1 hd)
      obtain ⟨w, hw⟩ := h3u
      refine ⟨(locA hu.1 v - 1) * ↑w⁻¹, ?_⟩
      have : (3 : ℤ_[primesEquiv v]) * ↑w⁻¹ = 1 := by rw [← hw]; simp
      linear_combination (-(locA hu.1 v - 1)) * this
  choose y hy using hloc
  refine ⟨hu, adeleHom y, adeleHom_mem y, ?_⟩
  rw [← adeleHom_locA hu.1]
  rw [show locA hu.1 = 1 + 3 * y from funext fun v => by
    show locA hu.1 v = 1 + 3 * y v; linear_combination hy v]
  rw [map_add, map_mul, map_one, map_ofNat]

theorem neg_one_mem_ZhatU : (-1 : Afˣ) ∈ ZhatU :=
  ⟨by simpa using Zhat.neg_mem Zhat.one_mem, by simpa using Zhat.neg_mem Zhat.one_mem⟩

theorem chi_neg_one : chi (-1) = -1 := by
  apply Units.ext
  rw [chi_of_mem neg_one_mem_ZhatU]
  have : (⟨((-1 : Afˣ) : Af), neg_one_mem_ZhatU.1⟩ : Zhat) = -1 := Subtype.ext (by simp)
  rw [this, map_neg, map_one]; rfl

theorem units_zmod3' (u : (ZMod 3)ˣ) : u = 1 ∨ u = -1 := by revert u; decide

theorem chi_surjective : Function.Surjective chi := by
  intro u
  rcases units_zmod3' u with rfl | rfl
  · exact ⟨1, map_one _⟩
  · exact ⟨-1, chi_neg_one⟩

/-- **The kernel of `χ` is `ℚ^×_{>0} · nrd(K₃)`.** -/
theorem chi_ker : chi.ker = posRat ⊔ K3.map nrdU := by
  apply le_antisymm
  · intro s hs
    rw [MonoidHom.mem_ker] at hs
    have h1 : r3 ⟨du s, (du_mem s).1⟩ = 1 := by
      rw [← chi_val, hs]; rfl
    have h2 : du s ∈ K3.map nrdU := U3_le (mem_U3_of_r3 (du_mem s) h1)
    rw [← emb_dq_mul_du s]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨dq s, dq_pos s, rfl⟩)
      (Subgroup.mem_sup_right h2)
  · refine sup_le ?_ ?_
    · rintro _ ⟨q, hq, rfl⟩
      rw [MonoidHom.mem_ker]; apply Units.ext
      rw [chi_val]
      have : (⟨du (emb q), (du_mem _).1⟩ : Zhat) = 1 := Subtype.ext (by show ((du (emb q) : Afˣ) : Af) = 1; rw [du_emb hq]; rfl)
      rw [this, map_one]; rfl
    · intro x hx
      obtain ⟨hxZ, t, ht, hxt⟩ := nrd_K3_le hx
      rw [MonoidHom.mem_ker]; apply Units.ext
      rw [chi_of_mem hxZ]
      have : (⟨(x : Af), hxZ.1⟩ : Zhat) = ⟨1 + 3 * t, hxt ▸ hxZ.1⟩ := Subtype.ext hxt
      rw [this, r3_one_add_three t ht]; rfl

/-! ### The two double coset spaces -/

/-- **`ℚ^×_{>0} \ 𝔸_f^× / nrd(𝒪̂^×)` is a point.** -/
theorem pi0_Kfull_eq_one (x : Pi0 Kfull) : x = 1 := by
  induction x using QuotientGroup.induction_on with
  | H s =>
    rw [QuotientGroup.eq_one_iff, ← emb_dq_mul_du s]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨dq s, dq_pos s, rfl⟩)
      (Subgroup.mem_sup_right (ZhatU_le (du_mem s)))

instance : Subsingleton (Pi0 Kfull) :=
  ⟨fun x y => by rw [pi0_Kfull_eq_one x, pi0_Kfull_eq_one y]⟩

/-- **`ℚ^×_{>0} \ 𝔸_f^× / nrd(K₃) ≅ (ℤ/3)^×`**, by `q·u ↦ u mod 3`. -/
noncomputable def pi0K3Equiv : Pi0 K3 ≃* (ZMod 3)ˣ :=
  (QuotientGroup.quotientMulEquivOfEq chi_ker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective chi chi_surjective)

theorem pi0K3Equiv_mk (s : Afˣ) : pi0K3Equiv (QuotientGroup.mk s) = chi s := rfl


/-! ### The cyclotomic character as an idele, and `χ(χ_cyc(g)) = χ₃(g)` -/

section Cyc

variable {L : Type*} [Field L]

/-- **`χ_cyc(g) ∈ ℤ̂^× ⊆ 𝔸_f^×`**: the idele whose `v`-component is Mathlib's `p`-adic cyclotomic
character `cyclotomicCharacter L p g ∈ ℤ_p^×` (`p = primesEquiv v`). -/
noncomputable def cycU (g : L ≃+* L) : Afˣ :=
  Units.map adeleHom (MulEquiv.piUnits.symm
    (fun v : Place => cyclotomicCharacter L (primesEquiv v) g))

theorem cycU_apply (g : L ≃+* L) (v : Place) :
    ((cycU g : Afˣ) : Af) v = (adicCompletion.padicEquiv (R := ℤ) v).symm
      ((cyclotomicCharacter L (primesEquiv v) g : ℤ_[primesEquiv v]) : ℚ_[primesEquiv v]) := rfl

theorem cycU_mem (g : L ≃+* L) : cycU g ∈ ZhatU := by
  refine ⟨adeleHom_mem _, ?_⟩
  rw [cycU, ← map_inv, Units.coe_map]
  exact adeleHom_mem _

theorem locA_cycU (g : L ≃+* L) (v : Place) :
    locA (cycU_mem g).1 v = (cyclotomicCharacter L (primesEquiv v) g : ℤ_[primesEquiv v]) := by
  rw [locA]
  have : (⟨((cycU g : Afˣ) : Af) v, (cycU_mem g).1 v⟩ : v.adicCompletionIntegers ℚ) =
      (locZ v).symm (cyclotomicCharacter L (primesEquiv v) g : ℤ_[primesEquiv v]) := rfl
  rw [this, RingEquiv.apply_symm_apply]

theorem toZMod_transport {p : ℕ} [Fact p.Prime] (h : p = 3) (g : L ≃+* L) :
    ZMod.ringEquivCongr h (PadicInt.toZMod (cyclotomicCharacter L p g : ℤ_[p])) =
      PadicInt.toZMod (cyclotomicCharacter L 3 g : ℤ_[3]) := by
  subst h; rw [ZMod.ringEquivCongr_refl_apply]

/-- **Mod 3, Mathlib's `3`-adic cyclotomic character is the mod-3 cyclotomic character.** -/
theorem toZMod_cyc_three [∀ i, HasEnoughRootsOfUnity L (3 ^ i)]
    (hn : Nat.card {x // x ∈ rootsOfUnity 3 L} = 3) (g : L ≃+* L) :
    PadicInt.toZMod (cyclotomicCharacter L 3 g : ℤ_[3]) =
      (modularCyclotomicCharacter L hn g : ZMod 3) := by
  apply modularCyclotomicCharacter.unique
  intro t ht
  set x : ℤ_[3] := (cyclotomicCharacter L 3 g : ℤ_[3])
  have ht3 : (t : L) ^ 3 = 1 := by
    rw [mem_rootsOfUnity] at ht
    have := congrArg Units.val ht
    rw [Units.val_pow_eq_pow_val, Units.val_one] at this
    exact this
  have ht31 : (t : L) ^ 3 ^ 1 = 1 := by rw [pow_one]; exact ht3
  have hspec := cyclotomicCharacter.spec (L := L) 3 (n := 1) g (t : L) ht31
  rw [hspec]
  push_cast
  rw [pow_eq_pow_mod _ ht3, pow_eq_pow_mod (PadicInt.toZMod x).val ht3]
  congr 1
  set a := (PadicInt.toZModPow 1 x).val
  set b := (PadicInt.toZMod x).val
  have ha : x - (a : ℤ_[3]) ∈ IsLocalRing.maximalIdeal ℤ_[3] := by
    have : x - (a : ℤ_[3]) ∈ RingHom.ker (PadicInt.toZModPow 1 : ℤ_[3] →+* ZMod (3 ^ 1)) := by
      rw [RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
    rw [PadicInt.ker_toZModPow, pow_one, ← PadicInt.maximalIdeal_eq_span_p] at this
    exact this
  have hb : x - (b : ℤ_[3]) ∈ IsLocalRing.maximalIdeal ℤ_[3] := by
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  have := PadicInt.zmod_congr_of_sub_mem_max_ideal x a b ha hb
  exact (ZMod.natCast_eq_natCast_iff' a b 3).1 this

/-- **`χ(χ_cyc(g)) = χ₃(g)`**: the image of the cyclotomic idele of `g` in
`ℚ^×_{>0}\𝔸_f^×/nrd(K₃) ≅ (ℤ/3)^×` is the mod-3 cyclotomic character of `g`. -/
theorem chi_cycU [∀ i, HasEnoughRootsOfUnity L (3 ^ i)]
    (hn : Nat.card {x // x ∈ rootsOfUnity 3 L} = 3) (g : L ≃+* L) :
    chi (cycU g) = modularCyclotomicCharacter L hn g := by
  apply Units.ext
  rw [chi_of_mem (cycU_mem g), r3_apply]
  change ZMod.ringEquivCongr v3_spec (PadicInt.toZMod (locA (cycU_mem g).1 v3)) = _
  rw [locA_cycU, toZMod_transport v3_spec, toZMod_cyc_three hn]

end Cyc

end ShimuraGlue

/-! ## Part 2: shimura-split `Y3Conn.lean`, verbatim -/

/-!
# shimura-split, Part 2: the orbit computation for `Y3Connected` (row H-59)

The row `TSHecke.Y3Connected` (`∃ (Y, Φ), R1fpProps Y Φ ∧ ConnectedSpace Y.left`) is a composite: Deligne's
description of the geometric components of a Shimura variety with the Galois action on them (Deligne,
*Travaux de Shimura*, Sém. Bourbaki 389 (1971), §§2-3; *Variétés de Shimura*, PSPM 33 (1979), 2.1, 2.6.3),
specialized to `K₃`, **plus** an orbit computation (the Galois group acts transitively on the components,
hence `Y₃` is connected over `ℚ`). This file states the first as a leaf over genuine definitions (the
connected components of the base change `Y ×_ℚ Spec ℚ̄`, the action of `Aut(ℚ̄/ℚ)` on it, and the mod-3
cyclotomic character) and proves the row from it in Lean.
-/

set_option linter.all false

noncomputable section

namespace ShimuraSplit

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV

/-- `Spec ℚ̄ → Spec ℚ`. -/
abbrev sQbar : Spec (CommRingCat.of Qbar) ⟶ Spec (CommRingCat.of ℚ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℚ Qbar))

/-- The base change `Y_ℚ̄ = Y ×_{Spec ℚ} Spec ℚ̄` of a `ℚ`-scheme. -/
abbrev baseQbar (Y : Over (Spec (CommRingCat.of ℚ))) : Scheme := pullback Y.hom sQbar

theorem specMap_sigma_comp (σ : Qbar ≃ₐ[ℚ] Qbar) :
    Spec.map (CommRingCat.ofHom (σ : Qbar →+* Qbar)) ≫ sQbar = sQbar := by
  rw [sQbar, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact (σ : Qbar →ₐ[ℚ] Qbar).comp_algebraMap

/-- **The action of `σ ∈ Aut(ℚ̄/ℚ)` on `Y_ℚ̄`**: `id_Y × Spec σ`. -/
def galAct (Y : Over (Spec (CommRingCat.of ℚ))) (σ : Qbar ≃ₐ[ℚ] Qbar) : baseQbar Y ⟶ baseQbar Y :=
  pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom (σ : Qbar →+* Qbar))) (𝟙 _)
    (by simp) (by rw [Category.comp_id, specMap_sigma_comp])

theorem galAct_fst (Y : Over (Spec (CommRingCat.of ℚ))) (σ : Qbar ≃ₐ[ℚ] Qbar) :
    galAct Y σ ≫ pullback.fst _ _ = pullback.fst _ _ := by
  simp [galAct]

/-- The induced map on the connected components of `Y_ℚ̄`. -/
def galActπ₀ (Y : Over (Spec (CommRingCat.of ℚ))) (σ : Qbar ≃ₐ[ℚ] Qbar) :
    _root_.ConnectedComponents (baseQbar Y) → _root_.ConnectedComponents (baseQbar Y) :=
  (galAct Y σ).continuous.connectedComponentsMap

theorem exists_primitive3 : ∃ ω : Qbar, IsPrimitiveRoot ω 3 := by
  obtain ⟨ω, hω⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic 3 Qbar)
    (by rw [Polynomial.degree_cyclotomic]; norm_num)
  exact ⟨ω, (Polynomial.isRoot_cyclotomic_iff).1 hω⟩

/-- `ℚ̄` contains exactly three cube roots of unity. -/
theorem card_mu3 : Nat.card {x // x ∈ rootsOfUnity 3 Qbar} = 3 :=
  exists_primitive3.choose_spec.card_rootsOfUnity

/-- **The mod-3 cyclotomic character** `χ₃ : Aut(ℚ̄/ℚ) → (ℤ/3)^×` (Mathlib's
`modularCyclotomicCharacter`: `σ(ζ) = ζ^{χ₃(σ)}` for every cube root of unity `ζ`). -/
def chi3 (σ : Qbar ≃ₐ[ℚ] Qbar) : (ZMod 3)ˣ :=
  modularCyclotomicCharacter Qbar card_mu3 σ.toRingEquiv

/-- **LEAF (Deligne's components of `Sh_{K₃}` with the Galois action; specialization).**

*Published statement* (Deligne, *Travaux de Shimura*, Sém. Bourbaki 389 (1971), §§2-3; *Variétés de
Shimura*, PSPM 33 (1979), 2.1 and Thm 2.6.3; Milne, *Introduction to Shimura varieties* (2005), Thm 5.17
and §13; locators UNVERIFIED, no network): for `G = B^×` the set of connected components of
`Sh_K(G, X)_ℚ̄` is `π₀ = ℚ^×_{>0} \ 𝔸_f^× / nrd(K)`, and `σ ∈ Gal(ℚ̄/ℚ)` acts on it by multiplication by
`art⁻¹(σ|ℚ^ab) ∈ ℤ̂^×` (up to the sign convention of the reciprocity map).

*Lean form*: some fine witness `(Y, Φ)` (the canonical model `Y₃ = Sh_{K₃}`, as in `CanonicalModelY3`) has
a bijection `c : π₀(Y_ℚ̄) ≃ (ℤ/3)^×` under which `σ` acts by multiplication by `χ₃(σ)`.

*Why a specialization of the display (with one computation)*: for `K₃ = ker(𝒪̂^× → (𝒪/3𝒪)^×)`,
`nrd(K₃) = ∏_{ℓ≠3} ℤ_ℓ^× × (1 + 3ℤ_3)` (`nrd(𝒪_ℓ^×) = ℤ_ℓ^×` for every `ℓ`, and `nrd(1 + 3𝒪_3) = 1 + 3ℤ_3`),
and `𝔸_f^× = ℚ^×_{>0} · ℤ̂^×` with `ℚ^×_{>0} ∩ ℤ̂^× = 1`, so `π₀ = ℤ̂^×/nrd(K₃) = (ℤ/3)^×`; the image of
`art⁻¹(σ)` there is `χ₃(σ)^{±1} = χ₃(σ)` (`χ₃` has order 2, so the sign convention does not matter).
The computation of `nrd(K₃)` is not formalized (no local quaternion algebras in Mathlib); ts-hecke's
`pi0_check.py` checks the two orbits in Shimura's uniformization `𝒪^× \ (ℍ^± × (𝒪/3𝒪)^×)`.
So this leaf is a **consequence of one theorem** (Deligne's `π₀`), not its printed form. -/
def DeligneComponentsY3 : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y), R1fpProps Y Φ ∧
    ∃ c : _root_.ConnectedComponents (baseQbar Y) ≃ (ZMod 3)ˣ,
      ∀ (σ : Qbar ≃ₐ[ℚ] Qbar) (z : _root_.ConnectedComponents (baseQbar Y)),
        c (galActπ₀ Y σ z) = chi3 σ * c z

/-! ## The orbit computation -/

/-- Some `σ ∈ Aut(ℚ̄/ℚ)` has `χ₃(σ) = −1` (it sends a primitive cube root of unity `ω` to `ω²`). -/
theorem exists_chi3_neg : ∃ σ : Qbar ≃ₐ[ℚ] Qbar, chi3 σ = -1 := by
  obtain ⟨ω, hprim⟩ := exists_primitive3
  have hprim2 : IsPrimitiveRoot (ω ^ 2) 3 := hprim.pow_of_coprime 2 (by norm_num)
  have hmin : minpoly ℚ (ω ^ 2) = minpoly ℚ ω := by
    rw [← Polynomial.cyclotomic_eq_minpoly_rat hprim2 (by norm_num),
      ← Polynomial.cyclotomic_eq_minpoly_rat hprim (by norm_num)]
  obtain ⟨σ, hσ⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := ℚ) (E := Qbar)).1 hmin
  change σ • ω = ω ^ 2 at hσ
  rw [AlgEquiv.smul_def] at hσ
  refine ⟨σ, ?_⟩
  set u : Qbarˣ := (hprim.isUnit (by norm_num)).unit with hu
  have hu1 : (u : Qbar) = ω := rfl
  have hmem : u ∈ rootsOfUnity 3 Qbar := by
    rw [mem_rootsOfUnity]; ext; simp [hu1, hprim.pow_eq_one]
  have hspec := modularCyclotomicCharacter.spec Qbar card_mu3 σ.toRingEquiv hmem
  change σ (u : Qbar) = (u : Qbar) ^ _ at hspec
  rw [hu1, hσ] at hspec
  have hval : ((chi3 σ : (ZMod 3)ˣ) : ZMod 3).val = 2 :=
    (hprim.pow_inj (by norm_num) (ZMod.val_lt _) hspec).symm
  apply Units.ext
  apply ZMod.val_injective
  rw [hval]
  rfl

theorem units_zmod3 (t u : (ZMod 3)ˣ) : u = t ∨ u = -1 * t := by
  revert t u; decide

instance : AlgebraicGeometry.Surjective sQbar := by
  constructor
  intro x
  obtain ⟨y⟩ := (inferInstance : Nonempty (Spec (CommRingCat.of Qbar)))
  exact ⟨y, Subsingleton.elim _ _⟩

/-- **The orbit computation (row H-59 from the leaf)**: if `Aut(ℚ̄/ℚ)` acts on `π₀(Y_ℚ̄) ≃ (ℤ/3)^×` by
`χ₃`, then `Y` is connected (a clopen `U ⊆ Y` pulls back to a Galois-stable clopen of `Y_ℚ̄`, a union of
components whose labels form a `χ₃`-stable subset of `(ℤ/3)^×`, hence `∅` or everything). -/
theorem y3Connected_of_deligne (h : DeligneComponentsY3) :
    ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y), R1fpProps Y Φ ∧ ConnectedSpace Y.left := by
  obtain ⟨Y, Φ, h1, c, hc⟩ := h
  refine ⟨Y, Φ, h1, ?_⟩
  obtain ⟨-, -, ⟨y₀⟩, -, -, -⟩ := h1
  rw [connectedSpace_iff_clopen]
  refine ⟨⟨y₀.left (IsLocalRing.closedPoint _)⟩, fun U hU => ?_⟩
  let p : baseQbar Y ⟶ Y.left := pullback.fst _ _
  have hpsurj : Function.Surjective p := p.surjective
  let V : Set (baseQbar Y) := p ⁻¹' U
  have hV : IsClopen V := hU.preimage p.continuous
  by_contra hne
  rw [not_or] at hne
  obtain ⟨hne0, hne1⟩ := hne
  obtain ⟨u, hu⟩ := Set.nonempty_iff_ne_empty.2 hne0
  obtain ⟨u', hu'⟩ : ∃ u', u' ∉ U := by
    by_contra hall
    exact hne1 (Set.eq_univ_of_forall fun a => by by_contra ha; exact hall ⟨a, ha⟩)
  obtain ⟨z, hz⟩ := hpsurj u
  obtain ⟨z', hz'⟩ := hpsurj u'
  have hzV : z ∈ V := by show p z ∈ U; rw [hz]; exact hu
  have hz'V : z' ∉ V := by show p z' ∉ U; rw [hz']; exact hu'
  -- labels of components inside `V`
  let T : Set (ZMod 3)ˣ := {t | ∃ w ∈ V, c (ConnectedComponents.mk w) = t}
  have hT : ∀ σ : Qbar ≃ₐ[ℚ] Qbar, ∀ t ∈ T, chi3 σ * t ∈ T := by
    rintro σ t ⟨w, hw, rfl⟩
    refine ⟨galAct Y σ w, ?_, ?_⟩
    · show p (galAct Y σ w) ∈ U
      change (pullback.fst Y.hom sQbar) (galAct Y σ w) ∈ U
      rw [← Scheme.Hom.comp_apply, galAct_fst]; exact hw
    · rw [← hc σ]; rfl
  obtain ⟨σ, hσ⟩ := exists_chi3_neg
  have hzT : c (ConnectedComponents.mk z) ∈ T := ⟨z, hzV, rfl⟩
  rcases units_zmod3 (c (ConnectedComponents.mk z)) (c (ConnectedComponents.mk z')) with e | e
  · -- same component as `z`
    have hmk : ConnectedComponents.mk z' = ConnectedComponents.mk z := c.injective e
    rw [ConnectedComponents.coe_eq_coe'] at hmk
    exact hz'V (hV.connectedComponent_subset hzV hmk)
  · obtain ⟨w, hw, hwe⟩ := hT σ _ hzT
    rw [hσ, ← e] at hwe
    have hmk : ConnectedComponents.mk z' = ConnectedComponents.mk w := c.injective hwe.symm
    rw [ConnectedComponents.coe_eq_coe'] at hmk
    exact hz'V (hV.connectedComponent_subset hw hmk)

end ShimuraSplit

#print axioms ShimuraSplit.y3Connected_of_deligne

/-! ## Part 3: shimura-split `DeligneComponentsX6`, verbatim -/

namespace HDec.QMSplit.Moduli

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV

/-- **LEAF-form (Deligne's components at level one; specialization).** Some witness of the moduli clause
lists has `X₆ ×_ℚ ℚ̄` connected. Deligne, Sém. Bourbaki 389 (1971), §§2-3 and PSPM 33 (1979), 2.1, 2.6.3:
`π₀(Sh_K ⊗ ℚ̄) = ℚ^×_{>0}\𝔸_f^×/nrd(K)`; for `K = 𝒪̂^×`, `nrd(𝒪̂^×) = ℤ̂^×` and
`𝔸_f^× = ℚ^×_{>0}·ℤ̂^×`, so `π₀` is one point (locators UNVERIFIED). A consequence of one theorem (the
computation `nrd(𝒪̂^×) = ℤ̂^×` is not formalized). -/
def DeligneComponentsX6 : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (X : Over (Spec (CommRingCat.of ℚ)))
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) (fY : Y ⟶ X),
    R1fpProps Y Φ ∧ X6Props Y Φ X Ψ fY ∧ ConnectedSpace (ShimuraSplit.baseQbar X)

end HDec.QMSplit.Moduli

/-! # shimura-glue: Deligne's `π₀` in printed form; `DeligneComponentsY3`, `DeligneComponentsX6` from it -/

namespace ShimuraGlue

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Rat.HeightOneSpectrum

attribute [local instance 2000] instAlgebraAdicCompletion

/-- **The display of Deligne's theorem on `π₀` for `Sh_K(B^×)`** (with its Galois action), for a
`ℚ`-scheme `Y` and a compact open `K ⊆ (B ⊗ 𝔸_f)^×`: a bijection
`c : π₀(Y ×_ℚ ℚ̄) ≃ ℚ^×_{>0} \ 𝔸_f^× / nrd(K)` under which `σ ∈ Aut(ℚ̄/ℚ)` acts by multiplication by
the class of `u^ε` for every idele `u ∈ ℤ̂^×` whose `p`-components are the `p`-adic cyclotomic
characters of `σ` (Mathlib's `cyclotomicCharacter`), for a fixed sign `ε = ±1`.

* `π₀(Y ×_ℚ ℚ̄)`: Mathlib's `ConnectedComponents` of the scheme `Y ×_{Spec ℚ} Spec ℚ̄`
  (`ShimuraSplit.baseQbar`); `σ` acts by `id × Spec σ` (`ShimuraSplit.galActπ₀`).
* `𝔸_f = FiniteAdeleRing ℤ ℚ`, `B ⊗ 𝔸_f = QuaternionAlgebra 𝔸_f 2 0 (−3)`, `nrd = x x̄`
  (`nrdQ_eq_mul_star`), `ℚ^×_{>0} = posRat`, the double coset space `Pi0 K`.
* The idele condition `u_v = χ_p(σ)` (via Mathlib's `padicEquiv : ℚ_v ≅ ℚ_p`) is the reciprocity map
  of `ℚ` made explicit: `art_ℚ(u)` acts on `μ_∞` by `ζ ↦ ζ^{u^{∓1}}` (sign by normalization), so the
  ideles `s` with `art(s) = σ|ℚ^ab` are `ℚ^×_{>0}·u^{±1}`; the sign `ε` absorbs both the normalization
  of `art` and the left/right convention of `galActπ₀`. -/
def DelignePi0 (Y : Over (Spec (CommRingCat.of ℚ))) (K : Subgroup BAfˣ) : Prop :=
  ∃ (c : _root_.ConnectedComponents (ShimuraSplit.baseQbar Y) ≃ Pi0 K) (ε : ℤˣ),
    ∀ (σ : Qbar ≃ₐ[ℚ] Qbar) (u : Afˣ),
      (∀ v : Place, (u : Af) v = (adicCompletion.padicEquiv (R := ℤ) v).symm
        ((cyclotomicCharacter Qbar (primesEquiv v) σ.toRingEquiv : ℤ_[primesEquiv v]) :
          ℚ_[primesEquiv v])) →
      ∀ z : _root_.ConnectedComponents (ShimuraSplit.baseQbar Y),
        c (ShimuraSplit.galActπ₀ Y σ z) = (QuotientGroup.mk u : Pi0 K) ^ (ε : ℤ) * c z

/-- **LEAF (Deligne's theorem on the connected components of a Shimura variety and the Galois action on
them; printed form, at level `K₃` on the canonical model `Y₃`).**

*Published statement*: P. Deligne, *Travaux de Shimura*, Sém. Bourbaki 389 (1971), Thm 2.4 and §3
(reciprocity on `π₀`), and *Variétés de Shimura*, Proc. Sympos. Pure Math. 33 (1979), Part 2,
2.1.3 and Thm 2.6.3 (`π₀(Sh_K(G,X)_ℂ) = G(ℚ)_+ \ G(𝔸_f) / K ≅ T(ℚ)^† \ T(𝔸_f) / ν(K)` for `G^der`
simply connected, `T = G/G^der`, with `Aut(ℂ/ℚ)` acting through the reciprocity map); also
J. S. Milne, *Introduction to Shimura varieties* (2005), Thm 5.17 and Thm 13.6 (locators UNVERIFIED, no
network). For `G = B^×` (`B` indefinite, `G^der = SL₁(B)` simply connected, `ν = nrd`, `T = 𝔾_m`,
`T(ℚ)^† = ℚ^×_{>0}`) this is the display `DelignePi0 Y K` for `Y = Sh_K`.

*Lean form*: some fine witness `(Y, Φ)` of the moduli clause lists (`R1fpProps`: the canonical model
`Y₃ = Sh_{K₃}` with its moduli interpretation, as in `CanonicalModelY3`) satisfies `DelignePi0 Y K3`, where
`K3 = ker(𝒪̂^× → (𝒪̂/3𝒪̂)^×)` is the level of the kernel's `Level3`.

*Reading*: printed form, with (i) the reciprocity map of `ℚ` written through the cyclotomic character,
and (ii) `π₀` of `Sh_K ⊗ ℚ̄` in the Zariski topology, which equals `π₀(Sh_K(ℂ))` (finite type over an
algebraically closed field; GAGA). Not stronger than the print. -/
def DeligneComponentsY3Printed : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y), R1fpProps Y Φ ∧ DelignePi0 Y K3

/-- **LEAF (Deligne's theorem, printed form, at level `𝒪̂^×` on the canonical model `X₆ = X₀(6,1)`).**
Same source and reading as `DeligneComponentsY3Printed`; the witness is a coarse witness
(`X6Props`: `X₆ = Sh_{𝒪̂^×}` with the coarse moduli interpretation of its `ℚ̄`-points) and the level is
`Kfull = 𝒪̂^×`. -/
def DeligneComponentsX6Printed : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (X : Over (Spec (CommRingCat.of ℚ)))
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) (fY : Y ⟶ X),
    R1fpProps Y Φ ∧ X6Props Y Φ X Ψ fY ∧ DelignePi0 X Kfull

instance : NeZero ((3 : ℕ) : ℚ) := ⟨by norm_num⟩

theorem zmod3_zpow (x : (ZMod 3)ˣ) (ε : ℤˣ) : x ^ (ε : ℤ) = x := by
  rcases Int.units_eq_one_or ε with rfl | rfl
  · simp
  · have : ∀ y : (ZMod 3)ˣ, y⁻¹ = y := by decide
    simp [this]

/-- **`DeligneComponentsY3` (shimura-split) from the printed leaf**, by the computation
`ℚ^×_{>0} \ 𝔸_f^× / nrd(K₃) ≅ (ℤ/3)^×` (`pi0K3Equiv`) and `χ(χ_cyc(σ)) = χ₃(σ)` (`chi_cycU`). -/
theorem deligneComponentsY3_of_printed (h : DeligneComponentsY3Printed) :
    ShimuraSplit.DeligneComponentsY3 := by
  obtain ⟨Y, Φ, h1, c, ε, hc⟩ := h
  refine ⟨Y, Φ, h1, c.trans pi0K3Equiv.toEquiv, fun σ z => ?_⟩
  have := hc σ (cycU σ.toRingEquiv) (fun v => cycU_apply _ v) z
  simp only [Equiv.trans_apply, MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, this, map_mul,
    map_zpow, pi0K3Equiv_mk]
  rw [chi_cycU ShimuraSplit.card_mu3, zmod3_zpow]
  rfl

/-- A space whose `π₀` is a nonempty subsingleton is connected. -/
theorem connectedSpace_of_subsingleton {T : Type*} [TopologicalSpace T] [Nonempty T]
    (h : Subsingleton (_root_.ConnectedComponents T)) : ConnectedSpace T := by
  haveI : PreconnectedSpace T := by
    rw [preconnectedSpace_iff_connectedComponent]
    intro x
    apply Set.eq_univ_of_forall
    intro y
    have : ConnectedComponents.mk y = ConnectedComponents.mk x := Subsingleton.elim _ _
    rw [ConnectedComponents.coe_eq_coe] at this
    rw [← this]; exact mem_connectedComponent
  exact ⟨inferInstance⟩

/-- **`DeligneComponentsX6` (shimura-split) from the printed leaf**, by the computation
`ℚ^×_{>0} \ 𝔸_f^× / nrd(𝒪̂^×) = 1` (`pi0_Kfull_eq_one`: `𝔸_f^× = ℚ^×_{>0} ℤ̂^×` and
`nrd(𝒪̂^×) = ℤ̂^×`). -/
theorem deligneComponentsX6_of_printed (h : DeligneComponentsX6Printed) :
    HDec.QMSplit.Moduli.DeligneComponentsX6 := by
  obtain ⟨Y, Φ, X, Ψ, fY, h1, h6, c, -, -⟩ := h
  refine ⟨Y, Φ, X, Ψ, fY, h1, h6, ?_⟩
  obtain ⟨x⟩ := h6.2.2.1
  haveI : Nonempty (ShimuraSplit.baseQbar X) := by
    let s : Spec (CommRingCat.of Qbar) ⟶ ShimuraSplit.baseQbar X :=
      pullback.lift x.left (𝟙 _) (by rw [Category.id_comp]; exact Over.w x)
    obtain ⟨pt⟩ := (inferInstance : Nonempty (Spec (CommRingCat.of Qbar)))
    exact ⟨s pt⟩
  exact connectedSpace_of_subsingleton c.subsingleton

end ShimuraGlue

#print axioms ShimuraGlue.deligneComponentsY3_of_printed
#print axioms ShimuraGlue.deligneComponentsX6_of_printed