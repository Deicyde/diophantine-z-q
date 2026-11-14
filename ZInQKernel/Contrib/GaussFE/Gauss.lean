import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Gauss's point count on `y² = x³ − x` via a quartic Jacobi sum

For a prime `p ≡ 1 (mod 4)` let `χ : 𝔽_p → ℤ[i]` be a multiplicative character of order `4`
(it exists because `i ∈ ℤ[i]` is a primitive fourth root of unity) and `J = J(χ, χ²)`.

* `χ²` is the quadratic character (`quadraticChar_eq_chi_sq`), so
  `#{y² = x³ − x} = p + Σ_x χ(x³ − x)²` and `Σ_x χ(x³ − x)² = J + J̄` (`sum_chi_sq_cubic`,
  substituting `t = x²`).
* `J J̄ = p` (Mathlib's `jacobiSum_mul_jacobiSum_inv`, through `ℤ[i] ↪ ℂ`).
* `J ≡ −1 (mod 2 + 2i)` (`two_add_two_i_dvd_jacobi_add_one`): the summand of `J` is invariant
  under `t ↦ t⁻¹`, the involution is free off `{0, ±1}`, and `2(u − 1) ≡ 0 (mod 2 + 2i)` for
  every unit `u`; the term `t = −1` equals `1` because `2i = (1 + i)²` in `𝔽_p`.

Hence (`gauss_jacobi`) `#{(x, y) : y² = x³ − x} = p + 2A` with `A + Bi = J`, `A² + B² = p`,
`A` odd and `B ≡ A + 1 (mod 4)`, i.e. `−J` is primary. This is Gauss's theorem
(Ireland–Rosen, Ch. 18 §4; the congruence is Ch. 9 §9 for `J(χ, χ)`).
-/

namespace ZInQ.Contrib.GaussFE

open MulChar Finset

/-- `i ∈ ℤ[i]`. -/
def gI : GaussianInt := ⟨0, 1⟩

theorem gI_sq : gI ^ 2 = -1 := by
  rw [sq]; ext <;> simp [gI]

theorem isPrimitiveRoot_gI : IsPrimitiveRoot gI 4 := by
  refine IsPrimitiveRoot.mk_of_lt gI (by norm_num) ?_ ?_
  · rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, gI_sq]; norm_num
  · intro l hl0 hl4
    interval_cases l
    · intro h; have := congrArg Zsqrtd.re h; simp [gI] at this
    · rw [gI_sq]; intro h; have := congrArg Zsqrtd.re h; simp at this
    · rw [pow_succ, gI_sq]; intro h; have := congrArg Zsqrtd.re h; simp [gI] at this

/-- The elements of `ℤ[i]` with `u⁴ = 1` are `±1, ±i`. -/
theorem pow_four_eq_one_cases {u : GaussianInt} (h : u ^ 4 = 1) :
    u = 1 ∨ u = -1 ∨ u = gI ∨ u = -gI := by
  have hn : u.norm ^ 4 = 1 := by
    have := congrArg Zsqrtd.norm h
    rw [show u ^ 4 = u * u * u * u by ring, Zsqrtd.norm_mul, Zsqrtd.norm_mul, Zsqrtd.norm_mul,
      Zsqrtd.norm_one] at this
    linear_combination this
  have hN : u.norm = 1 :=
    (pow_eq_one_iff_of_nonneg (Zsqrtd.norm_nonneg (by norm_num) u) (by norm_num)).mp hn
  have h1 : u.re * u.re + u.im * u.im = 1 := by
    have := Zsqrtd.norm_def u; rw [hN] at this; linarith
  have hr : u.re = -1 ∨ u.re = 0 ∨ u.re = 1 := by
    have : u.re * u.re ≤ 1 := by nlinarith [mul_self_nonneg u.im]
    have h2 : -1 ≤ u.re := by nlinarith
    have h3 : u.re ≤ 1 := by nlinarith
    omega
  have hi : u.im = -1 ∨ u.im = 0 ∨ u.im = 1 := by
    have : u.im * u.im ≤ 1 := by nlinarith [mul_self_nonneg u.re]
    have h2 : -1 ≤ u.im := by nlinarith
    have h3 : u.im ≤ 1 := by nlinarith
    omega
  rcases hr with hr | hr | hr <;> rcases hi with hi | hi | hi <;> rw [hr, hi] at h1 <;>
    norm_num at h1
  · right; left; ext <;> simp [hr, hi]
  · right; right; right; ext <;> simp [gI, hr, hi]
  · right; right; left; ext <;> simp [gI, hr, hi]
  · left; ext <;> simp [hr, hi]

/-- `2 + 2i`. -/
def twoTwoI : GaussianInt := ⟨2, 2⟩

theorem unit_facts {u : GaussianInt} (h : u ^ 4 = 1) :
    star u = u ^ 3 ∧ twoTwoI ∣ 2 * (u - 1) := by
  rcases pow_four_eq_one_cases h with rfl | rfl | rfl | rfl
  · exact ⟨by simp, ⟨0, by simp⟩⟩
  · refine ⟨by ext <;> simp [pow_succ], ⟨⟨-1, 1⟩, ?_⟩⟩
    ext <;> simp [twoTwoI]
  · refine ⟨?_, ⟨gI, ?_⟩⟩
    · rw [pow_succ, gI_sq]; ext <;> simp [gI]
    · ext <;> simp [twoTwoI, gI]
  · refine ⟨?_, ⟨-1, ?_⟩⟩
    · rw [pow_succ, neg_sq, gI_sq]; ext <;> simp [gI]
    · ext <;> simp [twoTwoI, gI]

variable {p : ℕ} [hp : Fact p.Prime]

theorem two_ne_zero_zmod (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 :=
  Ring.two_ne_zero (by rw [ZMod.ringChar_zmod_n]; exact hp2)

/-- A quartic character exists for `p ≡ 1 (mod 4)`. -/
theorem exists_quartic (hp1 : p % 4 = 1) : ∃ χ : MulChar (ZMod p) GaussianInt, orderOf χ = 4 :=
  MulChar.exists_mulChar_orderOf (ZMod p) (by rw [ZMod.card]; omega) isPrimitiveRoot_gI

section Chi

variable (χ : MulChar (ZMod p) GaussianInt) (hχ : orderOf χ = 4)
include hχ

theorem chi_pow_four : χ ^ 4 = 1 := hχ ▸ pow_orderOf_eq_one χ

theorem chi_apply_pow_four {a : ZMod p} (ha : a ≠ 0) : χ a ^ 4 = 1 := by
  rw [← MulChar.pow_apply' χ (by norm_num : (4 : ℕ) ≠ 0), chi_pow_four χ hχ]
  exact MulChar.one_apply ha.isUnit

theorem star_chi (a : ZMod p) : star (χ a) = χ a ^ 3 := by
  by_cases ha : a = 0
  · subst ha; simp
  · exact (unit_facts (chi_apply_pow_four χ hχ ha)).1

theorem chi_pow_six (a : ZMod p) : χ a ^ 6 = χ a ^ 2 := by
  by_cases ha : a = 0
  · subst ha; simp
  · rw [show 6 = 4 + 2 from rfl, pow_add, chi_apply_pow_four χ hχ ha, one_mul]

theorem chi_neg_one_sq : χ (-1) ^ 2 = 1 := by
  rw [← map_pow, neg_one_sq, map_one]

theorem chi_inv_apply {t : ZMod p} (ht : t ≠ 0) : χ t⁻¹ = χ t ^ 3 := by
  have h1 : χ t * χ t⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ ht, map_one]
  have h4 := chi_apply_pow_four χ hχ ht
  linear_combination (χ t ^ 3) * h1 - (χ t⁻¹) * h4

theorem chi_ne_one : χ ≠ 1 := by
  have := pow_ne_one_of_lt_orderOf (x := χ) (n := 1) one_ne_zero (by omega)
  rwa [pow_one] at this

theorem chi_sq_ne_one : χ ^ 2 ≠ 1 := pow_ne_one_of_lt_orderOf two_ne_zero (by omega)

theorem chi_cube_ne_one : χ ^ 3 ≠ 1 := pow_ne_one_of_lt_orderOf three_ne_zero (by omega)

theorem chi_inv : χ⁻¹ = χ ^ 3 :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_succ', chi_pow_four χ hχ])

theorem chi_sq_inv : (χ ^ 2)⁻¹ = χ ^ 2 :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_add, chi_pow_four χ hχ])

/-- `χ²` is the quadratic character. -/
theorem quadraticChar_eq_chi_sq (hp2 : p ≠ 2) (a : ZMod p) :
    ((quadraticChar (ZMod p) a : ℤ) : GaussianInt) = χ a ^ 2 := by
  by_cases ha : a = 0
  · subst ha; simp
  have hc : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hord : orderOf g = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units]
  have hp3 : 3 ≤ p := by
    have := hp.out.two_le; omega
  have hgen : ∀ x : (ZMod p)ˣ, ∃ n : ℕ, g ^ n = x := fun x =>
    (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr (hg x))
  -- the quadratic character at the generator
  have hq : quadraticChar (ZMod p) g = -1 := by
    rcases quadraticChar_dichotomy (F := ZMod p) g.ne_zero with h | h
    · exfalso
      have h2 := quadraticChar_eq_pow_of_char_ne_two' hc (g : ZMod p)
      rw [h, ZMod.card] at h2
      have h3 : g ^ (p / 2) = 1 := by
        ext; push_cast; rw [← h2]; simp
      exact pow_ne_one_of_lt_orderOf (by omega) (by omega) h3
    · exact h
  -- `χ²` at the generator
  have hχg : χ g ^ 2 = -1 := by
    have h4 : (χ g ^ 2) ^ 2 = 1 := by
      rw [← pow_mul]; exact chi_apply_pow_four χ hχ g.ne_zero
    rcases sq_eq_one_iff.mp h4 with h | h
    · exfalso
      apply chi_sq_ne_one χ hχ
      rw [MulChar.eq_one_iff]
      intro x
      obtain ⟨n, rfl⟩ := hgen x
      rw [MulChar.pow_apply' _ two_ne_zero, Units.val_pow_eq_pow_val, map_pow, ← pow_mul,
        mul_comm, pow_mul, h, one_pow]
    · exact h
  obtain ⟨n, hn⟩ := hgen (Units.mk0 a ha)
  have ha' : a = (g : ZMod p) ^ n := by
    rw [← Units.val_pow_eq_pow_val, hn, Units.val_mk0]
  rw [ha', map_pow, hq, map_pow, ← pow_mul, mul_comm, pow_mul, hχg]
  push_cast; rfl

/-- `Σ_x F(x²) = Σ_t (1 + χ(t)²) F(t)`. -/
theorem sum_sq_comp (hp2 : p ≠ 2) (F : ZMod p → GaussianInt) :
    ∑ x : ZMod p, F (x ^ 2) = ∑ t : ZMod p, (1 + χ t ^ 2) * F t := by
  classical
  have hc : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  rw [← Finset.sum_fiberwise Finset.univ (fun x : ZMod p => x ^ 2) (fun x => F (x ^ 2))]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.sum_congr rfl (fun x hx => by rw [(Finset.mem_filter.mp hx).2]), Finset.sum_const,
    nsmul_eq_mul]
  congr 1
  rw [← quadraticChar_eq_chi_sq χ hχ hp2 t]
  have h := quadraticChar_card_sqrts hc t
  rw [Set.toFinset_ofPred] at h
  have h' : (((Finset.univ.filter fun x : ZMod p => x ^ 2 = t).card : ℤ) : GaussianInt) =
      ((quadraticChar (ZMod p) t + 1 : ℤ) : GaussianInt) := by rw [h]
  push_cast at h'
  rw [h', add_comm]

/-- `Σ_x χ(x³ − x)² = J(χ, χ²) + J(χ³, χ²)`. -/
theorem sum_chi_sq_cubic (hp2 : p ≠ 2) :
    ∑ x : ZMod p, χ (x ^ 3 - x) ^ 2 = jacobiSum χ (χ ^ 2) + jacobiSum (χ ^ 3) (χ ^ 2) := by
  have h1 : ∀ x : ZMod p, χ (x ^ 3 - x) ^ 2 = χ (x ^ 2) * χ (1 - x ^ 2) ^ 2 := by
    intro x
    have : x ^ 3 - x = x * (-1) * (1 - x ^ 2) := by ring
    rw [this, map_mul, map_mul, map_pow]
    have h := chi_neg_one_sq χ hχ
    linear_combination (χ x ^ 2 * χ (1 - x ^ 2) ^ 2) * h
  rw [Finset.sum_congr rfl (fun x _ => h1 x),
    sum_sq_comp χ hχ hp2 (fun t => χ t * χ (1 - t) ^ 2)]
  simp only [jacobiSum, MulChar.pow_apply' _ two_ne_zero, MulChar.pow_apply' _ three_ne_zero,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  ring

/-- `J(χ³, χ²) = conj J(χ, χ²)`. -/
theorem jacobi_conj : jacobiSum (χ ^ 3) (χ ^ 2) = star (jacobiSum χ (χ ^ 2)) := by
  simp only [jacobiSum, MulChar.pow_apply' _ two_ne_zero, MulChar.pow_apply' _ three_ne_zero]
  rw [star_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [star_mul', star_pow, star_chi χ hχ, star_chi χ hχ, ← pow_mul, chi_pow_six χ hχ]

/-- `J(χ, χ²) · conj J(χ, χ²) = p`. -/
theorem jacobi_mul_star : jacobiSum χ (χ ^ 2) * star (jacobiSum χ (χ ^ 2)) = p := by
  rw [← jacobi_conj χ hχ]
  have hinj : Function.Injective GaussianInt.toComplex := GaussianInt.toComplex_injective
  apply hinj
  have hch : ringChar ℂ ≠ ringChar (ZMod p) := by
    rw [ringChar.eq_zero, ZMod.ringChar_zmod_n]; exact hp.out.ne_zero.symm
  have h := jacobiSum_mul_jacobiSum_inv hch (χ := χ.ringHomComp GaussianInt.toComplex)
    (φ := (χ ^ 2).ringHomComp GaussianInt.toComplex)
    ((MulChar.ringHomComp_ne_one_iff hinj).mpr (chi_ne_one χ hχ))
    ((MulChar.ringHomComp_ne_one_iff hinj).mpr (chi_sq_ne_one χ hχ))
    (by
      rw [← MulChar.ringHomComp_mul, ← pow_succ']
      exact (MulChar.ringHomComp_ne_one_iff hinj).mpr (chi_cube_ne_one χ hχ))
  rw [MulChar.ringHomComp_inv, MulChar.ringHomComp_inv, jacobiSum_ringHomComp,
    jacobiSum_ringHomComp, chi_inv χ hχ, chi_sq_inv χ hχ, ZMod.card] at h
  rw [map_mul, h, map_natCast]

/-- `χ(−1) χ(2)² = 1` for `p ≡ 1 (mod 4)` (`−1 = r²`, `2r = (1 + r)²`). -/
theorem chi_neg_one_mul_chi_two_sq (hp1 : p % 4 = 1) : χ (-1) * χ 2 ^ 2 = 1 := by
  obtain ⟨r, hr⟩ := ZMod.exists_sq_eq_neg_one_iff.mpr (by omega : p % 4 ≠ 3)
  have hp2 : p ≠ 2 := by rintro rfl; omega
  have h2r : (2 : ZMod p) * r = (1 + r) ^ 2 := by linear_combination hr
  have h1r : 1 + r ≠ 0 := by
    intro h
    have hr1 : r = -1 := by linear_combination h
    rw [hr1] at hr
    apply two_ne_zero_zmod hp2
    linear_combination -hr
  rw [hr, map_mul]
  have : χ r * χ r * χ 2 ^ 2 = (χ (1 + r) ^ 2) ^ 2 := by
    rw [← map_pow χ (1 + r) 2, ← h2r, map_mul]; ring
  rw [this, ← pow_mul]
  exact chi_apply_pow_four χ hχ h1r

/-- **The congruence `J(χ, χ²) ≡ −1 (mod 2 + 2i)`**: `−J` is primary. -/
theorem two_add_two_i_dvd_jacobi_add_one (hp1 : p % 4 = 1) :
    twoTwoI ∣ jacobiSum χ (χ ^ 2) + 1 := by
  classical
  have hp2 : p ≠ 2 := by rintro rfl; omega
  have h20 := two_ne_zero_zmod hp2
  set f : ZMod p → GaussianInt := fun t => χ t * χ (1 - t) ^ 2 with hf
  have hJ : jacobiSum χ (χ ^ 2) = ∑ t, f t := by
    simp only [jacobiSum, MulChar.pow_apply' _ two_ne_zero, hf]
  -- the three special points
  have h10 : (1 : ZMod p) ≠ 0 := one_ne_zero
  have hm10 : (-1 : ZMod p) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  have hm11 : (-1 : ZMod p) ≠ 1 := by
    intro h; apply h20; linear_combination -h
  set X := ((Finset.univ.erase (0 : ZMod p)).erase 1).erase (-1) with hX
  have hmemX : ∀ t, t ∈ X ↔ t ≠ -1 ∧ t ≠ 1 ∧ t ≠ 0 := by
    intro t; simp [hX, Finset.mem_erase]
  have hsplit : ∑ t, f t = f 0 + f 1 + f (-1) + ∑ t ∈ X, f t := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod p)),
      ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨h10, Finset.mem_univ _⟩),
      ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hm11, Finset.mem_erase.mpr
        ⟨hm10, Finset.mem_univ _⟩⟩)]
    ring
  have hf0 : f 0 = 0 := by simp [hf]
  have hf1 : f 1 = 0 := by simp [hf]
  have hfm1 : f (-1) = 1 := by
    simp only [hf]
    rw [show (1 : ZMod p) - -1 = 2 by ring]
    exact chi_neg_one_mul_chi_two_sq χ hχ hp1
  have hcard : X.card = p - 3 := by
    rw [hX, Finset.card_erase_of_mem, Finset.card_erase_of_mem, Finset.card_erase_of_mem,
      Finset.card_univ, ZMod.card]
    · omega
    · exact Finset.mem_univ _
    · exact Finset.mem_erase.mpr ⟨h10, Finset.mem_univ _⟩
    · exact Finset.mem_erase.mpr ⟨hm11, Finset.mem_erase.mpr ⟨hm10, Finset.mem_univ _⟩⟩
  -- the involution `t ↦ t⁻¹` on `X`
  have hinvf : ∀ t : ZMod p, t ≠ 0 → f t⁻¹ = f t := by
    intro t ht
    simp only [hf]
    have h1t : 1 - t⁻¹ = (-1) * (1 - t) * t⁻¹ := by field_simp; ring
    rw [h1t, map_mul, map_mul, chi_inv_apply χ hχ ht]
    have hu4 := chi_apply_pow_four χ hχ ht
    have hw2 := chi_neg_one_sq χ hχ
    linear_combination (χ t * χ (1 - t) ^ 2 * (χ t ^ 4 + 1) * χ (-1) ^ 2) * hu4 +
      (χ t * χ (1 - t) ^ 2) * hw2
  have hunit : ∀ t ∈ X, f t ^ 4 = 1 := by
    intro t ht
    obtain ⟨-, h1, h0⟩ := (hmemX t).mp ht
    have h1t : 1 - t ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
    simp only [hf]
    rw [mul_pow, ← pow_mul, show 2 * 4 = 4 * 2 from rfl, pow_mul, chi_apply_pow_four χ hχ h0,
      chi_apply_pow_four χ hχ h1t, one_pow, one_mul]
  have hinvX : ∀ t ∈ X, t⁻¹ ∈ X := by
    intro t ht
    obtain ⟨hm1, h1, h0⟩ := (hmemX t).mp ht
    refine (hmemX _).mpr ⟨?_, ?_, inv_ne_zero h0⟩
    · intro h; apply hm1; rw [← inv_inv t, h]; simp
    · intro h; apply h1; rw [← inv_inv t, h, inv_one]
  have hkey : Ideal.Quotient.mk (Ideal.span {twoTwoI}) (∑ t ∈ X, (f t - 1)) = 0 := by
    rw [map_sum]
    refine Finset.sum_involution (fun t _ => t⁻¹) ?_ ?_ hinvX ?_
    · intro t ht
      obtain ⟨-, -, h0⟩ := (hmemX t).mp ht
      rw [hinvf t h0, ← map_add, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton,
        ← two_mul]
      exact (unit_facts (hunit t ht)).2
    · intro t ht _ h
      obtain ⟨hm1, h1, h0⟩ := (hmemX t).mp ht
      have htt : t * t = 1 := by
        have := mul_inv_cancel₀ h0
        rwa [h] at this
      rcases mul_self_eq_one_iff.mp htt with h' | h'
      · exact h1 h'
      · exact hm1 h'
    · intro t _; exact inv_inv t
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hkey
  -- assemble: `J + 1 = (p − 1) + Σ_X (f − 1)`
  have hsumX : ∑ t ∈ X, f t = ∑ t ∈ X, (f t - 1) + ((p - 3 : ℕ) : GaussianInt) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, hcard, nsmul_eq_mul, mul_one]; ring
  have hp4 : (4 : ℕ) ∣ p - 1 := by omega
  obtain ⟨k, hk⟩ := hp4
  have hp' : ((p - 3 : ℕ) : GaussianInt) + 2 = 4 * (k : GaussianInt) := by
    have h3 : 3 ≤ p := by have := hp.out.two_le; omega
    have : p - 3 + 2 = 4 * k := by omega
    exact_mod_cast this
  rw [hJ, hsplit, hf0, hf1, hfm1, hsumX]
  have h4 : twoTwoI ∣ (4 : GaussianInt) := ⟨⟨1, -1⟩, by ext <;> simp [twoTwoI]⟩
  have : (0 : GaussianInt) + 0 + 1 + (∑ t ∈ X, (f t - 1) + ((p - 3 : ℕ) : GaussianInt)) + 1 =
      ∑ t ∈ X, (f t - 1) + 4 * (k : GaussianInt) := by
    rw [← hp']; ring
  rw [this]
  exact dvd_add hkey (dvd_mul_of_dvd_left h4 _)

end Chi

/-- `#{(x, y) ∈ 𝔽_p² : y² = x³ − x} = p + Σ_x ((x³ − x)/p)` for odd `p`. -/
theorem card_cubic_eq (hp2 : p ≠ 2) :
    (Nat.card {xy : ZMod p × ZMod p // xy.2 ^ 2 = xy.1 ^ 3 - xy.1} : ℤ) =
      p + ∑ x : ZMod p, quadraticChar (ZMod p) (x ^ 3 - x) := by
  classical
  have hc : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type]
  push_cast
  have : ∀ x : ZMod p, (∑ y : ZMod p, if y ^ 2 = x ^ 3 - x then (1 : ℤ) else 0) =
      quadraticChar (ZMod p) (x ^ 3 - x) + 1 := fun x => by
    rw [← quadraticChar_card_sqrts hc, Set.toFinset_ofPred, Finset.card_filter]
    push_cast; rfl
  simp_rw [this]
  rw [Finset.sum_add_distrib]
  simp [ZMod.card, add_comm]

/-- **Gauss's theorem (1814) for `y² = x³ − x`.** For a prime `p ≡ 1 (mod 4)` there are
integers `A, B` with `A² + B² = p`, `A` odd, `B ≡ A + 1 (mod 4)` (so `−(A + Bi)` is primary,
`≡ 1 mod 2 + 2i`), and `#{(x, y) ∈ 𝔽_p² : y² = x³ − x} = p + 2A`. -/
theorem gauss_jacobi (hp1 : p % 4 = 1) :
    ∃ A B : ℤ, A ^ 2 + B ^ 2 = p ∧ (A + 1) % 2 = 0 ∧ (B - A - 1) % 4 = 0 ∧
      (Nat.card {xy : ZMod p × ZMod p // xy.2 ^ 2 = xy.1 ^ 3 - xy.1} : ℤ) = p + 2 * A := by
  have hp2 : p ≠ 2 := by rintro rfl; omega
  obtain ⟨χ, hχ⟩ := exists_quartic hp1
  set J := jacobiSum χ (χ ^ 2) with hJ
  refine ⟨J.re, J.im, ?_, ?_⟩
  · -- the norm
    have h := jacobi_mul_star χ hχ
    rw [← hJ, ← Zsqrtd.norm_eq_mul_conj] at h
    have h' := congrArg Zsqrtd.re h
    simp only [Zsqrtd.re_intCast, Zsqrtd.re_natCast] at h'
    rw [Zsqrtd.norm_def] at h'
    linear_combination h'
  · obtain ⟨c, hc⟩ := two_add_two_i_dvd_jacobi_add_one χ hχ hp1
    have hre := congrArg Zsqrtd.re hc
    have him := congrArg Zsqrtd.im hc
    simp [twoTwoI, ← hJ] at hre him
    refine ⟨by omega, by omega, ?_⟩
    rw [card_cubic_eq hp2]
    congr 1
    have hS := sum_chi_sq_cubic χ hχ hp2
    rw [jacobi_conj χ hχ, ← hJ] at hS
    have hS' : ((∑ x : ZMod p, quadraticChar (ZMod p) (x ^ 3 - x) : ℤ) : GaussianInt) =
        J + star J := by
      push_cast
      rw [← hS]
      exact Finset.sum_congr rfl fun x _ => quadraticChar_eq_chi_sq χ hχ hp2 _
    have h2 := congrArg Zsqrtd.re hS'
    simp only [Zsqrtd.re_intCast, Zsqrtd.re_add, Zsqrtd.re_star] at h2
    rw [h2]; ring

end ZInQ.Contrib.GaussFE
