import ZInQKernel.Model.Field.Basic

/-!
# `ℤ[√2]` is a Euclidean domain

Blueprint: `model/field/integers-pid.md` (first part).

`ℤ[s]` is Euclidean for `|N|`: for `b ≠ 0`, write `a s̄(b) = α + β s` and take the quotient
`q = ⌊α / N(b)⌉ + ⌊β / N(b)⌉ s`; then `N(a - q b) N(b) = N(b)² (e₁² - 2 e₂²)` with
`|e₁|, |e₂| ≤ 1/2`, so `|N(a - q b)| ≤ |N(b)| / 2 < |N(b)|`. This follows Mathlib's
`GaussianInt` instance.
-/

namespace ZInQ

open QuadraticAlgebra

namespace Zs

theorem norm_eq (z : Zs) : QuadraticAlgebra.norm z = z.re ^ 2 - 2 * z.im ^ 2 := by
  rw [QuadraticAlgebra.norm_def]; ring

theorem norm_toK0 (z : Zs) :
    QuadraticAlgebra.norm (Zs.toK0 z) = ((QuadraticAlgebra.norm z : ℤ) : ℚ) := by
  rw [K0.norm_eq, norm_eq]; simp

theorem norm_eq_zero_iff {z : Zs} : QuadraticAlgebra.norm z = 0 ↔ z = 0 := by
  constructor
  · intro h
    apply Zs.toK0_injective
    rw [map_zero, ← K0.norm_eq_zero_iff, norm_toK0, h, Int.cast_zero]
  · rintro rfl; simp

theorem norm_ne_zero {z : Zs} (hz : z ≠ 0) : QuadraticAlgebra.norm z ≠ 0 :=
  fun h => hz (norm_eq_zero_iff.mp h)

@[simp] theorem mk_re (u v : ℤ) : (⟨u, v⟩ : Zs).re = u := rfl
@[simp] theorem mk_im (u v : ℤ) : (⟨u, v⟩ : Zs).im = v := rfl

/-- The Euclidean quotient: round the components of `a s̄(b) / N(b)`. -/
instance : Div Zs :=
  ⟨fun x y =>
    ⟨round ((x * star y).re / QuadraticAlgebra.norm y : ℚ),
      round ((x * star y).im / QuadraticAlgebra.norm y : ℚ)⟩⟩

theorem div_def (x y : Zs) :
    x / y = ⟨round ((x * star y).re / QuadraticAlgebra.norm y : ℚ),
      round ((x * star y).im / QuadraticAlgebra.norm y : ℚ)⟩ := rfl

instance : Mod Zs := ⟨fun x y => x - y * (x / y)⟩

theorem mod_def (x y : Zs) : x % y = x - y * (x / y) := rfl

theorem norm_star' (z : Zs) : QuadraticAlgebra.norm (star z) = QuadraticAlgebra.norm z :=
  QuadraticAlgebra.norm_star z

/-- `|N(x % y)| < |N(y)|` for `y ≠ 0`. -/
theorem abs_norm_mod_lt (x : Zs) {y : Zs} (hy : y ≠ 0) :
    |QuadraticAlgebra.norm (x % y)| < |QuadraticAlgebra.norm y| := by
  set N := QuadraticAlgebra.norm y with hN
  have hN0 : N ≠ 0 := norm_ne_zero hy
  have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast hN0
  set w := x * star y with hw
  set q := x / y with hq
  -- `(x - y q) s̄(y) = w - N q`
  have key : (x % y) * star y = w - (N : Zs) * q := by
    rw [mod_def, sub_mul, hw, mul_comm y, mul_assoc, ← QuadraticAlgebra.algebraMap_norm_eq_mul_star,
      eq_intCast, hq, hN]
    ring
  have hnorm : QuadraticAlgebra.norm (x % y) * N = QuadraticAlgebra.norm (w - (N : Zs) * q) := by
    rw [← key, map_mul, norm_star']
  set e₁ : ℚ := (w.re : ℚ) / N - round ((w.re : ℚ) / N) with he₁
  set e₂ : ℚ := (w.im : ℚ) / N - round ((w.im : ℚ) / N) with he₂
  have h₁ : |e₁| ≤ 1 / 2 := abs_sub_round _
  have h₂ : |e₂| ≤ 1 / 2 := abs_sub_round _
  have hq_re : (q.re : ℚ) = round ((w.re : ℚ) / N) := by rw [hq, div_def]
  have hq_im : (q.im : ℚ) = round ((w.im : ℚ) / N) := by rw [hq, div_def]
  have hcomp : ((QuadraticAlgebra.norm (w - (N : Zs) * q) : ℤ) : ℚ) = (N : ℚ) ^ 2 * (e₁ ^ 2 - 2 * e₂ ^ 2) := by
    rw [norm_eq]
    have hre : ((w - (N : Zs) * q).re : ℚ) = N * e₁ := by
      simp only [QuadraticAlgebra.re_sub, QuadraticAlgebra.re_mul, QuadraticAlgebra.re_intCast,
        QuadraticAlgebra.im_intCast]
      push_cast
      rw [hq_re, he₁]; field_simp; ring
    have him : ((w - (N : Zs) * q).im : ℚ) = N * e₂ := by
      simp only [QuadraticAlgebra.im_sub, QuadraticAlgebra.im_mul, QuadraticAlgebra.re_intCast,
        QuadraticAlgebra.im_intCast]
      push_cast
      rw [hq_im, he₂]; field_simp; ring
    push_cast
    rw [hre, him]; ring
  have hbound : |e₁ ^ 2 - 2 * e₂ ^ 2| < 1 := by
    have a1 : e₁ ^ 2 ≤ 1 / 4 := by
      have := sq_le_sq' (abs_le.mp h₁).1 (abs_le.mp h₁).2; nlinarith
    have a2 : e₂ ^ 2 ≤ 1 / 4 := by
      have := sq_le_sq' (abs_le.mp h₂).1 (abs_le.mp h₂).2; nlinarith
    rw [abs_lt]; constructor <;> nlinarith [sq_nonneg e₁, sq_nonneg e₂]
  have hNpos : (0 : ℚ) < |(N : ℚ)| := abs_pos.mpr hNq
  have : |((QuadraticAlgebra.norm (x % y) : ℤ) : ℚ)| * |(N : ℚ)| < |(N : ℚ)| * |(N : ℚ)| := by
    rw [← abs_mul]
    have e : ((QuadraticAlgebra.norm (x % y) : ℤ) : ℚ) * N = (N : ℚ) ^ 2 * (e₁ ^ 2 - 2 * e₂ ^ 2) := by
      rw [← hcomp]; exact_mod_cast hnorm
    rw [e, abs_mul, abs_pow, ← pow_two]
    calc |(N : ℚ)| ^ 2 * |e₁ ^ 2 - 2 * e₂ ^ 2| < |(N : ℚ)| ^ 2 * 1 :=
          mul_lt_mul_of_pos_left hbound (by positivity)
      _ = |(N : ℚ)| ^ 2 := mul_one _
  have := lt_of_mul_lt_mul_right this hNpos.le
  exact_mod_cast this

theorem natAbs_norm_mod_lt (x : Zs) {y : Zs} (hy : y ≠ 0) :
    (QuadraticAlgebra.norm (x % y)).natAbs < (QuadraticAlgebra.norm y).natAbs := by
  have := abs_norm_mod_lt x hy
  zify; exact this

theorem natAbs_norm_le_mul (x : Zs) {y : Zs} (hy : y ≠ 0) :
    (QuadraticAlgebra.norm x).natAbs ≤ (QuadraticAlgebra.norm (x * y)).natAbs := by
  rw [map_mul, Int.natAbs_mul]
  exact Nat.le_mul_of_pos_right _ (Int.natAbs_pos.mpr (norm_ne_zero hy))

/-- `ℤ[s]` is a Euclidean domain for `|N|`. -/
instance euclideanDomain : EuclideanDomain Zs :=
  { (inferInstance : CommRing Zs), (inferInstance : Nontrivial Zs) with
    quotient := (· / ·)
    remainder := (· % ·)
    quotient_zero := fun x => by
      rw [div_def]; ext <;> simp
    quotient_mul_add_remainder_eq := fun x y => by rw [mod_def]; ring
    r := _
    r_wellFounded := (measure (Int.natAbs ∘ QuadraticAlgebra.norm)).wf
    remainder_lt := natAbs_norm_mod_lt
    mul_left_not_lt := fun a _ hb0 => not_lt_of_ge <| natAbs_norm_le_mul a hb0 }

end Zs

/-- `ℤ[s]` is a principal ideal domain. -/
instance Zs.isPrincipalIdealRing : IsPrincipalIdealRing Zs := inferInstance

/-- `ℤ[s]` is a unique factorization domain. -/
instance Zs.uniqueFactorizationMonoid : UniqueFactorizationMonoid Zs := inferInstance

end ZInQ
