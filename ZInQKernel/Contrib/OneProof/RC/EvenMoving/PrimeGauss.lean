import ZInQKernel.Contrib.OneProof.RC.HalfIntegral.ThetaPoisson
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.GaussSum

/-! Poisson resummation at an odd prime denominator. The needed comparison
uses a ratio of two quadratic sums and avoids an absolute Gauss sum sign. -/

noncomputable section

namespace ZInQ.Manuscript.RC.EvenMoving

open HalfIntegral Complex
open scoped Real BigOperators

private theorem quadraticFourier_zero_eq_gauss {q : ℕ} [Fact q.Prime] (hq : q ≠ 2)
    {a : ZMod q} (ha : a ≠ 0) :
    quadraticFourier a 0 =
      gaussSum ((quadraticChar (ZMod q)).ringHomComp (Int.castRingHom ℂ))
        (ZMod.stdAddChar.mulShift a) := by
  classical
  let ψ : AddChar (ZMod q) ℂ := ZMod.stdAddChar.mulShift a
  have hz : ψ ≠ 1 := by
    rw [ne_eq, AddChar.mulShift_unit_eq_one_iff _ (ha.isUnit)]
    intro he
    have hone : ZMod.stdAddChar (1 : ZMod q) = 1 := by rw [he, AddChar.one_apply]
    exact one_ne_zero (ZMod.injective_stdAddChar (hone.trans ZMod.stdAddChar.map_zero_eq_one.symm))
  have hzero : (∑ x : ZMod q, ψ x) = 0 := AddChar.sum_eq_zero_of_ne_one hz
  calc
    quadraticFourier a 0 = ∑ x : ZMod q, ψ (x ^ 2) := by
      simp [quadraticFourier, ψ]
    _ = ∑ y : ZMod q, ∑ x ∈ (Finset.univ.filter fun x : ZMod q => x ^ 2 = y), ψ y := by
      exact (Finset.sum_fiberwise' Finset.univ (fun x : ZMod q => x ^ 2) ψ).symm
    _ = ∑ y : ZMod q, (((quadraticChar (ZMod q) y + 1 : ℤ) : ℂ) * ψ y) := by
      refine Finset.sum_congr rfl fun y _ => ?_
      have hc := quadraticChar_card_sqrts (F := ZMod q) (by rwa [ZMod.ringChar_zmod_n]) y
      rw [Finset.sum_const, nsmul_eq_mul]
      congr 1
      exact_mod_cast (by simpa only [Set.toFinset_ofPred] using hc :
        (↑(Finset.univ.filter (fun x : ZMod q => x ^ 2 = y)).card : ℤ) =
          quadraticChar (ZMod q) y + 1)
    _ = _ := by
      simp only [Int.cast_add, Int.cast_one, add_mul, one_mul, Finset.sum_add_distrib, hzero,
        add_zero, gaussSum, MulChar.ringHomComp_apply, ψ]
      rfl

/-- Changing the numerator by a unit multiplies the Gauss sum by the corresponding
Legendre symbol, with no choice of the square root of the Gauss sum. -/
theorem quadraticFourier_prime_scale {q : ℕ} [Fact q.Prime] (hq : q ≠ 2)
    {a s : ZMod q} (ha : a ≠ 0) (hs : s ≠ 0) :
    quadraticFourier (a * s) 0 = (quadraticChar (ZMod q) s : ℂ) * quadraticFourier a 0 := by
  let χ := (quadraticChar (ZMod q)).ringHomComp (Int.castRingHom ℂ)
  rw [quadraticFourier_zero_eq_gauss hq (mul_ne_zero ha hs), quadraticFourier_zero_eq_gauss hq ha]
  have h := gaussSum_mulShift χ (ZMod.stdAddChar.mulShift a) hs.isUnit.unit
  rw [AddChar.mulShift_mulShift, IsUnit.unit_spec] at h
  change (quadraticChar (ZMod q) s : ℂ) * _ = _ at h
  have hsq : ((quadraticChar (ZMod q) s : ℤ) : ℂ) ^ 2 = 1 := by
    exact_mod_cast quadraticChar_sq_one hs
  calc
    _ = (quadraticChar (ZMod q) s : ℂ) ^ 2 *
        gaussSum χ (ZMod.stdAddChar.mulShift (a * s)) := by rw [hsq, one_mul]
    _ = _ := by rw [pow_two, mul_assoc, h]

/-- Resummation of theta at `b/q` in the coordinates of a matrix whose
lower-left entry is `4*k`. The determinant condition is used modulo `q`. -/
theorem theta_right_cusp {q : ℕ} [Fact q.Prime] (hq : q ≠ 2)
    (b k : ℤ) (hb : (b : ZMod q) * (-(4 * (k : ZMod q))) = 1)
    {t w : ℂ} (ht : 0 < t.im)
    (hw : -1 / t = w - 2 * (k : ℂ) / q) :
    jacobiTheta (2 * b / q + t / (q : ℂ) ^ 2) =
      (1 / (-I * t) ^ (1 / 2 : ℂ)) * quadraticFourier (b : ZMod q) 0 * jacobiTheta w := by
  have h2 : (2 : ZMod q) ≠ 0 := by
    change ((2 : ℕ) : ZMod q) ≠ 0
    rw [ne_eq, ZMod.natCast_eq_zero_iff]
    exact fun hd => hq ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp hd)
  rw [jacobiTheta_rational_resum b ht, mul_assoc]
  apply congrArg (fun x : ℂ => (1 / (-I * t) ^ (1 / 2 : ℂ)) * x)
  rw [jacobiTheta, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  let x : ZMod q := (n : ZMod q) / 2
  have hx : 2 * x = (n : ZMod q) := by dsimp [x]; field_simp
  have hphase : -( (-(4 * (k : ZMod q))) * x ^ 2) = ((k * n ^ 2 : ℤ) : ZMod q) := by
    push_cast
    rw [← hx]
    ring
  have hf : quadraticFourier (b : ZMod q) (n : ZMod q) =
      ZMod.stdAddChar ((k * n ^ 2 : ℤ) : ZMod q) * quadraticFourier (b : ZMod q) 0 := by
    conv_lhs => rw [← hx]
    rw [quadraticFourier_even hb, hphase]
  rw [hf, ZMod.stdAddChar_coe, hw, mul_comm _ (quadraticFourier _ 0), mul_assoc,
    ← Complex.exp_add]
  congr 2
  push_cast
  ring

end ZInQ.Manuscript.RC.EvenMoving
