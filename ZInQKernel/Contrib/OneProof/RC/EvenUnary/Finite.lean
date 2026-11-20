import ZInQKernel.Contrib.OneProof.RC.HalfIntegral.ThetaGauss
import Mathlib.Tactic

/-! The finite phase in weighted Poisson summation. At a denominator
divisible by four times the square of the coefficient period, the
quadratic sum on each nonzero fiber of reduction to the period vanishes. -/

noncomputable section

set_option maxHeartbeats 800000

namespace ZInQ.Manuscript.RC.EvenUnary

open Complex HalfIntegral
open scoped Real

def weightedQuadraticFourier {B C : ℕ} [NeZero C] (hBC : B ∣ C)
    (v : ZMod B → ℂ) (a n : ZMod C) : ℂ :=
  ∑ x : ZMod C, v (ZMod.castHom hBC (ZMod B) x) * ZMod.stdAddChar (a * x ^ 2 + n * x)

private theorem phase_reduction (B k : ℕ) [NeZero B] [NeZero (4 * (B ^ 2 * k))]
    (hBC : B ∣ 4 * (B ^ 2 * k)) (x : ZMod (4 * (B ^ 2 * k))) :
    ZMod.stdAddChar ((4 * (B : ZMod (4 * (B ^ 2 * k))) * (k : ZMod (4 * (B ^ 2 * k)))) * x) =
      ZMod.stdAddChar (ZMod.castHom hBC (ZMod B) x) := by
  have hB : (B : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne B)
  have hk : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr
    (fun h => NeZero.ne (4 * (B ^ 2 * k)) (by simp [h]))
  obtain ⟨m, rfl⟩ := ZMod.intCast_surjective x
  rw [show (4 * (B : ZMod (4 * (B ^ 2 * k))) * (k : ZMod (4 * (B ^ 2 * k)))) * (m : ZMod (4 * (B ^ 2 * k))) =
    (((4 * (B : ℤ) * k) * m : ℤ) : ZMod (4 * (B ^ 2 * k))) by push_cast; ring,
    map_intCast (ZMod.castHom hBC (ZMod B)), ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  field_simp

/-- After summing over the quadratic phase, only the zero residue modulo
the period contributes. The weight may be any function on the period. -/
theorem quadratic_zero_residue (B k : ℕ) [NeZero B] [NeZero (4 * (B ^ 2 * k))]
    (hBC : B ∣ 4 * (B ^ 2 * k)) {a d : ZMod (4 * (B ^ 2 * k))}
    (had : a * d = 1) (v : ZMod B → ℂ) :
    weightedQuadraticFourier hBC v a 0 = v 0 * quadraticFourier a 0 := by
  classical
  let C := 4 * (B ^ 2 * k)
  let proj := ZMod.castHom hBC (ZMod B)
  let t : ZMod C := 2 * B * k
  have hpt : proj t = 0 := by simp [t, proj, map_mul]
  have hc : (4 * (B : ZMod C)^2 * (k : ZMod C)) = 0 := by
    rw [← show (C : ZMod C) = 4 * (B : ZMod C)^2 * (k : ZMod C) by change (((4 * (B ^ 2 * k) : ℕ)) : ZMod C) = _; push_cast; ring]
    exact ZMod.natCast_self C
  have ht : t^2 = 0 := by dsimp [t]; linear_combination (k : ZMod C) * hc
  let G (s : ZMod B) := ∑ x : ZMod C,
    if proj x = s then ZMod.stdAddChar (a * x^2) else 0
  have hG (s : ZMod B) (hs : s ≠ 0) : G s = 0 := by
    let ε := ZMod.stdAddChar (proj a * s)
    have he : G s = ε * G s := by
      dsimp [G]
      rw [Finset.mul_sum]
      refine Fintype.sum_equiv (Equiv.subRight t) _ _ fun x => ?_
      have hp : proj (x - t) = proj x := by rw [map_sub, hpt, sub_zero]
      simp only [Equiv.subRight_apply, hp]
      split_ifs with hx
      · have hsq : a * (x - t) ^ 2 = a * x ^ 2 - (4 * B * k) * (a * x) := by
          dsimp [t] at ht ⊢
          linear_combination a * ht
        have hphase : ZMod.stdAddChar ((4 * B * k) * (a * x) : ZMod C) = ε := by
          rw [phase_reduction B k hBC, show proj (a * x) = proj a * proj x from map_mul _ _ _,
            hx]
        rw [hsq, sub_eq_add_neg, ← hphase, ← AddChar.map_add_eq_mul]
        congr 1
        ring
      · simp
    have hε : ε ≠ 1 := by
      intro hz
      have h0 : proj a * s = 0 := ZMod.injective_stdAddChar
        (hz.trans (AddChar.map_zero_eq_one (ZMod.stdAddChar : AddChar (ZMod B) ℂ)).symm)
      have hh : proj a * proj d = 1 := by rw [← map_mul, had, map_one]
      apply hs
      linear_combination proj d * h0 - s * hh
    exact (mul_eq_zero.mp (show (1 - ε) * G s = 0 by linear_combination he)).resolve_left
      (sub_ne_zero.mpr hε.symm)
  have hf (w : ZMod B → ℂ) :
      weightedQuadraticFourier hBC w a 0 = ∑ s, w s * G s := by
    unfold weightedQuadraticFourier G
    simp only [zero_mul, add_zero, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rfl
  have hcollapse (w : ZMod B → ℂ) :
      weightedQuadraticFourier hBC w a 0 = w 0 * G 0 := by
    rw [hf, Finset.sum_eq_single 0]
    · intro s _ hs
      rw [hG s hs, mul_zero]
    · simp
  rw [hcollapse]
  have hconst := hcollapse (fun _ => 1)
  simpa [weightedQuadraticFourier, quadraticFourier] using (congrArg (v 0 * ·) hconst).symm

/-- Completion of the square, with the remaining periodic weight evaluated
on the one surviving residue. -/
theorem weightedQuadraticFourier_even (B k : ℕ) [NeZero B] [NeZero (4 * (B ^ 2 * k))]
    (hBC : B ∣ 4 * (B ^ 2 * k)) {a d : ZMod (4 * (B ^ 2 * k))}
    (had : a * d = 1) (v : ZMod B → ℂ) (n : ZMod (4 * (B ^ 2 * k))) :
    weightedQuadraticFourier hBC v a (2 * n) =
      ZMod.stdAddChar (-(d * n ^ 2)) *
        v (ZMod.castHom hBC (ZMod B) (-(d * n))) * quadraticFourier a 0 := by
  have h :
      weightedQuadraticFourier hBC v a (2 * n) =
        ZMod.stdAddChar (-(d * n ^ 2)) *
          weightedQuadraticFourier hBC (fun x => v (x - ZMod.castHom hBC (ZMod B) (d * n))) a 0 := by
    rw [weightedQuadraticFourier, weightedQuadraticFourier, Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.addRight (d * n)) _ _ fun x => ?_
    simp only [Equiv.coe_addRight, zero_mul, add_zero, map_add, add_sub_cancel_right]
    calc
      _ = v (ZMod.castHom hBC (ZMod B) x) *
          (ZMod.stdAddChar (-(d * n ^ 2)) * ZMod.stdAddChar (a * (x + d * n) ^ 2)) := by
        rw [← AddChar.map_add_eq_mul]
        congr 2
        linear_combination -(2 * n * x + d * n ^ 2) * had
      _ = _ := by ring
  rw [h, quadratic_zero_residue B k hBC had, zero_sub, map_neg (ZMod.castHom hBC (ZMod B)), mul_assoc]

/-- Translation by half the modulus negates odd frequencies, while
leaving the weight unchanged. -/
theorem weightedQuadraticFourier_odd (B k : ℕ) [NeZero (4 * (B ^ 2 * k))]
    (hBC : B ∣ 4 * (B ^ 2 * k)) (v : ZMod B → ℂ) (a : ZMod (4 * (B ^ 2 * k)))
    (n : ℤ) (hn : Odd n) : weightedQuadraticFourier hBC v a (n : ZMod (4 * (B ^ 2 * k))) = 0 := by
  let C := 4 * (B ^ 2 * k)
  let m := B ^ 2 * k
  let t : ZMod C := 2 * m
  let proj := ZMod.castHom hBC (ZMod B)
  have hpt : proj t = 0 := by simp [t, m, proj, map_mul, pow_two]
  have hC : 4 * (m : ZMod C) = 0 := by
    rw [← show (C : ZMod C) = 4 * (m : ZMod C) by change (((4 * m : ℕ)) : ZMod C) = _; push_cast; rfl]
    exact ZMod.natCast_self C
  have ht : 2 * t = 0 := by dsimp [t]; linear_combination hC
  have hsq : t ^ 2 = 0 := by dsimp [t]; linear_combination (m : ZMod C) * hC
  have hphase : ZMod.stdAddChar t = -1 := by
    have hm : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr
      (fun h => NeZero.ne C (show 4 * m = 0 by simp [h]))
    rw [show t = ((2 * (m : ℤ) : ℤ) : ZMod C) by push_cast; rfl, ZMod.stdAddChar_coe,
      ← Complex.exp_pi_mul_I]
    congr 1
    change _ / ((4 * m : ℕ) : ℂ) = _
    push_cast
    field_simp
    ring
  obtain ⟨l, hl⟩ := hn
  have hn' : (n : ZMod C) * t = t := by
    rw [hl]
    push_cast
    linear_combination (l : ZMod C) * ht
  have hEq : weightedQuadraticFourier hBC v a (n : ZMod C) =
      -(weightedQuadraticFourier hBC v a (n : ZMod C)) := by
    unfold weightedQuadraticFourier
    rw [← Finset.sum_neg_distrib]
    refine Fintype.sum_equiv (Equiv.addRight t) _ _ fun x => ?_
    have he : a * (x + t) ^ 2 + (n : ZMod C) * (x + t) =
        (a * x ^ 2 + (n : ZMod C) * x) + t := by
      linear_combination a * x * ht + a * hsq + hn'
    have hproj : (ZMod.castHom hBC (ZMod B)) (x + t) =
        (ZMod.castHom hBC (ZMod B)) x := by
      change proj (x + t) = proj x
      rw [map_add, hpt, add_zero]
    rw [Equiv.coe_addRight, hproj, he, AddChar.map_add_eq_mul (y := t), hphase,
      mul_neg_one, mul_neg, neg_neg]
  linear_combination hEq / 2

end ZInQ.Manuscript.RC.EvenUnary
