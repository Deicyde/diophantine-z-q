import ZInQKernel.Contrib.OneProof.RC.EvenUnary.Finite
import ZInQKernel.Contrib.OneProof.RC.EvenUnary.Resum
import ZInQKernel.Contrib.OneProof.RC.HalfIntegral.ThetaPoisson

/-! The weighted comparison with ordinary theta at a positive lower-left
entry in the intrinsic level (tex 9548–9555, 9623–9625). -/

noncomputable section

set_option maxHeartbeats 1200000

namespace ZInQ.Manuscript.RC.EvenUnary

open Complex HalfIntegral OldStageLaw
open scoped Real

theorem weightedTheta_rational_modes {B C : ℕ} [NeZero B] [NeZero C]
    (hBC : B ∣ C) (v : ZMod B → ℂ) (a : ℤ) {τ : ℂ} (hτ : 0 < τ.im) :
    weightedTheta v (2 * (a : ℂ) / C + τ / (C : ℂ) ^ 2) =
      ((C : ℂ) * ((1 / (-I * τ) ^ (1 / 2 : ℂ)) / τ)) *
        ∑' n : ℤ, weightedQuadraticFourier hBC v (a : ZMod C) (n : ZMod C) *
          ((n : ℂ) * exp (π * I * (n : ℂ)^2 * (-1 / τ))) := by
  rw [weightedTheta_rational_resum hBC v a hτ]
  congr 1
  have hτ' : 0 < (-1 / τ).im := by
    have hz : τ ≠ 0 := fun h => by simp [h] at hτ
    rw [neg_div, neg_im, one_div, inv_im, neg_div, neg_neg]
    exact div_pos hτ (normSq_pos.mpr hz)
  simp_rw [linearTheta, ← tsum_mul_left]
  rw [← Summable.tsum_finsetSum (fun r _ => (linearTheta_hasSum ((r.val : ℂ) / C) hτ').summable.mul_left _)]
  apply tsum_congr
  intro n
  rw [weightedQuadraticFourier, Finset.sum_mul]
  refine Finset.sum_congr rfl fun r _ => ?_
  have he : exp (2 * π * I * (n : ℂ) * ((r.val : ℂ) / C)) =
      ZMod.stdAddChar ((n : ZMod C) * r) := by
    rw [show (n : ZMod C) * r = ((n * (r.val : ℤ) : ℤ) : ZMod C) by simp,
      ZMod.stdAddChar_coe]
    congr 1
    push_cast
    ring
  rw [jacobiTheta₂_term, Complex.exp_add, he, AddChar.map_add_eq_mul, mul_comm (n : ZMod C)]
  ring

private theorem tsum_even_odd (f : ℤ → ℂ) (hf : Summable f) :
    (∑' n, f n) = (∑' n : ℤ, f (2*n)) + (∑' n : ℤ, f (2*n+1)) := by
  let e : Fin 2 × ℤ ≃ ℤ := (intResidues 2).symm
  have he : Summable (fun p => f (e p)) := e.summable_iff.mpr hf
  rw [← e.tsum_eq f, he.tsum_prod, tsum_fintype]
  change (∑ r : Fin 2, ∑' n : ℤ, f (e (r,n))) = _
  rw [Fin.sum_univ_two]
  have hzero (n : ℤ) : e (0,n) = 2*n := zero_add _
  have hone (n : ℤ) : e (1,n) = 2*n+1 := by change (1 : ℤ) + 2*n = _; ring
  simp only [hzero, hone]

/-- At level divisible by `4B²`, the weighted residue sum produces
`v(d)(Cz+d)` times the scalar of ordinary theta. This is the relative
Poisson law before evaluation of the ordinary quadratic sum. -/
theorem weightedTheta_at_cusp {B k : ℕ} [NeZero B] [NeZero (4 * (B ^ 2 * k))]
    (hBC : B ∣ 4 * (B ^ 2 * k)) (v : DirichletCharacter ℂ B) (hv : v.Odd)
    (a d : ℤ) {z : ℂ} (hz : 0 < z.im)
    (had : (a : ZMod (4 * (B ^ 2 * k))) * d = 1) :
    let C : ℕ := 4 * (B ^ 2 * k)
    let t := z / 2 + (d : ℂ) / (2 * C)
    weightedTheta v (2 * (a : ℂ) / C - 2 / ((C : ℂ) * ((C : ℂ) * z + d))) =
      v d * ((C : ℂ) * z + d) *
        ((1 / (-I * (-1 / t)) ^ (1 / 2 : ℂ)) *
          quadraticFourier (a : ZMod C) 0) * weightedTheta v (2 * z) := by
  let C := 4 * (B ^ 2 * k)
  let t : ℂ := z / 2 + (d : ℂ) / (2 * C)
  have hv' : v (-1) = -1 := hv
  have hC : (C : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne C)
  have ht : 0 < t.im := by
    dsimp [t]
    rw [show (d : ℂ) / (2 * (C : ℂ)) = (((d : ℝ) / (2 * C) : ℝ) : ℂ) by push_cast; rfl,
      ofReal_im, add_zero, show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, div_ofReal_im]
    positivity
  have ht₀ : t ≠ 0 := fun h => by simp [h] at ht
  have ht' : 0 < (-1 / t).im := by
    rw [neg_div, neg_im, one_div, inv_im, neg_div, neg_neg]
    exact div_pos ht (normSq_pos.mpr ht₀)
  have hI : -1 / (-1 / t) = t := by field_simp
  have hD : (C : ℂ) * z + d ≠ 0 := by
    have h : (C : ℂ) * z + d = 2 * C * t := by dsimp [t]; field_simp
    rw [h]
    exact mul_ne_zero (mul_ne_zero two_ne_zero hC) ht₀
  change weightedTheta v (2 * (a : ℂ) / C - 2 / ((C : ℂ) * ((C : ℂ) * z + d))) = _
  have harg : 2 * (a : ℂ) / C - 2 / ((C : ℂ) * ((C : ℂ) * z + d)) =
      2 * (a : ℂ) / C + (-1 / t) / (C : ℂ)^2 := by
    dsimp [t] at ht₀ ⊢
    field_simp; ring
  rw [harg, weightedTheta_rational_modes hBC v a ht', hI]
  let f (n : ℤ) := weightedQuadraticFourier hBC v (a : ZMod C) (n : ZMod C) *
    ((n : ℂ) * exp (π * I * (n : ℂ)^2 * t))
  have hf : Summable f := by
    let v' (x : ZMod C) := weightedQuadraticFourier hBC v (a : ZMod C) x
    simpa only [f, v', jacobiTheta₂_term, mul_zero, zero_add] using
      (weightedTheta_hasSum v' ht).summable
  have ho (n : ℤ) : f (2*n+1) = 0 := by
    dsimp [f]
    rw [weightedQuadraticFourier_odd B k hBC v _ _ ⟨n, by ring⟩, zero_mul]
  have he (n : ℤ) : f (2*n) =
      ((-2 : ℂ) * v d * quadraticFourier (a : ZMod C) 0) *
        (v (n : ZMod B) * ((n : ℂ) * jacobiTheta₂_term n 0 (2*z))) := by
    dsimp only [f]
    simp only [Int.cast_mul, Int.cast_ofNat]
    rw [weightedQuadraticFourier_even B k hBC had]
    have hres : (ZMod.castHom hBC (ZMod B)) (-((d : ZMod C) * (n : ZMod C))) =
         (-1) * ((d : ZMod B) * (n : ZMod B)) := by
      rw [map_neg, map_mul, map_intCast, map_intCast]
      ring
    rw [hres, map_mul v, map_mul v, hv']
    have hphase : ZMod.stdAddChar (-((d : ZMod C) * (n : ZMod C)^2)) *
        exp (π * I * ((2 : ℂ) * (n : ℂ))^2 * t) =
          jacobiTheta₂_term n 0 (2*z) := by
      rw [show -((d : ZMod C) * (n : ZMod C)^2) = ((-(d * n^2) : ℤ) : ZMod C) by simp,
        ZMod.stdAddChar_coe, ← exp_add, jacobiTheta₂_term, mul_zero, zero_add]
      congr 1
      dsimp [t]
      push_cast
      field_simp
      ring
    rw [← hphase]
    push_cast
    ring
  change _ * (∑' n, f n) = _
  rw [tsum_even_odd f hf]
  simp_rw [he, ho]
  rw [tsum_zero, add_zero, tsum_mul_left, ← weightedTheta]
  have hfac : (C : ℂ) * ((1 / (-I * (-1 / t)) ^ (1 / 2 : ℂ)) / (-1 / t)) *
      (-2 * v d * quadraticFourier (a : ZMod C) 0) =
    v d * ((C : ℂ) * z + d) *
      ((1 / (-I * (-1 / t)) ^ (1 / 2 : ℂ)) * quadraticFourier (a : ZMod C) 0) := by
    have hi : (-1 / t)⁻¹ = -t := by rw [neg_div, ← neg_inv, inv_div, div_one]
    rw [div_eq_mul_inv, hi]
    dsimp [t]
    field_simp
  rw [← mul_assoc, hfac]

end ZInQ.Manuscript.RC.EvenUnary
