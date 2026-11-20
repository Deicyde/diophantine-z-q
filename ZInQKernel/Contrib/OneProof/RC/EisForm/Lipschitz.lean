import ZInQKernel.Contrib.OneProof.RC.EisForm.Expansion
import Mathlib.Analysis.Fourier.ZMod

/-! The weight-two Lipschitz construction of the positive Eisenstein series.
The finite character weighting and the regrouping are on-the-spot (c),
at the divisor-sum step of tex 9862–9864. -/

noncomputable section

namespace ZInQ.Manuscript.RC.EisForm

open O12Eisenstein UpperHalfPlane Complex
open scoped Real

variable {m₁ m₂ : ℕ}

def lambertTerm (a : DirichletCharacter ℂ m₁) (b : DirichletCharacter ℂ m₂)
    (r : ℂ) (u v : ℕ+) : ℂ :=
  a (u.val : ZMod m₁) * (b (v.val : ZMod m₂) * (v.val : ℂ)) * r ^ (u.val * v.val)

private theorem summable_lambertTerm (a : DirichletCharacter ℂ m₁)
    (b : DirichletCharacter ℂ m₂) {r : ℂ} (hr : ‖r‖ < 1) :
    Summable fun x : ℕ+ × ℕ+ => lambertTerm a b r x.1 x.2 := by
  apply Summable.of_norm_bounded (summable_prod_mul_pow 1 hr).norm
  intro x
  simp only [lambertTerm, norm_mul, norm_pow, pow_one, Complex.norm_natCast]
  calc
    _ ≤ (1 : ℝ) * (1 * (x.2.val : ℝ)) * ‖r‖ ^ (x.1.val * x.2.val) := by
      gcongr <;> apply DirichletCharacter.norm_le_one
    _ = _ := by simp

/-- Regroup the normally convergent weighted Lambert series by the product
of its two positive indices. -/
theorem series_eq_lambert (a : DirichletCharacter ℂ m₁)
    (b : DirichletCharacter ℂ m₂) (C : ℂ) (z : ℍ) :
    series a b C z = C + ∑' u : ℕ+, ∑' v : ℕ+, lambertTerm a b (Function.Periodic.qParam 1 z) u v := by
  let r := Function.Periodic.qParam 1 z
  have hr : ‖r‖ < 1 := Function.Periodic.norm_qParam_lt_one one_pos z.im_pos
  have hs := summable_lambertTerm a b hr
  have hs' : Summable (fun x : (n : ℕ+) × n.val.divisorsAntidiagonal =>
      lambertTerm a b r (sigmaAntidiagonalEquivProd x).1 (sigmaAntidiagonalEquivProd x).2) :=
    sigmaAntidiagonalEquivProd.summable_iff.mpr hs
  rw [← hs.tsum_prod, ← sigmaAntidiagonalEquivProd.tsum_eq, hs'.tsum_sigma]
  have h (n : ℕ+) :
      ∑' x : n.val.divisorsAntidiagonal,
          lambertTerm a b r (divisorsAntidiagonalFactors n x).1
            (divisorsAntidiagonalFactors n x).2 = divisorCoeff a b n.val * r ^ n.val := by
    rw [tsum_fintype, divisorCoeff, Finset.sum_mul, Finset.univ_eq_attach]
    conv_rhs => rw [← Finset.sum_attach]
    exact Finset.sum_congr rfl fun x _ => by
      change _ * r ^ (x.val.1 * x.val.2) = _ * r ^ n.val
      rw [(Nat.mem_divisorsAntidiagonal.mp x.property).1]
      rfl
  simp_rw [show ∀ x, (sigmaAntidiagonalEquivProd x) = divisorsAntidiagonalFactors x.1 x.2
    from fun _ => rfl, h]
  rw [(hasSum_series a b C z).tsum_eq.symm, Summable.tsum_eq_zero_add
    (hasSum_series a b C z).summable]
  simp only [seriesCoeff, pow_zero, smul_eq_mul, mul_one, Nat.succ_ne_zero, ite_false, ite_true]
  rw [tsum_pnat_eq_tsum_succ (f := fun n => divisorCoeff a b n * r ^ n)]

/-- Injective change of coefficient field keeps a character primitive. -/
theorem primitive_ringHomComp {D : Type*} [Field D] {m : ℕ} [NeZero m]
    (χ : DirichletCharacter D m) (c : D →+* ℂ) (h : χ.IsPrimitive) :
    DirichletCharacter.IsPrimitive (χ.ringHomComp c : DirichletCharacter ℂ m) := by
  let χ' : DirichletCharacter ℂ m := χ.ringHomComp c
  have hd : χ'.conductor ∣ m := χ'.conductor_dvd_level
  have hf : χ.FactorsThrough χ'.conductor := by
    apply (DirichletCharacter.factorsThrough_iff_ker_unitsMap hd).mpr
    intro u hu
    have he := (DirichletCharacter.factorsThrough_iff_ker_unitsMap hd).mp
      χ'.factorsThrough_conductor hu
    rw [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one] at he ⊢
    apply c.injective
    simpa only [χ', MulChar.ringHomComp_apply, map_one] using he
  change χ'.conductor = m
  have he := χ.conductor_dvd_of_mem_conductorSet (χ.mem_conductorSet_iff.mpr hf)
  rw [(DirichletCharacter.isPrimitive_def χ).mp h] at he
  exact Nat.dvd_antisymm hd he

section Rows

variable [NeZero m₂]

private def shift (z : ℍ) (u : ℕ+) (r : ZMod m₂) : ℍ :=
  ⟨(u.val : ℂ) * z + ((r.val : ℝ) / m₂ : ℝ), by
    simp only [Complex.add_im, Complex.mul_im, Complex.natCast_re, Complex.natCast_im,
      zero_mul, add_zero, Complex.ofReal_im]
    exact mul_pos (by exact_mod_cast u.2) z.im_pos⟩

private theorem qParam_shift_pow (z : ℍ) (u v : ℕ+) (r : ZMod m₂) :
    Function.Periodic.qParam 1 (shift z u r) ^ v.val =
      ZMod.stdAddChar (r * (v.val : ZMod m₂)) *
        Function.Periodic.qParam 1 z ^ (u.val * v.val) := by
  have he : r * (v.val : ZMod m₂) = ((r.val * v.val : ℕ) : ZMod m₂) := by simp
  rw [he, ← Int.cast_natCast (R := ZMod m₂), ZMod.stdAddChar_coe]
  simp only [Function.Periodic.qParam, Complex.ofReal_one, div_one, ← Complex.exp_nat_mul,
    Int.cast_natCast, shift]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The Eisenstein row obtained by a finite sum of translates of the
weight-two Lipschitz kernel. Its normalization uses the inverse character. -/
def lipschitzRow (b : DirichletCharacter ℂ m₂) (z : ℍ) (u : ℕ+) : ℂ :=
  ∑ r : ZMod m₂, b⁻¹ r * ∑' n : ℤ, 1 / ((shift z u r : ℂ) + n) ^ 2

private theorem lipschitzRow_eq (b : DirichletCharacter ℂ m₂) (hb : b.IsPrimitive)
    (z : ℍ) (u : ℕ+) :
    lipschitzRow b z u =
      ((-2 * Real.pi * Complex.I) ^ 2 * gaussSum b⁻¹ ZMod.stdAddChar) *
        ∑' v : ℕ+, b (v.val : ZMod m₂) * (v.val : ℂ) *
          Function.Periodic.qParam 1 z ^ (u.val * v.val) := by
  have hprim : b⁻¹.IsPrimitive := by simpa [DirichletCharacter.IsPrimitive,
    DirichletCharacter.conductor_inv] using hb
  have hSum (r : ZMod m₂) : Summable fun v : ℕ+ =>
      (v.val : ℂ) * Function.Periodic.qParam 1 (shift z u r) ^ v.val := by
    have hs := (summable_pow_mul_cexp 1 1 (shift z u r)).comp_injective
      (i := fun v : ℕ+ => v.val) PNat.coe_injective
    simpa [Function.Periodic.qParam, Function.comp_def] using! hs
  simp only [lipschitzRow, EisensteinSeries.qExpansion_identity_pnat (k := 1) (by decide),
    Nat.factorial_one, Nat.cast_one, div_one, pow_one]
  simp_rw [show ∀ w : ℍ, Complex.exp (2 * Real.pi * Complex.I * w) =
    Function.Periodic.qParam 1 w by intro w; simp [Function.Periodic.qParam]]
  simp_rw [← mul_assoc, ← tsum_mul_left]
  rw [← Summable.tsum_finsetSum (fun r _ => (hSum r).mul_left _)]
  refine tsum_congr fun v => ?_
  simp only [qParam_shift_pow]
  calc
    _ = ((-2 * Real.pi * Complex.I) ^ 2 *
        (∑ r : ZMod m₂, b⁻¹ r * ZMod.stdAddChar (r * (v.val : ZMod m₂)))) *
        ((v.val : ℂ) * Function.Periodic.qParam 1 z ^ (u.val * v.val)) := by
      rw [Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun _ _ => by ring
    _ = _ := by
      have hg := gaussSum_mulShift_of_isPrimitive ZMod.stdAddChar hprim (v.val : ZMod m₂)
      simp only [gaussSum, AddChar.mulShift_apply, inv_inv] at hg
      rw [show (∑ r : ZMod m₂, b⁻¹ r * ZMod.stdAddChar (r * (v.val : ZMod m₂))) =
        b (v.val : ZMod m₂) * gaussSum b⁻¹ ZMod.stdAddChar by
          simpa [gaussSum, mul_comm (v.val : ZMod m₂)] using hg]
      ring

private theorem gaussInv_ne_zero (b : DirichletCharacter ℂ m₂) (hb : b.IsPrimitive) :
    gaussSum b⁻¹ ZMod.stdAddChar ≠ 0 := by
  intro h
  have hprim : b⁻¹.IsPrimitive := by simpa [DirichletCharacter.IsPrimitive,
    DirichletCharacter.conductor_inv] using hb
  have he : ZMod.dft (⇑(b⁻¹)) = 0 := by
    funext r
    rw [hprim.fourierTransform_eq_inv_mul_gaussSum, h, mul_zero, Pi.zero_apply]
  have hb0 : (⇑(b⁻¹) : ZMod m₂ → ℂ) = 0 :=
    ZMod.dft.injective (he.trans ZMod.dft.map_zero.symm)
  have := congrFun hb0 1
  simp only [MulChar.map_one, Pi.zero_apply, one_ne_zero] at this

/-- The row sum in the Lipschitz construction with a separately specified constant. -/
def lipschitzSeries (a : DirichletCharacter ℂ m₁) (b : DirichletCharacter ℂ m₂)
    (C : ℂ) (z : ℍ) : ℂ :=
  C + ∑' u : ℕ+, a (u.val : ZMod m₁) *
    (lipschitzRow b z u / ((-2 * Real.pi * Complex.I) ^ 2 * gaussSum b⁻¹ ZMod.stdAddChar))

/-- For a primitive second character the convergent, normalized lattice rows
give the analytic series whose positive coefficients are the weight-two
divisor sums. This uses Mathlib's weight-two Lipschitz formula, before any
interchange of the two lattice directions. -/
theorem series_eq_lipschitz (a : DirichletCharacter ℂ m₁) (b : DirichletCharacter ℂ m₂)
    (hb : b.IsPrimitive) (C : ℂ) (z : ℍ) :
    series a b C z = lipschitzSeries a b C z := by
  rw [series_eq_lambert, lipschitzSeries]
  congr 1
  apply tsum_congr
  intro u
  have hN : (-2 * Real.pi * Complex.I) ^ 2 * gaussSum b⁻¹ ZMod.stdAddChar ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by simp [Real.pi_ne_zero])) (gaussInv_ne_zero b hb)
  rw [lipschitzRow_eq b hb, mul_comm (_ * gaussSum _ _) _, mul_div_cancel_right₀ _ hN,
    ← tsum_mul_left]
  exact tsum_congr fun v => by unfold lambertTerm; ring

end Rows


end ZInQ.Manuscript.RC.EisForm
