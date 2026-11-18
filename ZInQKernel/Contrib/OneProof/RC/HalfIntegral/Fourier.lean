import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Algebra.Field.ZMod

/-!
# Finite translation sums for Appendix E (tex 8101–8103)

Fourier inversion chooses the coefficients of the translation sum. For a primitive
character this is the manuscript's normalized Gauss sum. Inversion at the original
modulus also handles imprimitive characters: their zero values off the units give the
sieve directly. Using Fourier inversion for this combined step is provenance (c).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.HalfIntegral

open UpperHalfPlane Function
open scoped ZMod Manifold

/-- The Fourier weights of a coefficient multiplier on `ℤ/Nℤ`. -/
def translationWeights {N : ℕ} [NeZero N] (v : ZMod N → ℂ) : ZMod N → ℂ :=
  (N : ℂ)⁻¹ • 𝓕 v

/-- The representative of the translation indexed by `u`. -/
def residueShift {N : ℕ} (u : ZMod N) : ℝ := (u.val : ℝ) / N

/-- The same translation representative, as a rational number. -/
def ratShift {N : ℕ} (u : ZMod N) : ℚ := (u.val : ℚ) / N

theorem ratShift_cast {N : ℕ} (u : ZMod N) : (ratShift u : ℝ) = residueShift u := by
  simp [ratShift, residueShift]

/-- The finite sum of translates weighted by the Fourier transform of `v`. -/
def translationSum {N : ℕ} [NeZero N] (v : ZMod N → ℂ) (f : ℍ → ℂ) (z : ℍ) : ℂ :=
  ∑ u : ZMod N, translationWeights v u * f (residueShift u +ᵥ z)

theorem sum_translationWeights {N : ℕ} [NeZero N] (v : ZMod N → ℂ) (n : ZMod N) :
    ∑ u : ZMod N, translationWeights v u * ZMod.stdAddChar (u * n) = v n := by
  have h := congrFun (ZMod.dft.symm_apply_apply v) n
  rw [ZMod.invDFT_apply] at h
  simpa only [translationWeights, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc,
    mul_comm (ZMod.stdAddChar _), mul_comm n] using h

/-- Under multiplication of the translation index by the inverse square of a unit
the weight picks up the square of the character of the unit. -/
theorem translationWeights_unit {N : ℕ} [NeZero N] (ν : DirichletCharacter ℂ N)
    (d : (ZMod N)ˣ) (u : ZMod N) :
    translationWeights ν ((↑(d⁻¹ ^ 2) : ZMod N) * u) =
      ν d ^ 2 * translationWeights ν u := by
  have h := ZMod.dft_comp_unitMul (ν : ZMod N → ℂ) (d ^ 2) u
  have h' : (fun j : ZMod N ↦ ν ((↑(d ^ 2) : ZMod N) * j)) = ν d ^ 2 • (ν : ZMod N → ℂ) := by
    ext j
    simp [map_mul, map_pow]
  rw [h', ZMod.dft_const_smul] at h
  simpa only [translationWeights, inv_pow, Pi.smul_apply, smul_eq_mul,
    mul_left_comm (ν d ^ 2)] using congrArg ((N : ℂ)⁻¹ * ·) h.symm

/-- For a primitive character the weights use the Gauss sum of its inverse character,
which agrees with complex conjugation on character values. -/
theorem translationWeights_primitive {N : ℕ} [NeZero N] (ν : DirichletCharacter ℂ N)
    (hν : ν.IsPrimitive) (u : ZMod N) :
    translationWeights ν u = (gaussSum ν⁻¹ ZMod.stdAddChar)⁻¹ * ν⁻¹ u := by
  have hν' : (ν⁻¹).IsPrimitive := by
    rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]
    exact hν
  have hg (n : ZMod N) :
      𝓕 (ν⁻¹ : DirichletCharacter ℂ N) n = ν (-n) * gaussSum ν⁻¹ ZMod.stdAddChar := by
    simpa only [inv_inv] using hν'.fourierTransform_eq_inv_mul_gaussSum n
  have hG : gaussSum ν⁻¹ ZMod.stdAddChar ≠ 0 := by
    intro h0
    have hz : 𝓕 (ν⁻¹ : DirichletCharacter ℂ N) = 𝓕 (0 : ZMod N → ℂ) := by
      ext n
      simp [hg, h0]
    have hz' := congrFun (ZMod.dft.injective hz) 1
    simp at hz'
  have hh : 𝓕 (ν⁻¹ : DirichletCharacter ℂ N) =
      gaussSum ν⁻¹ ZMod.stdAddChar • fun n ↦ ν (-n) := by
    ext n
    simp only [hg, Pi.smul_apply, smul_eq_mul, mul_comm]
  have hs := congrFun (ZMod.dft_dft (ν⁻¹ : DirichletCharacter ℂ N)) (-u)
  conv_lhs at hs => rw [hh, ZMod.dft_const_smul, ZMod.dft_comp_neg]
  simp only [Pi.smul_apply, smul_eq_mul, neg_neg] at hs
  have hn : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  rw [translationWeights, Pi.smul_apply, smul_eq_mul]
  field_simp
  linear_combination hs

private theorem qParam_residueShift {N : ℕ} [NeZero N] (u : ZMod N) (z : ℍ) (n : ℕ) :
    Periodic.qParam 1 (↑(residueShift u +ᵥ z) : ℂ) ^ n =
      ZMod.stdAddChar (u * (n : ZMod N)) * Periodic.qParam 1 (z : ℂ) ^ n := by
  simp only [coe_vadd, Periodic.qParam, Complex.ofReal_one, div_one, mul_add, Complex.exp_add,
    mul_pow, ← Complex.exp_nat_mul]
  congr 1
  have hu : u * (n : ZMod N) = (((u.val * n : ℕ) : ℤ) : ZMod N) := by simp
  rw [hu, ZMod.stdAddChar_coe]
  unfold residueShift
  push_cast
  congr 1
  ring

/-- The translation sum has the everywhere convergent q-series of the
coefficientwise multiplier, whether or not `v` is primitive. -/
theorem hasSum_translationSum {N : ℕ} [NeZero N] (v : ZMod N → ℂ)
    {f : ℍ → ℂ} {a : ℕ → ℂ}
    (hf : ∀ z : ℍ, HasSum (fun n : ℕ ↦ a n • Periodic.qParam 1 (z : ℂ) ^ n) (f z))
    (z : ℍ) :
    HasSum (fun n : ℕ ↦ (v n * a n) • Periodic.qParam 1 (z : ℂ) ^ n)
      (translationSum v f z) := by
  classical
  have ht (u : ZMod N) := (hf (residueShift u +ᵥ z)).mul_left (translationWeights v u)
  have hs := hasSum_sum (s := (Finset.univ : Finset (ZMod N))) (fun u _ ↦ ht u)
  unfold translationSum
  convert hs using 1
  funext n
  simp only [smul_eq_mul, qParam_residueShift]
  simp_rw [show ∀ a b c d : ℂ, a * (b * (c * d)) = (a * c) * (b * d) by intros; ring]
  rw [← Finset.sum_mul, sum_translationWeights]
  ring

/-- An analytic q-expansion at zero identifies the coefficients computed by the translation sum. -/
theorem qExpansion_translationSum {N : ℕ} [NeZero N] (v : ZMod N → ℂ)
    {f : ℍ → ℂ} {a : ℕ → ℂ}
    (hf : ∀ z : ℍ, HasSum (fun n : ℕ ↦ a n • Periodic.qParam 1 (z : ℂ) ^ n) (f z))
    (ha : AnalyticAt ℂ (cuspFunction 1 (translationSum v f)) 0) (n : ℕ) :
    (qExpansion 1 (translationSum v f)).coeff n = v n * a n := by
  have h₁ := hasFPowerSeriesOnBall_cuspFunction one_pos ha (hasSum_translationSum v hf)
  have h := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ ↦ p n fun _ ↦ 1)
    (h₁.hasFPowerSeriesAt.eq_formalMultilinearSeries
      (ha.hasFPowerSeriesAt))
  simpa [FormalMultilinearSeries.apply_eq_prod_smul_coeff, qExpansion_coeff, div_eq_mul_inv, mul_comm] using h.symm

/-- The principal character modulo a prime gives the deletion of that prime's
multiples: subtract the average of all rational translates from the original form. -/
theorem translationSum_principal_prime {p : ℕ} [Fact p.Prime] [NeZero p]
    (f : ℍ → ℂ) (z : ℍ) :
    translationSum (1 : DirichletCharacter ℂ p) f z =
      f z - (p : ℂ)⁻¹ * ∑ u : ZMod p, f (residueShift u +ᵥ z) := by
  classical
  have hv (x : ZMod p) : (1 : DirichletCharacter ℂ p) x = 1 - (if x = 0 then 1 else 0) := by
    by_cases hx : x = 0
    · subst x
      simpa using (1 : DirichletCharacter ℂ p).map_nonunit (show ¬ IsUnit (0 : ZMod p) by simp)
    · simp [hx, MulChar.one_apply (isUnit_iff_ne_zero.mpr hx)]
  have hw (u : ZMod p) :
      translationWeights (1 : DirichletCharacter ℂ p) u = (if u = 0 then 1 else 0) - (p : ℂ)⁻¹ := by
    rw [translationWeights, Pi.smul_apply, ZMod.dft_apply]
    simp_rw [hv, smul_eq_mul, mul_sub, mul_one, mul_ite, mul_zero, ← mul_neg]
    rw [Finset.sum_sub_distrib, AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar p)]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, zero_mul, AddChar.map_zero_eq_one,
      mul_one, ZMod.card, neg_eq_zero]
    have hp : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p)
    split_ifs <;> field_simp
    norm_num
  simp_rw [translationSum, hw, sub_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp [residueShift]

/-- The values at the original modulus are the primitive values with all
indices not coprime to the original modulus deleted. -/
theorem dirichlet_apply_primitive_sieve {N : ℕ} [NeZero N]
    (ν : DirichletCharacter ℂ N) (n : ℕ) :
    ν n = if n.Coprime N then ν.primitiveCharacter (n : ℕ) else 0 := by
  have h : IsCoprime (n : ℤ) (N : ℤ) ↔ n.Coprime N := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast, Nat.Coprime]
  split_ifs with hn
  · simpa only [Int.cast_natCast] using (ν.primitiveCharacter_apply_of_isCoprime (h.mpr hn)).symm
  · simpa only [Int.cast_natCast] using
      (ν.apply_eq_zero_iff (n : ℤ)).mpr (fun h' ↦ hn (h.mp h'))

#print axioms ratShift_cast
#print axioms sum_translationWeights
#print axioms translationWeights_unit
#print axioms translationWeights_primitive
#print axioms qParam_residueShift
#print axioms hasSum_translationSum
#print axioms qExpansion_translationSum
#print axioms translationSum_principal_prime
#print axioms dirichlet_apply_primitive_sieve

end ZInQ.Manuscript.RC.HalfIntegral
