import ZInQKernel.Contrib.OneProof.GrossZagierHeegner.WeilParam
import ZInQKernel.Contrib.OneProof.GrossZagierHeegner.Heegner

/-! gz-conj, part 3: the Eichler integral under conjugation and under `W_N`. -/

noncomputable section

open Filter Topology Complex UpperHalfPlane HeckeRing.GL2 CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped ComplexConjugate MatrixGroups

namespace ZInQ.GZConj

section Eichler

variable {N : ℕ} [NeZero N]

/-- `τ ↦ −τ̄` on `ℍ`. -/
def negConjH (τ : ℍ) : ℍ := ⟨-conj (τ : ℂ), by simpa using τ.im_pos⟩

theorem im_fricke_pos {z : ℂ} (hz : 0 < z.im) : 0 < (-1 / ((N : ℂ) * z)).im := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hz0 : (N : ℂ) * z ≠ 0 :=
    mul_ne_zero (by exact_mod_cast NeZero.ne N) (fun h => by simp [h] at hz)
  have hpos : 0 < Complex.normSq ((N : ℂ) * z) := Complex.normSq_pos.mpr hz0
  rw [Complex.div_im]
  simp only [Complex.neg_re, Complex.neg_im, Complex.one_re, Complex.one_im, Complex.mul_im,
    Complex.natCast_re, Complex.natCast_im, neg_zero, zero_mul, zero_div, zero_sub,
    neg_mul, one_mul, neg_div, neg_neg]
  positivity

/-- The Fricke involution `W_N : τ ↦ −1/(Nτ)` on `ℍ`. -/
def frickeH (τ : ℍ) : ℍ := ⟨-1 / ((N : ℂ) * τ), im_fricke_pos τ.im_pos⟩

/-- `ψ(τ) = W_N(−τ̄) = 1/(N τ̄)`. -/
def psiH (τ : ℍ) : ℍ := frickeH (N := N) (negConjH τ)

theorem coe_psiH (τ : ℍ) : (psiH (N := N) τ : ℂ) = 1 / ((N : ℂ) * conj (τ : ℂ)) := by
  show -1 / ((N : ℂ) * -conj (τ : ℂ)) = _
  rw [mul_neg, div_neg, neg_div, neg_neg]

variable (f : Newform N 2)

theorem conj_eichler
    (hreal : ∀ n : ℕ, n ≠ 0 → conj (ZInQ.GZDecomp.coeff f n) = ZInQ.GZDecomp.coeff f n)
    (τ : ℍ) : conj (ZInQ.GZHL3.eichler f τ) = ZInQ.GZHL3.eichler f (negConjH τ) := by
  rw [ZInQ.GZHL3.eichler, ZInQ.GZHL3.eichler, Complex.conj_tsum]
  congr 1
  ext n
  have h1 : conj ((n : ℂ) + 1) = (n : ℂ) + 1 := by simp
  rw [map_mul, map_div₀, hreal _ (Nat.succ_ne_zero n), h1, ← Complex.exp_conj]
  congr 2
  simp only [negConjH, map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, h1]
  show _ = _ * -conj (τ : ℂ)
  ring

/-- `f(−1/(Nz)) = ε_N N z² f(z)` (the Fricke sign). -/
theorem fricke_apply (hχ : f.χ = 1) (z : ℂ) (hz : 0 < z.im)
    (hz' : 0 < (-1 / ((N : ℂ) * z)).im) :
    f.toCuspForm ⟨-1 / ((N : ℂ) * z), hz'⟩ = f.frickeSign hχ * N * z ^ 2 * f.toCuspForm ⟨z, hz⟩ := by
  have hfr := f.normalizedFrickeOperatorCusp_eq_frickeSign_smul hχ
  set ε := f.frickeSign hχ
  have hnorm : TauCeti.atkinLehnerNormalizer N 2 = 1 := by
    simp [TauCeti.atkinLehnerNormalizer]
  have hM0 : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have h := congrArg (fun F : CuspForm ((Gamma1 N).map (mapGL ℝ)) 2 => (⇑F) ⟨z, hz⟩) hfr
  simp only [TauCeti.coe_normalizedFrickeOperatorCusp, hnorm, one_smul] at h
  rw [ModularForm.slash_apply] at h
  have hdet : (0 : ℝ) < ((TauCeti.frickeGL ℝ N).det : ℝ) := TauCeti.val_det_frickeGL_pos
  have hσ : ∀ w : ℂ, σ (TauCeti.frickeGL ℝ N) w = w := fun w => by
    simp only [σ, if_pos hdet]; rfl
  have hpt : (TauCeti.frickeGL ℝ N • (⟨z, hz⟩ : ℍ)) = ⟨-1 / ((N : ℂ) * z), hz'⟩ := by
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.coe_smul_of_det_pos hdet, UpperHalfPlane.num, UpperHalfPlane.denom,
      TauCeti.coe_frickeGL]
    simp
  have hden : denom (TauCeti.frickeGL ℝ N) (⟨z, hz⟩ : ℍ) = (N : ℂ) * z := by
    rw [UpperHalfPlane.denom, TauCeti.coe_frickeGL]
    simp
  have hdetv : |((TauCeti.frickeGL ℝ N).det : ℝ)| = N := by
    rw [TauCeti.val_det_frickeGL, abs_of_nonneg (Nat.cast_nonneg _)]
  rw [hσ, hpt, hden, hdetv, CuspForm.smul_apply, smul_eq_mul] at h
  have hz0 : z ≠ 0 := fun h0 => by simp [h0] at hz
  generalize f.toCuspForm ⟨-1 / ((N : ℂ) * z), hz'⟩ = A at h ⊢
  generalize f.toCuspForm ⟨z, hz⟩ = B at h ⊢
  push_cast at h
  have hne : ((N : ℂ) * z) ^ 2 ≠ 0 := pow_ne_zero _ (mul_ne_zero hM0 hz0)
  simp only [zpow_one, zpow_neg, zpow_two] at h
  field_simp at h
  linear_combination h

/-- **For Fricke sign `+1` the Eichler integral is `W_N`-invariant**: `φ_f(−1/(Nτ)) = φ_f(τ)`
(the derivative of the difference is `2πi(ε_N − 1) f = 0`, and `i/√N` is fixed by `W_N`). -/
theorem eichler_fricke (hχ : f.χ = 1) (hε : f.frickeSign hχ = 1) (τ : ℍ) :
    ZInQ.GZHL3.eichler f (frickeH (N := N) τ) = ZInQ.GZHL3.eichler f τ := by
  set U : Set ℂ := {w : ℂ | 0 < w.im} with hU
  set F : ℂ → ℂ := fun w => (ZInQ.GZHL3.eichler f ∘ ofComplex) (-1 / ((N : ℂ) * w)) -
    (ZInQ.GZHL3.eichler f ∘ ofComplex) w with hF
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hd : ∀ w ∈ U, HasDerivAt F 0 w := by
    intro w hw
    have hw' : 0 < w.im := hw
    have hw0 : w ≠ 0 := fun h => by simp [h] at hw'
    have hNw : (N : ℂ) * w ≠ 0 := mul_ne_zero hN0 hw0
    have hg : HasDerivAt (fun x : ℂ => -1 / ((N : ℂ) * x)) (1 / ((N : ℂ) * w ^ 2)) w := by
      have := (((hasDerivAt_id' w).const_mul (N : ℂ)).inv hNw).neg
      convert this using 1
      · funext x; simp only [Pi.neg_apply, Pi.inv_apply]; rw [neg_div, one_div]
      · field_simp
    have hwi := im_fricke_pos (N := N) hw'
    have h1 := HasDerivAt.comp (h := fun x : ℂ => -1 / ((N : ℂ) * x)) w
      (GZHeegner.hasDerivAt_eichler f ⟨-1 / ((N : ℂ) * w), hwi⟩) hg
    have h2 := GZHeegner.hasDerivAt_eichler f ⟨w, hw'⟩
    have h3 := h1.sub h2
    convert h3 using 1
    · funext x; rfl
    have hf := fricke_apply f hχ w hw' hwi
    rw [hf, hε]
    field_simp
    ring
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_im
  have hc : ∀ x ∈ U, ∀ y ∈ U, F x = F y := fun x hx y hy =>
    hUo.is_const_of_deriv_eq_zero (convex_halfSpace_im_gt 0).isPreconnected
      (fun w hw => (hd w hw).differentiableAt.differentiableWithinAt)
      (fun w hw => (hd w hw).deriv) hx hy
  -- the fixed point `i/√N`
  have hNr : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  set s : ℝ := Real.sqrt N with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr hNr
  have hs2 : ((s : ℂ)) ^ 2 = N := by
    rw [← Complex.ofReal_pow, hs, Real.sq_sqrt hNr.le]; simp
  set w0 : ℂ := Complex.I / s with hw0
  have hw0im : 0 < w0.im := by
    rw [hw0, Complex.div_ofReal_im]; simp [hs0]
  have hfix : -1 / ((N : ℂ) * w0) = w0 := by
    have hsc : (s : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
    rw [hw0, ← hs2]
    field_simp
    rw [Complex.I_sq]
  have hF0 : F w0 = 0 := by simp only [hF, hfix, sub_self]
  have hFτ := hc _ (show (τ : ℂ) ∈ U from τ.im_pos) _ (show w0 ∈ U from hw0im)
  rw [hF0] at hFτ
  have hτ' : 0 < (-1 / ((N : ℂ) * τ)).im := im_fricke_pos τ.im_pos
  simp only [hF, Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hτ',
    UpperHalfPlane.ofComplex_apply_of_im_pos τ.im_pos, sub_eq_zero] at hFτ
  exact hFτ

/-- **Conjugation of the Eichler integral, Fricke sign `+1`**: `conj φ_f(τ) = φ_f(1/(N τ̄))`. -/
theorem conj_eichler_psi (hχ : f.χ = 1) (hε : f.frickeSign hχ = 1)
    (hreal : ∀ n : ℕ, n ≠ 0 → conj (ZInQ.GZDecomp.coeff f n) = ZInQ.GZDecomp.coeff f n)
    (τ : ℍ) : conj (ZInQ.GZHL3.eichler f τ) = ZInQ.GZHL3.eichler f (psiH (N := N) τ) := by
  rw [conj_eichler f hreal, psiH, eichler_fricke f hχ hε]

end Eichler

end ZInQ.GZConj
