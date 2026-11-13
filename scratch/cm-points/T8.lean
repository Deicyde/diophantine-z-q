import ZInQKernel.Contrib.TYZGenus.CM

noncomputable section
namespace ZInQ.Contrib.TYZGenus.CM
open ZInQ.Contrib.TYZDecomp.CurveA Complex ComplexConjugate

theorem qParam_conj (h : ℝ) (z : ℂ) :
    Function.Periodic.qParam h (-conj z) = conj (Function.Periodic.qParam h z) := by
  simp only [Function.Periodic.qParam, ← Complex.exp_conj]
  congr 1
  simp only [map_div₀, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  ring

/-- **`η(−z̄) = conj η(z)`** (real `q`-coefficients). -/
theorem eta_conj (z : ℂ) : ModularForm.eta (-conj z) = conj (ModularForm.eta z) := by
  unfold ModularForm.eta
  rw [map_mul, qParam_conj]
  congr 1
  rw [Function.LeftInverse.map_tprod (g := starRingEnd ℂ) _ Complex.continuous_conj
    Complex.continuous_conj (fun w => Complex.conj_conj w)]
  congr 1
  funext n
  simp only [ModularForm.eta_q, map_sub, map_one, map_pow, qParam_conj]

theorem etaD_conj (d : ℕ) (z : ℂ) : X0.etaD d (-conj z) = conj (X0.etaD d z) := by
  unfold X0.etaD
  rw [← eta_conj]
  congr 1
  simp

theorem xC_conj (z : ℂ) : X0.xC (-conj z) = conj (X0.xC z) := by
  unfold X0.xC
  simp only [etaD_conj, map_add, map_div₀, map_mul, map_pow, map_ofNat]

theorem yC_conj (z : ℂ) : X0.yC (-conj z) = conj (X0.yC z) := by
  unfold X0.yC
  simp only [etaD_conj, map_neg, map_div₀, map_mul, map_pow]

/-- Complex conjugation on `A(ℂ)` (`A` is defined over `ℚ`). -/
def conjPt : X0.PtAC →+ X0.PtAC := WeierstrassCurve.Affine.Point.map (W' := curveA) conjQ

theorem conjQ_apply (z : ℂ) : conjQ z = conj z := rfl

theorem conjQ_injective : Function.Injective conjQ := conjQ.injective

theorem phiC_conj (τ τ' : UpperHalfPlane) (h : (τ' : ℂ) = -conj (τ : ℂ)) :
    X0.phiC τ' = conjPt (X0.phiC τ) := by
  unfold X0.phiC
  have ex : X0.xC τ' = conjQ (X0.xC τ) := by rw [h, xC_conj]; rfl
  have ey : X0.yC τ' = conjQ (X0.yC τ) := by rw [h, yC_conj]; rfl
  by_cases hn : X0.curveAC.toAffine.Nonsingular (X0.xC τ) (X0.yC τ)
  · have hn' : X0.curveAC.toAffine.Nonsingular (X0.xC τ') (X0.yC τ') := by
      rw [ex, ey]
      exact (WeierstrassCurve.Affine.baseChange_nonsingular (W := curveA) (f := conjQ)
        conjQ_injective _ _).mpr hn
    rw [dif_pos hn', dif_pos hn]
    simp only [conjPt, WeierstrassCurve.Affine.Point.map_some, ex, ey]
  · have hn' : ¬ X0.curveAC.toAffine.Nonsingular (X0.xC τ') (X0.yC τ') := by
      rw [ex, ey]
      exact fun h' => hn ((WeierstrassCurve.Affine.baseChange_nonsingular (W := curveA)
        (f := conjQ) conjQ_injective _ _).mp h')
    simp only [hn, hn', ↓reduceDIte, map_zero]

theorem toC_galPt (σ : GalQ) (hσ : ∀ x : Qbar, ιC (σ x) = conj (ιC x)) (P : PtA) :
    toC (galPt σ P) = conjPt (toC P) := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · obtain ⟨h', e⟩ := galPt_some σ h
    rw [e]
    simp only [toC, conjPt, WeierstrassCurve.Affine.Point.map_some,
      WeierstrassCurve.Affine.Point.some.injEq]
    exact ⟨hσ x, hσ y⟩

theorem conjPt_conjPt (P : X0.PtAC) : conjPt (conjPt P) = P := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · simp only [conjPt, WeierstrassCurve.Affine.Point.map_some, conjQ_apply, Complex.conj_conj]

theorem tau_conj {N : ℕ} {D : ℤ} (Q : HeegnerForm N D) :
    ((Q.conj).tauH : ℂ) = -conj ((Q.tauH : UpperHalfPlane) : ℂ) := by
  show cmPoint Q.A (-Q.B) D = -conj (cmPoint Q.A Q.B D)
  simp only [cmPoint, map_div₀, map_add, map_neg, map_mul, map_intCast, Complex.conj_ofReal,
    Complex.conj_I, map_ofNat]
  push_cast
  ring

/-- **`CMComplexConj` holds** (proved from `η(−z̄) = conj η(z)`; no leaf needed). -/
theorem cmComplexConj : CMComplexConj := by
  intro σ hσ D Q
  have hσinv : ∀ x : Qbar, ιC (σ.symm x) = conj (ιC x) := fun x => by
    have := hσ (σ.symm x)
    rw [AlgEquiv.apply_symm_apply] at this
    rw [this, Complex.conj_conj]
  by_cases h : ∃ P : PtA, toC P = X0.phiC Q.tauH
  · obtain ⟨P, hP⟩ := h
    rw [heegnerPt_eq Q hP]
    symm
    apply heegnerPt_eq
    rw [toC_galPt σ hσ, hP, phiC_conj _ _ (tau_conj Q)]
  · have h0 : heegnerPt Q = 0 := by simp only [heegnerPt, h, ↓reduceDIte]
    have h1 : ¬ ∃ P : PtA, toC P = X0.phiC Q.conj.tauH := by
      rintro ⟨P, hP⟩
      apply h
      refine ⟨galPt σ.symm P, ?_⟩
      rw [toC_galPt σ.symm hσinv, hP, phiC_conj _ _ (tau_conj Q), conjPt_conjPt]
    have h1' : heegnerPt Q.conj = 0 := by simp only [heegnerPt, h1, ↓reduceDIte]
    rw [h0, h1', map_zero]

end ZInQ.Contrib.TYZGenus.CM

#print axioms ZInQ.Contrib.TYZGenus.CM.cmComplexConj
