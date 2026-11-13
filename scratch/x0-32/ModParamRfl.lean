import ZInQKernel.Contrib.TYZGenus.X0

/-! Check that cm-points' `CM.modParam` (copied verbatim from origin/wip/cm-points c4b568dc) is
definitionally `X0.modParamF`. -/

open ZInQ.Contrib.TYZDecomp.CurveA Complex

noncomputable def aCoeff (m : ℕ) : ℤ := curveA.LFunction m

noncomputable def modParam (τ : ℂ) : ℂ :=
  ∑' m : ℕ, ((aCoeff m : ℂ) / m) * Complex.exp (2 * Real.pi * I * m * τ)

example : modParam = ZInQ.Contrib.TYZGenus.X0.modParamF := rfl
