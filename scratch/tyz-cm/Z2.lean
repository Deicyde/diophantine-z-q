import ZInQKernel.Contrib.TYZGenus.ShimuraRecip

noncomputable section

namespace ZInQ.Contrib.TYZGenus.Shimura

open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus Complex WeierstrassCurve.Affine

theorem curveAC_a₁ : X0.curveAC.a₁ = 0 := by
  simp [X0.curveAC, curveA, shortCurve, WeierstrassCurve.baseChange]
theorem curveAC_a₃ : X0.curveAC.a₃ = 0 := by
  simp [X0.curveAC, curveA, shortCurve, WeierstrassCurve.baseChange]

theorem negY_AC (x y : ℂ) : X0.curveAC.toAffine.negY x y = -y := by
  rw [negY, curveAC_a₁, curveAC_a₃]; ring

/-- **`φ(τ + 1/2) = −φ(τ)`** (from x0-32's `xC_add_half`, `yC_add_half`). -/
theorem phiC_add_half (τ τ' : UpperHalfPlane) (h : (τ' : ℂ) = τ + 1 / 2) :
    X0.phiC τ' = -X0.phiC τ := by
  have hx : X0.xC τ' = X0.xC τ := by rw [h, X0.xC_add_half]
  have hy : X0.yC τ' = -X0.yC τ := by rw [h, X0.yC_add_half]
  unfold X0.phiC
  by_cases hns : X0.curveAC.toAffine.Nonsingular (X0.xC τ) (X0.yC τ)
  · have hns' : X0.curveAC.toAffine.Nonsingular (X0.xC τ') (X0.yC τ') := by
      rw [hx, hy, ← negY_AC]; exact (nonsingular_neg ..).2 hns
    rw [dite_eq_left hns, dite_eq_left hns', Point.neg_some, Point.some.injEq, negY_AC]
    exact ⟨hx, hy⟩
  · have hns' : ¬ X0.curveAC.toAffine.Nonsingular (X0.xC τ') (X0.yC τ') := by
      rw [hx, hy, ← negY_AC]; exact fun h' => hns ((nonsingular_neg ..).1 h')
    rw [dite_eq_right hns, dite_eq_right hns', neg_zero]

/-- `(0, 0) ∈ A(ℂ)`. -/
theorem nonsingular_00C : X0.curveAC.toAffine.Nonsingular 0 0 := by
  rw [WeierstrassCurve.Affine.nonsingular_iff', WeierstrassCurve.Affine.equation_iff']
  have h4 : X0.curveAC.a₄ = 4 := by simp [X0.curveAC, curveA, shortCurve, WeierstrassCurve.baseChange]
  have h0 : X0.curveAC.a₂ = 0 ∧ X0.curveAC.a₆ = 0 := by
    simp [X0.curveAC, curveA, shortCurve, WeierstrassCurve.baseChange]
  rw [h4, curveAC_a₁, curveAC_a₃, h0.1, h0.2]
  refine ⟨by norm_num, Or.inl ?_⟩
  norm_num

def pt00C : X0.PtAC := .some 0 0 nonsingular_00C

theorem ptTC_add_self : X0.ptTC + X0.ptTC = pt00C := by
  have hy : (-4 : ℂ) ≠ X0.curveAC.toAffine.negY 2 (-4) := by rw [negY_AC]; norm_num
  rw [X0.ptTC, Point.add_self_of_Y_ne hy, pt00C, Point.some.injEq]
  have h4 : X0.curveAC.a₄ = 4 := by simp [X0.curveAC, curveA, shortCurve, WeierstrassCurve.baseChange]
  have h2 : X0.curveAC.a₂ = 0 := by simp [X0.curveAC, curveA, shortCurve, WeierstrassCurve.baseChange]
  have hs : X0.curveAC.toAffine.slope 2 2 (-4) (-4) = -2 := by
    rw [slope_of_Y_ne rfl hy]
    simp only [negY, curveAC_a₁, curveAC_a₃, h2, h4]; norm_num
  simp only [addX, addY, negAddY, negY, hs, curveAC_a₁, h2, curveAC_a₃]
  constructor <;> norm_num

theorem neg_pt00C : -pt00C = pt00C := by
  rw [pt00C, Point.neg_some, Point.some.injEq, negY_AC]; simp

/-- `τ ↦ −1/(32τ)` on `ℍ`. -/
def frickeH (τ : UpperHalfPlane) : UpperHalfPlane :=
  ⟨-1 / (32 * (τ : ℂ)), by
    have h32 : (32 : ℂ) * τ = ((32 : ℕ) : ℂ) * τ := by norm_num
    have hm := X0.mul_mem_upperHalfPlaneSet (d := 32) (by norm_num) τ
    rw [← h32] at hm
    have := UpperHalfPlane.im_inv_neg_coe_pos ⟨_, hm⟩
    simpa [div_eq_mul_inv, neg_inv] using this⟩

/-- `τ ↦ τ + 1/2` on `ℍ`. -/
def halfH (τ : UpperHalfPlane) : UpperHalfPlane :=
  ⟨(τ : ℂ) + 1 / 2, by
    show 0 < ((τ : ℂ) + 1 / 2).im
    simpa using τ.im_pos⟩

/-- **`φ(N₀τ) = φ(τ) + (0, 0)`** for `N₀ = S W S W`, `N₀τ = (14τ − 1)/(32τ − 2)`, from the Fricke
leaf `X0.EtaModelFricke` (`φ(Wτ) = T − φ(τ)`) and `φ(τ + 1/2) = −φ(τ)`; `2T = (0,0)`. -/
theorem phiC_N0 (hF : X0.EtaModelFricke) (τ τ' : UpperHalfPlane)
    (h : (τ' : ℂ) = (14 * τ - 1) / (32 * τ - 2)) : X0.phiC τ' = X0.phiC τ + pt00C := by
  set τ₁ := frickeH τ
  set τ₂ := halfH τ₁
  set τ₃ := frickeH τ₂
  have hτ' : (τ' : ℂ) = (halfH τ₃ : ℂ) := by
    rw [h]
    show _ = -1 / (32 * ((-1 / (32 * (τ : ℂ))) + 1 / 2)) + 1 / 2
    have hτ0 : (τ : ℂ) ≠ 0 := τ.ne_zero
    have hτ1 : (16 * (τ : ℂ) - 1) ≠ 0 := by
      intro h0
      have := congrArg Complex.im h0
      simp at this
      exact τ.im_pos.ne' this
    have hτ2 : (32 * (τ : ℂ) - 2) ≠ 0 := by
      intro h0; apply hτ1; linear_combination h0 / 2
    have hτ3 : (-2 + (τ : ℂ) * 32) ≠ 0 := by
      intro h0; apply hτ2; linear_combination h0
    field_simp
    ring_nf
    field_simp
    ring
  have e1 : X0.phiC τ₁ + X0.phiC τ = X0.ptTC := hF τ τ₁ rfl
  have e2 : X0.phiC τ₂ = -X0.phiC τ₁ := phiC_add_half τ₁ τ₂ rfl
  have e3 : X0.phiC τ₃ + X0.phiC τ₂ = X0.ptTC := hF τ₂ τ₃ rfl
  have e4 : X0.phiC τ' = -X0.phiC τ₃ := phiC_add_half τ₃ τ' hτ'
  rw [e4, eq_sub_of_add_eq e3, e2, eq_sub_of_add_eq e1]
  rw [← neg_pt00C, ← ptTC_add_self]
  abel

end ZInQ.Contrib.TYZGenus.Shimura
