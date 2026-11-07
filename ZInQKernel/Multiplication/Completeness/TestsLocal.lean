import ZInQKernel.Multiplication.Completeness.PoleValuationsAux
import ZInQKernel.Multiplication.Local.FormalGroup
import ZInQKernel.Multiplication.Local.TruncationUnit
import ZInQKernel.Multiplication.Local.Nonvanishing

/-!
# The twelve tests at a prime where the test points are formal

At a prime `ρ` of `ℤ[s]`, if `H = [h]P₀ ≠ O` lies in the formal neighbourhood `W₁` at `ρ`,
`V₀ = [h - c₀]P₀ ≠ O` lies in `W₁` at `σρ`, `U_i = [n_i]H` and `V_i = [n_i]V₀`, then all twelve
test values are `ρ`-integral: inverse abscissas of formal points have positive valuation, and
`L(z(nH))/L(z(H))` is `z(nH)/z(H)` times a unit.
-/

namespace ZInQ.Mult

open WeierstrassCurve WeierstrassCurve.Affine

variable {ρ : Zs} (hρ : Prime ρ)

theorem vP_neg_genD_sq_nonneg : 0 ≤ vP ρ hρ (-genD ^ 2) := by
  rw [(vP ρ hρ).map_neg]; exact vP_genD_sq_nonneg hρ

theorem zOf_eq_zCoord (Q : genCurve.toAffine.Point) : zOf Q = zCoord (A := -genD ^ 2) Q := by
  rcases Q with _ | ⟨x, y, h⟩ <;> rfl

theorem invX_eq_wCoord (Q : genCurve.toAffine.Point) : invX Q = wCoord (A := -genD ^ 2) Q := by
  rcases Q with _ | ⟨x, y, h⟩
  · rfl
  · show x⁻¹ = 1 / x; rw [one_div]

include hρ in
/-- The inverse abscissa of a formal point has valuation `≥ 2`. -/
theorem vge_invX_of_W1 {Q : genCurve.toAffine.Point} (hQ : Q ∈ W1 (vP ρ hρ) (-genD ^ 2)) :
    Vge (vP ρ hρ) 2 (invX Q) := by
  rcases Q with _ | ⟨x, y, h⟩
  · exact Vge.zero _
  obtain ⟨N, hN, -, -, -, -, hw, -⟩ := formal_val_x_y (vP_neg_genD_sq_nonneg hρ) h hQ
  rw [invX_eq_wCoord]
  exact (Vge.of_eq hw).mono (by omega)

include hρ in
/-- The ratio `Λ([n]H)/Λ(H)` is integral for a formal `H ≠ O`. -/
theorem vge_Lam_ratio {H : genCurve.toAffine.Point} (hH : H ∈ W1 (vP ρ hρ) (-genD ^ 2))
    (hH0 : H ≠ 0) (n : ℤ) : Vge (vP ρ hρ) 0 (Lam (n • H) / Lam H) := by
  have hA := vP_neg_genD_sq_nonneg hρ
  obtain ⟨-, hle⟩ := zsmul_mem_W1 hA hH n
  have hz1 : 1 ≤ vP ρ hρ (zOf H) := by rw [zOf_eq_zCoord]; exact one_le_val_zCoord hA hH
  have hzn1 : 1 ≤ vP ρ hρ (zOf (n • H)) := by
    rw [zOf_eq_zCoord]; exact le_trans (one_le_val_zCoord hA hH) hle
  have hz0 : zOf H ≠ 0 := by
    rcases H with _ | ⟨x, y, h⟩
    · exact absurd rfl hH0
    obtain ⟨N, -, -, -, -, hz, -⟩ := formal_val_x_y hA h hH
    intro h0
    have h0' : zCoord (A := -genD ^ 2) (Point.some x y h) = 0 := h0
    rw [h0', (vP ρ hρ).map_zero] at hz
    exact WithTop.top_ne_coe hz
  obtain ⟨N, hN⟩ := val_eq_coe (v := vP ρ hρ) hz0
  obtain ⟨η, hη, hL⟩ := log25_eq_mul_unit hρ hz1
  obtain ⟨η', hη', hL'⟩ := log25_eq_mul_unit hρ hzn1
  have hc0 : (16575 : K0) ≠ 0 := by norm_num
  have hu : vP ρ hρ (1 + η) = 0 := val_one_add (le_trans (by norm_num) hη)
  have hu0 : (1 + η) ≠ 0 := one_add_ne_zero (le_trans (by norm_num) hη)
  have hu' : Vge (vP ρ hρ) 0 (1 + η') := by
    rw [Vge, val_one_add (le_trans (by norm_num) hη')]; simp
  have e : Lam (n • H) / Lam H = (zOf (n • H) / zOf H) * ((1 + η') / (1 + η)) := by
    rw [Lam, Lam, hL, hL', mul_assoc, mul_assoc, mul_div_mul_left _ _ hc0, div_mul_div_comm]
  rw [e]
  have h1 : Vge (vP ρ hρ) 0 (zOf (n • H) / zOf H) := by
    have : Vge (vP ρ hρ) N (zOf (n • H)) := by
      rw [Vge, ← hN, zOf_eq_zCoord, zOf_eq_zCoord]; rw [zOf_eq_zCoord] at hN; exact hle
    simpa using this.div_val hN
  simpa using h1.mul (hu'.div_unit hu)

include hρ in
/-- **The twelve tests are integral** at `ρ` when `H = [h]P₀ ≠ O` is formal at `ρ`,
`V₀ = [h - c₀]P₀ ≠ O` is formal at `σρ`, `U_i = [n_i]H` and `V_i = [n_i]V₀`. -/
theorem tests_vge_zero_of_W1 (h : ℤ) (z : Fin 3 → ℤ) (c : Fin 4 → ℤ) (n : Fin 3 → ℤ)
    (hz : ∀ i, z i • genP0 = n i • (h • genP0))
    (hzc : ∀ i, (z i - c i.succ) • genP0 = n i • ((h - c 0) • genP0))
    (hH : h • genP0 ∈ W1 (vP ρ hρ) (-genD ^ 2)) (hH0 : h • genP0 ≠ 0)
    (hV : (h - c 0) • genP0 ∈ W1 (vP (star ρ) (prime_star hρ)) (-genD ^ 2))
    (hV0 : (h - c 0) • genP0 ≠ 0) (j : Fin 12) :
    Vge (vP ρ hρ) 0 (testValues h z c j) := by
  have hA := vP_neg_genD_sq_nonneg hρ
  have hA' := vP_neg_genD_sq_nonneg (prime_star hρ)
  have hstar : ∀ y : K0, Vge (vP (star ρ) (prime_star hρ)) 0 y → Vge (vP ρ hρ) 0 (star y) := by
    intro y hy; rw [Vge, ← vP_star]; exact hy
  have hU : ∀ i, Vge (vP ρ hρ) 0 (invX (z i • genP0)) := by
    intro i; rw [hz i]
    exact (vge_invX_of_W1 hρ (zsmul_mem_W1 hA hH (n i)).1).mono (by norm_num)
  have hVi : ∀ i, Vge (vP ρ hρ) 0 (star (invX ((z i - c i.succ) • genP0))) := by
    intro i; rw [hzc i]
    exact hstar _ ((vge_invX_of_W1 (prime_star hρ) (zsmul_mem_W1 hA' hV (n i)).1).mono
      (by norm_num))
  have hAi : ∀ i, Vge (vP ρ hρ) 0 (Lam (z i • genP0) / Lam (h • genP0)) := by
    intro i; rw [hz i]; exact vge_Lam_ratio hρ hH hH0 (n i)
  have hBi : ∀ i, Vge (vP ρ hρ) 0
      (star (Lam ((z i - c i.succ) • genP0) / Lam ((h - c 0) • genP0))) := by
    intro i; rw [hzc i]; exact hstar _ (vge_Lam_ratio (prime_star hρ) hV hV0 (n i))
  rw [testValues_eq]
  fin_cases j
  · exact (vge_invX_of_W1 hρ hH).mono (by norm_num)
  · exact hU 0
  · exact hU 1
  · exact hU 2
  · exact hstar _ ((vge_invX_of_W1 (prime_star hρ) hV).mono (by norm_num))
  · exact hVi 0
  · exact hVi 1
  · exact hVi 2
  · exact (hAi 0).sub (hBi 0)
  · exact (hAi 1).sub (hBi 1)
  · exact (hAi 2).sub (hBi 2)
  · exact ((hAi 0).mul (hAi 1)).mono (by norm_num) |>.sub (hAi 2)

end ZInQ.Mult
