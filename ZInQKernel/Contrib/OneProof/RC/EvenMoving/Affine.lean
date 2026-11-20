import ZInQKernel.Contrib.OneProof.RC.BlocksPerU.ThetaTransform
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Holomorphy and cusp bounds for positive rational affine changes of variable.
This fills in the cusp assertion at tex 9541–9542 and also covers the dilation. -/

noncomputable section

namespace ZInQ.Manuscript.RC.EvenMoving

open BlocksPerU Matrix Matrix.SpecialLinearGroup UpperHalfPlane Filter Asymptotics
open scoped MatrixGroups Manifold Topology

private def affine (a b : ℚ) (ha : 0 < a) : GL (Fin 2) ℚ :=
  GeneralLinearGroup.mkOfDetNeZero !![a, b; 0, 1]
    (by simpa [Matrix.det_fin_two] using ha.ne')

private theorem affine_det (a b : ℚ) (ha : 0 < a) :
    (affine a b ha).det.val = a := by
  change Matrix.det !![a, b; 0, 1] = a
  simp [Matrix.det_fin_two]

/-- The upper-half-plane map with complex coordinate `a * z + b`. -/
def affinePoint (a b : ℚ) (ha : 0 < a) (z : ℍ) : ℍ :=
  (affine a b ha).map (algebraMap ℚ ℝ) • z

private theorem affine_map_pos (a b : ℚ) (ha : 0 < a) :
    0 < ((affine a b ha).map (algebraMap ℚ ℝ)).det.val := by
  rw [GeneralLinearGroup.map_det, Units.coe_map, affine_det]
  change 0 < (a : ℝ)
  exact_mod_cast ha

theorem affinePoint_coe (a b : ℚ) (ha : 0 < a) (z : ℍ) :
    (affinePoint a b ha z : ℂ) = (a : ℂ) * (z : ℂ) + b := by
  rw [affinePoint, coe_smul_of_det_pos (affine_map_pos a b ha)]
  change ((↑(algebraMap ℚ ℝ a) : ℂ) * (z : ℂ) + ↑(algebraMap ℚ ℝ b)) /
    ((↑(algebraMap ℚ ℝ (0 : ℚ)) : ℂ) * (z : ℂ) + ↑(algebraMap ℚ ℝ (1 : ℚ))) = _
  simp

theorem affinePoint_holo (a b : ℚ) (ha : 0 < a) : MDiff (affinePoint a b ha) :=
  mdifferentiable_smul (affine_map_pos a b ha)

/-- Transport the bound at every cusp through a positive rational affine substitution. -/
theorem affinePoint_cusps (k : ℝ) {f : ℍ → ℂ}
    (hf : ∀ γ : SL(2, ℤ), IsBoundedAtImInfty (cuspNorm k f γ))
    (a b : ℚ) (ha : 0 < a) (γ : SL(2, ℤ)) :
    IsBoundedAtImInfty (cuspNorm k (fun z => f (affinePoint a b ha z)) γ) := by
  let F := affine a b ha
  let A : GL (Fin 2) ℚ := F * mapGL ℚ γ
  obtain ⟨β, hβ⟩ := (A • (OnePoint.infty : OnePoint ℚ)).exists_mem_SL2 ℤ
  let G := (mapGL ℚ β)⁻¹ * A
  have hG : G 1 0 = 0 := OnePoint.smul_infty_eq_self_iff.mp (by
    change ((mapGL ℚ β)⁻¹ * A) • (OnePoint.infty : OnePoint ℚ) = _
    rw [mul_smul, ← hβ, inv_smul_smul])
  let g := G.map (algebraMap ℚ ℝ)
  have hg : g 1 0 = 0 := by simp [g, GeneralLinearGroup.map, hG]
  have hGdet : G.det.val = a := by
    simpa [G, A, F] using affine_det a b ha
  have hgpos : 0 < g.det.val := by
    change 0 < (G.map (algebraMap ℚ ℝ)).det.val
    rw [GeneralLinearGroup.map_det, Units.coe_map, hGdet]
    change 0 < (a : ℝ)
    exact_mod_cast ha
  let v := F.map (algebraMap ℚ ℝ)
  have hprod : mapGL ℝ β * g = v * mapGL ℝ γ := by simp [g, G, A, v]
  have hz (z : ℍ) : affinePoint a b ha (γ • z) = β • (g • z) := by
    change v • (mapGL ℝ γ • z) = mapGL ℝ β • (g • z)
    rw [← mul_smul, ← mul_smul, hprod]
  have hv (z : ℍ) : denom v z = 1 := by
    change (↑(algebraMap ℚ ℝ (0 : ℚ)) : ℂ) * (z : ℂ) + ↑(algebraMap ℚ ℝ (1 : ℚ)) = _
    simp
  have hd (z : ℍ) : denom γ z = denom β (g • z : ℍ) * (g 1 1 : ℝ) := by
    have h₁ := denom_cocycle_σ v (mapGL ℝ γ) z
    have h₂ := denom_cocycle_σ (mapGL ℝ β) g z
    rw [← hprod, hv, map_one, one_mul, h₂] at h₁
    have hgpos' : 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det := hgpos
    simpa [UpperHalfPlane.σ, hgpos', denom, hg] using h₁.symm
  have he (z : ℍ) :
      cuspNorm k (fun w => f (affinePoint a b ha w)) γ z =
        cuspNorm k f β (g • z) * ‖(g 1 1 : ℝ)‖ ^ (-k) := by
    simp only [cuspNorm, hz, hd, norm_mul, Complex.norm_real,
      Real.mul_rpow (norm_nonneg _) (norm_nonneg _), mul_assoc]
  have hh : BoundedAtFilter atImInfty (fun z => cuspNorm k f β (g • z)) := by
    exact (show cuspNorm k f β =O[atImInfty] (1 : ℍ → ℝ) from hf β).comp_tendsto
      (tendsto_smul_atImInfty hg)
  have h := hh.mul (const_boundedAtFilter atImInfty (‖(g 1 1 : ℝ)‖ ^ (-k)))
  rw [show cuspNorm k (fun w => f (affinePoint a b ha w)) γ = _ from funext he]
  exact h

end ZInQ.Manuscript.RC.EvenMoving
