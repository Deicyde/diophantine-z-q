import ZInQKernel.Contrib.CloudB3W17Realify.DerivRestriction
import ZInQKernel.Contrib.CloudB3W17Realify.GlobalFlow
import Mathlib.Analysis.Complex.CauchyIntegral

/-! # Complex one-parameter subgroups from two fixed real canonical flows -/

open Function Set
open scoped Manifold Topology ContDiff

namespace CloudB3W17Realify

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]
variable {G : Type*} [TopologicalSpace G] [ChartedSpace E G] [CommGroup G]
  [LieGroup 𝓘(ℂ, E) ω G]

/-- Reconstruct complex scalar multiplication from its real and imaginary components. -/
theorem re_smul_add_im_smul (v : E) (z : ℂ) :
    z.re • v + z.im • (Complex.I • v) = z • v := by
  rw [← algebraMap_smul ℂ z.re v, ← algebraMap_smul ℂ z.im (Complex.I • v),
    smul_smul, ← add_smul]
  congr 1
  exact Complex.re_add_im z

/-- The real canonical field coincides with the complex left-translation derivative. -/
theorem real_invariantField_eq (v : E) (g : G) :
    mulInvariantVectorField (I := 𝓘(ℝ, E)) v g =
      mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E) (g * ·) (1 : G) v := by
  unfold mulInvariantVectorField
  exact mfderiv_real_apply ((contMDiffAt_mul_left (I := 𝓘(ℂ, E)) (n := ω)).mdifferentiableAt
    (by simp)) v

omit [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] in
/-- A one-variable holomorphic map into a complete complex self-model manifold is analytic. -/
theorem contMDiff_omega_of_mdifferentiable_oneVariable [CompleteSpace E]
    {f : ℂ → G} (hf : MDifferentiable 𝓘(ℂ, ℂ) 𝓘(ℂ, E) f) :
    ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, E) ω f := by
  intro z
  rw [contMDiffAt_iff_target_of_mem_source (mem_chart_source E (f z))]
  refine ⟨(hf z).continuousAt, ?_⟩
  rw [contMDiffAt_iff_contDiffAt]
  have hs : f ⁻¹' (chartAt E (f z)).source ∈ 𝓝 z :=
    hf.continuous.continuousAt.preimage_mem_nhds (chart_source_mem_nhds E (f z))
  have hd : DifferentiableOn ℂ (extChartAt 𝓘(ℂ, E) (f z) ∘ f)
      (f ⁻¹' (chartAt E (f z)).source) := by
    intro w hw
    exact ((mdifferentiableAt_iff_target_of_mem_source hw).mp (hf w)).2.differentiableAt
      |>.differentiableWithinAt
  exact (hd.analyticAt hs).contDiffAt

section FixedFlows

variable (v : E) (γ δ : ℝ → G)
  (hγ : IsMIntegralCurve γ (mulInvariantVectorField (I := 𝓘(ℝ, E)) v))
  (hδ : IsMIntegralCurve δ (mulInvariantVectorField (I := 𝓘(ℝ, E)) (Complex.I • v)))

include hγ hδ in
/-- The Cauchy--Riemann derivative of the product of two fixed canonical real flows. -/
theorem hasMFDerivAt_complexifiedFlow (z : ℂ) :
    HasMFDerivAt 𝓘(ℂ, ℂ) 𝓘(ℂ, E)
      (fun z : ℂ => γ z.re * δ z.im) z
      ((mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E) ((γ z.re * δ z.im) * ·) (1 : G) : E →L[ℂ] E).comp
        ((ContinuousLinearMap.id ℂ ℂ).smulRight v)) := by
  let : LieGroup 𝓘(ℝ, E) ω G := lieGroup_real
  let : LieGroup 𝓘(ℝ, E) 3 G := LieGroup.of_le (n := ω) le_top
  have hγ' := (hγ z.re).comp z Complex.reCLM.hasFDerivAt.hasMFDerivAt
  have hδ' := (hδ z.im).comp z Complex.imCLM.hasFDerivAt.hasMFDerivAt
  have hm := ((contMDiff_mul 𝓘(ℝ, E) 3 (G := G)).contMDiffAt
    (x := (γ z.re, δ z.im)) |>.mdifferentiableAt (by norm_num)).hasMFDerivAt
  have hp := hm.comp z (hγ'.prodMk hδ')
  apply hasMFDerivAt_complex
  apply hp.congr_mfderiv
  apply ContinuousLinearMap.ext
  intro w
  change ℂ at w
  change mfderiv (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 𝓘(ℝ, E)
    (fun p : G × G => p.1 * p.2) (γ z.re, δ z.im)
    (w.re • mulInvariantVectorField (I := 𝓘(ℝ, E)) v (γ z.re),
      w.im • mulInvariantVectorField (I := 𝓘(ℝ, E)) (Complex.I • v) (δ z.im)) =
    mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E) ((γ z.re * δ z.im) * ·) (1 : G) (w • v)
  rw [mfderiv_prod_eq_add_apply
    ((contMDiff_mul 𝓘(ℝ, E) 3).mdifferentiableAt (by norm_num))]
  have hr : (fun a : G => a * δ z.im) = (δ z.im * ·) := by
    funext a
    exact mul_comm _ _
  change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun a : G => a * δ z.im) (γ z.re)
      (w.re • mulInvariantVectorField (I := 𝓘(ℝ, E)) v (γ z.re)) +
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (γ z.re * ·) (δ z.im)
      (w.im • mulInvariantVectorField (I := 𝓘(ℝ, E)) (Complex.I • v) (δ z.im)) =
    mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E) ((γ z.re * δ z.im) * ·) (1 : G) (w • v)
  erw [hr, map_smul, map_smul,
    mfderiv_mul_left_invariant, mfderiv_mul_left_invariant, mul_comm (δ z.im) (γ z.re),
    real_invariantField_eq, real_invariantField_eq]
  let D : E →L[ℂ] E := mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E)
    ((γ z.re * δ z.im) * ·) (1 : G)
  change w.re • D v + w.im • D (Complex.I • v) = D (w • v)
  rw [← algebraMap_smul ℂ w.re (D v), ← algebraMap_smul ℂ w.im (D (Complex.I • v)),
    ← map_smul, ← map_smul, ← map_add]
  congr 1
  simpa only [algebraMap_smul] using re_smul_add_im_smul v w

end FixedFlows

/-- Two fixed real canonical flows give a global analytic complex one-parameter homomorphism.
No joint regularity in the velocity parameter is assumed. -/
theorem exists_complexOneParameter [CompleteSpace E] [T2Space G] (v : E) :
    ∃ f : ℂ → G, f 0 = 1 ∧ (∀ z w, f (z + w) = f z * f w) ∧
      ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, E) ω f ∧
      HasMFDerivAt 𝓘(ℂ, ℂ) 𝓘(ℂ, E) f 0 ((ContinuousLinearMap.id ℂ ℂ).smulRight v) := by
  let : LieGroup 𝓘(ℝ, E) ω G := lieGroup_real
  let : LieGroup 𝓘(ℝ, E) 3 G := LieGroup.of_le (n := ω) le_top
  obtain ⟨γ, hγ0, hγ⟩ := exists_global_invariantCurve (I := 𝓘(ℝ, E)) v (1 : G)
  obtain ⟨δ, hδ0, hδ⟩ := exists_global_invariantCurve (I := 𝓘(ℝ, E)) (Complex.I • v) (1 : G)
  let f : ℂ → G := fun z => γ z.re * δ z.im
  have hf0 : f 0 = 1 := by simp only [f, Complex.zero_re, Complex.zero_im, hγ0, hδ0, mul_one]
  have hd := hasMFDerivAt_complexifiedFlow v γ δ hγ hδ
  refine ⟨f, hf0, ?_, contMDiff_omega_of_mdifferentiable_oneVariable
    (fun z => (hd z).mdifferentiableAt), ?_⟩
  · intro z w
    simp only [f, Complex.add_re, Complex.add_im,
      invariantCurve_add v hγ0 hγ, invariantCurve_add (Complex.I • v) hδ0 hδ]
    exact mul_mul_mul_comm _ _ _ _
  · have h := hd 0
    have hid : (fun a : G => f 0 * a) = id := by
      funext a
      simp only [hf0, one_mul, id_eq]
    change HasMFDerivAt 𝓘(ℂ, ℂ) 𝓘(ℂ, E) f 0
      ((mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E) (fun a => f 0 * a) (1 : G) : E →L[ℂ] E).comp
        ((ContinuousLinearMap.id ℂ ℂ).smulRight v)) at h
    erw [hid, mfderiv_id, ContinuousLinearMap.id_comp] at h
    exact h

end CloudB3W17Realify
