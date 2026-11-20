import ZInQKernel.Contrib.OneProof.RC.J0Cusps.SourceLimit
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_E4_cube_div_discriminant_smul

/-! The width-one and zero cusps of the specified model, with convergence
in its complex scheme topology. On the spot (c), tex 1785–1787 and 2937–2939. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Filter Function ModularCurve PkgI3 UpperHalfPlane
open scoped MatrixGroups Topology

namespace ZInQ.Manuscript.RC.J0Cusps

theorem analyticJ_invariant (σ : SL(2, ℤ)) (τ : ℍ) :
    X0Model.analyticJ (σ • τ) = X0Model.analyticJ τ :=
  ModularCurve.E4_cube_div_discriminant_smul σ τ

private theorem qParam_one_zpow (z : ℂ) (n : ℤ) :
    Periodic.qParam 1 z ^ n = Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * z) := by
  rw [Periodic.qParam, Complex.ofReal_one, div_one, ← Complex.exp_int_mul]
  congr 1
  ring

private theorem qParam_at_cusp (w : ℝ) (hw : 0 < w) :
    Tendsto (fun τ : ℍ => Periodic.qParam w τ) atImInfty (𝓝[≠] (0 : ℂ)) :=
  (Periodic.qParam_tendsto hw).comp tendsto_coe_atImInfty

/-- The rational cusp at infinity is the complex limit of the given chart. -/
theorem tendsto_infinity (N : ℕ) [NeZero N] :
    Tendsto (fun τ : ℍ => complexLift (interior N τ)) atImInfty
      (𝓝 (complexLift (branchComplex N (Rat.castHom ℂ) (modularFunctionField N).subtype))) := by
  refine sourceLimit_of_generator_expansions N (Rat.castHom ℂ) (modularFunctionField N).subtype
    (fun τ : ℍ => Periodic.qParam 1 τ) id (qParam_at_cusp 1 one_pos)
    (fun τ => Periodic.qParam_ne_zero τ) ?_ ?_
  · exact Eventually.of_forall fun τ => by
      change HasSum (fun n : ℤ => (jq.coeff n : ℂ) * Periodic.qParam 1 τ ^ n)
        (X0Model.analyticJ τ)
      simpa only [qParam_one_zpow] using X0Model.hasSum_j τ
  · exact Eventually.of_forall fun τ => by
      change HasSum (fun n : ℤ => ((jqN N).coeff n : ℂ) * Periodic.qParam 1 τ ^ n)
        (X0Model.analyticJN N τ)
      simpa only [qParam_one_zpow] using X0Model.hasSum_jN N τ

private theorem dilate_S_dilate (N : ℕ) [NeZero N] (τ : ℍ) :
    X0Model.dilate N (ModularGroup.S • X0Model.dilate N τ) = ModularGroup.S • τ := by
  apply UpperHalfPlane.ext
  simp only [X0Model.dilate, modular_S_smul, UpperHalfPlane.coe_mk]
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  simp only [inv_neg, mul_inv, mul_neg]
  rw [← mul_assoc, mul_inv_cancel₀ hN, one_mul]

private def contract (N : ℕ) [NeZero N] (τ : ℍ) : ℍ :=
  ⟨(N : ℂ)⁻¹ * (τ : ℂ), by
    simp only [Complex.mul_im, ← Complex.ofReal_natCast, ← Complex.ofReal_inv,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    exact mul_pos (inv_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N))) τ.im_pos⟩

private theorem dilate_contract (N : ℕ) [NeZero N] (τ : ℍ) :
    X0Model.dilate N (contract N τ) = τ := by
  apply UpperHalfPlane.ext
  change (N : ℂ) * ((N : ℂ)⁻¹ * (τ : ℂ)) = τ
  rw [← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast NeZero.ne N), one_mul]

private theorem tendsto_contract (N : ℕ) [NeZero N] : Tendsto (contract N) atImInfty atImInfty := by
  rw [atImInfty, tendsto_comap_iff]
  refine tendsto_atTop.mpr fun b => ?_
  exact (atImInfty_mem _).mpr ⟨(N : ℝ) * b, fun τ hτ => by
    change b ≤ (((N : ℂ)⁻¹ * (τ : ℂ))).im
    simp only [Complex.mul_im, ← Complex.ofReal_natCast, ← Complex.ofReal_inv,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
    rw [inv_mul_eq_div, le_div_iff₀ hN, mul_comm]
    exact hτ⟩

/-- The chart translated by (S) converges to the complex base change of the
rational point selected by `j(q^N), j(q)` in the normalization. -/
theorem tendsto_zero (N : ℕ) [NeZero N] :
    Tendsto (fun τ : ℍ => complexLift (interior N (ModularGroup.S • τ))) atImInfty
      (𝓝 (complexLift (branchComplex N (Rat.castHom ℂ) (zeroField N)))) := by
  have h := sourceLimit_of_generator_expansions N (Rat.castHom ℂ) (zeroField N)
    (fun τ : ℍ => Periodic.qParam 1 τ) (fun τ => ModularGroup.S • X0Model.dilate N τ)
    (qParam_at_cusp 1 one_pos) (fun τ => Periodic.qParam_ne_zero τ)
    (Eventually.of_forall fun τ => by
      rw [zeroField_j, analyticJ_invariant]
      change HasSum (fun n : ℤ => ((jqN N).coeff n : ℂ) * Periodic.qParam 1 τ ^ n)
        (X0Model.analyticJN N τ)
      simpa only [qParam_one_zpow] using X0Model.hasSum_jN N τ)
    (Eventually.of_forall fun τ => by
      rw [zeroField_jN, X0Model.analyticJN, dilate_S_dilate, analyticJ_invariant]
      change HasSum (fun n : ℤ => (jq.coeff n : ℂ) * Periodic.qParam 1 τ ^ n)
        (X0Model.analyticJ τ)
      simpa only [qParam_one_zpow] using X0Model.hasSum_j τ)
  simpa only [Function.comp_def, dilate_contract] using h.comp (tendsto_contract N)


end ZInQ.Manuscript.RC.J0Cusps
