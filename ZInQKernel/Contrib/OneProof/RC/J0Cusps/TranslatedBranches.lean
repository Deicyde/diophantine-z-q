import ZInQKernel.Contrib.OneProof.RC.J0Cusps.Endpoints
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.Triangular
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_hasSum_cosetSubst_coeff_mul_qParam_pow
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_ModularPolynomialData_eval_E4_cube_div_discriminant_coset_eq_zero
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.RingTheory.RootsOfUnity.Complex

/-! Every modular translate has a Laurent branch with algebraic coefficients.
The triangular reduction and substitution are on the spot (c), tex 2937–2939. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Filter Function Matrix ModularCurve PkgI3 UpperHalfPlane
open scoped MatrixGroups Topology

namespace ZInQ.Manuscript.RC.J0Cusps

/-- The algebraic closure of the rationals inside the chosen complex field. -/
abbrev Qbar := algebraicClosure ℚ ℂ

abbrev qbarToComplex : Qbar →+* ℂ := (algebraicClosure ℚ ℂ).subtype

private theorem exists_cusp_root (N : ℕ) [NeZero N] :
    ∃ ζ : Qbarˣ, IsPrimitiveRoot ζ N ∧
      qbarToComplex (ζ : Qbar) = Complex.exp (2 * Real.pi * Complex.I / N) := by
  let z := Complex.exp (2 * Real.pi * Complex.I / N)
  have hc : IsPrimitiveRoot z N := Complex.isPrimitiveRoot_exp _ (NeZero.ne N)
  let z₀ : Qbar := ⟨z, mem_algebraicClosure_iff'.mpr
    (IsIntegral.of_pow (Nat.pos_of_ne_zero (NeZero.ne N)) (by rw [hc.pow_eq_one]; exact isIntegral_one))⟩
  have hc' : IsPrimitiveRoot (qbarToComplex z₀) N := hc
  have h₀ : IsPrimitiveRoot z₀ N := hc'.of_map_of_injective qbarToComplex.injective
  obtain ⟨u, hu⟩ := h₀.isUnit (NeZero.ne N)
  refine ⟨u, IsPrimitiveRoot.coe_units_iff.mp (by simpa only [hu] using h₀), ?_⟩
  rw [hu]
  rfl

private theorem qParam_level_pow (N : ℕ) [NeZero N] (τ : ℍ) :
    Periodic.qParam (N : ℝ) τ ^ N = Periodic.qParam 1 τ := by
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  rw [Periodic.qParam, ← Complex.exp_nat_mul, Periodic.qParam, Complex.ofReal_one,
    div_one, Complex.ofReal_natCast, mul_div_cancel₀ _ hN]

private theorem hasSum_first (N : ℕ) [NeZero N] (τ : ℍ) :
    HasSum (fun n : ℤ => (jqNModC ℂ N).coeff n * Periodic.qParam (N : ℝ) τ ^ n)
      (X0Model.analyticJ τ) := by
  have hq : Function.Injective (fun n : ℤ => (N : ℤ) * n) :=
    mul_right_injective₀ (by exact_mod_cast NeZero.ne N)
  refine (Function.Injective.hasSum_iff hq ?_).mp ?_
  · intro n hn
    have hnd : ¬ (N : ℤ) ∣ n := by
      rintro ⟨m, rfl⟩
      exact hn ⟨m, rfl⟩
    simp [jqNModC, qExpand_coeff_of_not_dvd N _ hnd]
  · change HasSum (fun n : ℤ => (qExpand ℂ N (jqModC ℂ)).coeff ((N : ℤ) * n) *
      Periodic.qParam (N : ℝ) τ ^ ((N : ℤ) * n)) _
    have hcoeff (n : ℤ) : (jqModC ℂ).coeff n = (jq.coeff n : ℂ) := by
      rw [← show coeffEmb ℂ jq = jqModC ℂ from map_jqModC (algebraMap ℚ ℂ), coeffEmb_coeff]
      exact DFunLike.congr_fun (Subsingleton.elim (algebraMap ℚ ℂ) (Rat.castHom ℂ)) _
    simpa only [qExpand_coeff_mul, _root_.zpow_mul, zpow_natCast, qParam_level_pow, hcoeff,
      X0Model.analyticJ]
      using (hasSum_jq_qParam τ)

private theorem second_form (N : ℕ) [NeZero N] (σ : SL(2, ℤ)) :
    ∃ (a b d : ℕ), (a, b, d) ∈ primCosetReps N ∧
      ∀ τ : ℍ, ∃ w : ℍ, (w : ℂ) = ((a : ℂ) * τ + b) / d ∧
        X0Model.analyticJN N (σ • τ) = X0Model.analyticJ w := by
  let D : Matrix (Fin 2) (Fin 2) ℤ := !![(N : ℤ), 0; 0, 1]
  let A := D * (σ : Matrix (Fin 2) (Fin 2) ℤ)
  have hA : A.det = N := by
    change (D * (σ : Matrix (Fin 2) (Fin 2) ℤ)).det = N
    rw [Matrix.det_mul, σ.property, mul_one]
    simp [D, Matrix.det_fin_two_of]
  have hbottom (i : Fin 2) : A 1 i = σ 1 i := by
    change (D * (σ : Matrix (Fin 2) (Fin 2) ℤ)) 1 i = _
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    change 0 * σ 0 i + 1 * σ 1 i = σ 1 i
    simp
  have hp (m : ℤ) (h₀ : m ∣ A 1 0) (h₁ : m ∣ A 1 1) : m ∣ 1 := by
    rw [hbottom] at h₀ h₁
    rw [← σ.property, Matrix.det_fin_two]
    exact dvd_sub (dvd_mul_of_dvd_right h₁ _) (dvd_mul_of_dvd_right h₀ _)
  obtain ⟨a, b, d, g, had, hb, hcop, hred⟩ :=
    exists_primitive_triangular N (Nat.pos_of_ne_zero (NeZero.ne N)) A hA hp
  refine ⟨a, b, d, (mem_primCosetReps (NeZero.ne N)).2 ⟨had, hb, hcop⟩, fun τ => ?_⟩
  have ha : 0 < a := Nat.pos_of_ne_zero (by rintro rfl; exact NeZero.ne N (by simpa using had.symm))
  have hd : 0 < d := by omega
  have hpos : (a : ℝ) * d ≠ 0 := mul_ne_zero (by exact_mod_cast ha.ne') (by exact_mod_cast hd.ne')
  let T := ModularForm.upperTriangularGL a b d hpos
  have hG : ModularForm.heckeDiagMatrix N * (σ : GL (Fin 2) ℝ) = (g : GL (Fin 2) ℝ) * T := by
    apply Units.ext
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M.map (Int.castRingHom ℝ)) hred
    simp only [A, Matrix.map_mul] at h
    simp only [Units.val_mul, ModularForm.val_heckeDiagMatrix (NeZero.ne N),
      T, ModularForm.val_upperTriangularGL]
    convert h using 2 <;> first | rfl | (ext i j; fin_cases i <;> fin_cases j <;> simp [D])
  refine ⟨T • τ, ?_, ?_⟩
  · exact P2MW.S_ModularCurve_ModularPolynomialData_eval_E4_cube_div_discriminant_coset_eq_zero.ModularCurve.CosetRootAux.coe_upperTriangularGL_smul ha hd hpos τ
  have hτ (v : ℍ) : X0Model.dilate N v = ModularForm.heckeDiagMatrix N • v :=
    UpperHalfPlane.ext (ModularForm.coe_heckeDiagMatrix_smul (NeZero.ne N) v).symm
  rw [X0Model.analyticJN, hτ]
  change X0Model.analyticJ (ModularForm.heckeDiagMatrix N • ((σ : GL (Fin 2) ℝ) • τ)) =
    X0Model.analyticJ (T • τ)
  rw [← mul_smul, hG, mul_smul]
  exact analyticJ_invariant g (T • τ)

private theorem coeffMap_qExpand {K : Type} [Field K] (ι : K →+* ℂ) (N : ℕ) [NeZero N]
    (x : LaurentSeries K) :
    coeffMap ι (qExpand K N x) = qExpand ℂ N (coeffMap ι x) := by
  ext n
  by_cases h : (N : ℤ) ∣ n
  · obtain ⟨m, rfl⟩ := h
    simp [qExpand_coeff_mul]
  · simp [qExpand_coeff_of_not_dvd N _ h]

private theorem coeffMap_qTwist {K : Type} [Field K] (ι : K →+* ℂ) (ζ : Kˣ) (x : LaurentSeries K) :
    coeffMap ι (qTwist ζ x) = qTwist (Units.map ι.toMonoidHom ζ) (coeffMap ι x) := by
  ext n
  simp [qTwist_coeff, ← map_zpow]

private theorem translated_generator_expansions (N : ℕ) [NeZero N] (σ : SL(2, ℤ)) :
    ∃ e : modularFunctionField N →+* LaurentSeries Qbar,
      ∀ τ : ℍ,
        HasSum (fun n : ℤ => qbarToComplex ((e ⟨jq, jq_mem N⟩).coeff n) *
          Periodic.qParam (N : ℝ) τ ^ n) (X0Model.analyticJ (σ • τ)) ∧
        HasSum (fun n : ℤ => qbarToComplex ((e ⟨jqN N, jqN_mem N⟩).coeff n) *
          Periodic.qParam (N : ℝ) τ ^ n) (X0Model.analyticJN N (σ • τ)) := by
  obtain ⟨ζ, hζ, hζ'⟩ := exists_cusp_root N
  obtain ⟨a, b, d, h, hσ⟩ := second_form N σ
  have had := ((mem_primCosetReps (NeZero.ne N)).mp h).1
  letI : NeZero a := ⟨by rintro rfl; exact NeZero.ne N (by simpa using had.symm)⟩
  let e := triangularField Qbar N ζ hζ (a, b, d) h
  have hmap : coeffMap qbarToComplex (jqModC Qbar) = jqModC ℂ := map_jqModC qbarToComplex
  refine ⟨e, fun τ => ⟨?_, ?_⟩⟩
  · rw [analyticJ_invariant, show e ⟨jq, jq_mem N⟩ = jqNModC Qbar N from
      triangularField_j Qbar N ζ hζ _ h]
    simpa only [← coeffMap_coeff, jqNModC, coeffMap_qExpand, hmap] using hasSum_first N τ
  · obtain ⟨w, hw, hx⟩ := hσ τ
    rw [hx, show e ⟨jqN N, jqN_mem N⟩ = cosetConj ζ (jqModC Qbar) (a, b, d) from
      triangularField_jN Qbar N ζ hζ _ h]
    have hJ : HasSum (fun n : ℤ => (jqModC ℂ).coeff n *
        Periodic.qParam 1 (((a : ℂ) * τ + b) / d) ^ n) (X0Model.analyticJ w) := by
      rw [← hw, ← show coeffEmb ℂ jq = jqModC ℂ from map_jqModC (algebraMap ℚ ℂ)]
      exact hasSum_jq_qParam w
    have hc := hasSum_cosetSubst_coeff_mul_qParam_pow (NeZero.ne N) had
      (Units.map qbarToComplex.toMonoidHom ζ) hζ' _ (τ : ℂ) _ hJ
    simpa only [cosetConj_eq, cosetSubst, RingHom.comp_apply, ← coeffMap_coeff,
      coeffMap_qExpand, coeffMap_qTwist, ← map_pow (Units.map qbarToComplex.toMonoidHom), hmap] using hc

/-- Every modular translate has a source limit on the specified model, and
that limit is the scalar extension of an algebraic point. -/
theorem exists_algebraic_cusp_limit (N : ℕ) [NeZero N] (σ : SL(2, ℤ)) :
    ∃ e : modularFunctionField N →+* LaurentSeries Qbar,
      Tendsto (fun τ : ℍ => complexLift (interior N (σ • τ))) atImInfty
        (𝓝 (complexLift (branchComplex N qbarToComplex e))) := by
  obtain ⟨e, he⟩ := translated_generator_expansions N σ
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  refine ⟨e, sourceLimit_of_generator_expansions N qbarToComplex e
    (fun τ : ℍ => Periodic.qParam (N : ℝ) τ) (fun τ => σ • τ)
    ((Periodic.qParam_tendsto hN).comp tendsto_coe_atImInfty)
    (fun τ => Periodic.qParam_ne_zero τ)
    (Eventually.of_forall fun τ => (he τ).1) (Eventually.of_forall fun τ => (he τ).2)⟩


end ZInQ.Manuscript.RC.J0Cusps
