import ZInQKernel.Contrib.OneProof.RC.ModFnClassify.Classification

/-! Rational Laurent descent for the pullback coordinates of the
involution at tex 2943–2944 and 8487–8489. On the spot (c). -/

set_option autoImplicit false

noncomputable section

open Filter Function UpperHalfPlane ModularCurve Polynomial Matrix
open Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups
open ZInQ.Manuscript.RC.ModFnField
open ZInQ.Manuscript.RC.ModFnClassify

namespace ZInQ.Manuscript.RC.AtkinRational

variable {N : ℕ} [NeZero N]

omit [NeZero N] in
private theorem levelInvariant_of_dvd {m : ℕ} [NeZero m] (hm : m ∣ N) :
    LevelInvariant N (jNFunction m) := by
  intro γ hγ τ
  refine jNFunction_invariant m γ (Gamma0_mem.mpr ?_) τ
  apply (CharP.intCast_eq_zero_iff (ZMod m) m (γ 1 0)).mpr
  exact dvd_trans (by exact_mod_cast hm)
    ((CharP.intCast_eq_zero_iff (ZMod N) N (γ 1 0)).mp (Gamma0_mem.mp hγ))

/-- The dilated rational $j$-series for any positive divisor of the level
belongs to the field of the level. The degree bound for the orbit product
applies to this function and to its linear combinations with $j_N$. -/
theorem jqN_mem_of_dvd {m : ℕ} [NeZero m] (hm : m ∣ N) : jqN m ∈ modularFunctionField N := by
  apply modularFunctionField_descent N
  have hc (t : ℕ) [NeZero t] : complexify (jqN t) = jqNModC ℂ t := by
    have hj : complexify jq = jqModC ℂ := map_jqModC (Rat.castHom ℂ)
    ext n
    by_cases hn : (t : ℤ) ∣ n
    · obtain ⟨i, rfl⟩ := hn
      simpa only [complexify_coeff, jqN, jqNModC, qExpand_coeff_mul] using
        congrArg (fun z : LaurentSeries ℂ => z.coeff i) hj
    · simp [jqN, jqNModC, qExpand_coeff_of_not_dvd _ _ hn]
  rw [hc]
  have ha (t : ℕ) [NeZero t] (σ : SL(2, ℤ)) :
      ∀ᶠ z : ℂ in comap Complex.im atTop,
        DifferentiableAt ℂ (fun w => jNFunction t (σ • ofComplex w : ℍ)) z :=
    ((eventually_gt_atTop (0 : ℝ)).comap Complex.im).mono
      (fun z hz => (jN_translate_analytic t σ z hz).differentiableAt)
  obtain ⟨hjI, hjD⟩ := complex_jN_minpoly_degree N
  have hmI := (formal_degree_bound_of_growth
    (fun z hz => (X0Model.analyticOn_jN m z hz).meromorphicAt)
    (levelInvariant_of_dvd hm) (ha m) (jN_translate_growth m) (realizes_jN m)).1
  rw [modularFunctionFieldC, ← IntermediateField.adjoin_simple_adjoin_simple]
  apply mem_adjoin_of_linear_degree_bound (R := ℂ) hjI hmI
  intro t
  rw [hjD]
  let v : ℂ → ℂ := fun z => jNFunction N z + t * jNFunction m z
  have hv : MeromorphicOn v upperDomain := fun z hz =>
    ((X0Model.analyticOn_jN N z hz).meromorphicAt).add
      ((MeromorphicAt.const t z).mul (X0Model.analyticOn_jN m z hz).meromorphicAt)
  have hi : LevelInvariant N v := fun σ hσ τ => by
    simp only [v, jNFunction_invariant N σ hσ τ, levelInvariant_of_dvd hm σ hσ τ]
  have hdiff (σ : SL(2, ℤ)) : ∀ᶠ z : ℂ in comap Complex.im atTop,
      DifferentiableAt ℂ (fun w => v (σ • ofComplex w : ℍ)) z := by
    filter_upwards [ha N σ, ha m σ] with z hz hw
    exact hz.add (differentiableAt_const t |>.mul hw)
  have hg (σ : SL(2, ℤ)) : CuspGrowth 1 (fun τ => v (σ • τ : ℍ)) := by
    have hn := cuspGrowth_sub one_pos (cuspGrowth_const (h := 1) 0)
      (cuspGrowth_mul (cuspGrowth_const t) (jN_translate_growth m σ))
    simpa only [zero_sub, sub_neg_eq_add] using
      cuspGrowth_sub one_pos (jN_translate_growth N σ) hn
  exact (formal_degree_bound_of_growth hv hi hdiff hg
    ((realizes_jN N).add ((Realizes.const t).mul (realizes_jN m)))).2


end ZInQ.Manuscript.RC.AtkinRational
