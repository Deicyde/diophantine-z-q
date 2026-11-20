import ZInQKernel.Contrib.OneProof.RC.X0Model.Section
import ZInQKernel.Contrib.OneProof.RC.X0Model2.LaurentConvergence
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_LaurentCoeff

/-! A convergent Laurent realization of the two generators determines
the regular function evaluations on a translated tail. On the spot (c),
tex 1785–1787 and 2937–2939. -/

noncomputable section

open Filter ModularCurve ShimuraPointDict
open scoped Topology

namespace ZInQ.Manuscript.RC.J0Cusps

private abbrev jGenField (N : ℕ) [NeZero N] : modularFunctionField N := ⟨jq, jq_mem N⟩
private abbrev jNGenField (N : ℕ) [NeZero N] : modularFunctionField N := ⟨jqN N, jqN_mem N⟩

private theorem fieldGerm_first (N : ℕ) [NeZero N] (w : UpperHalfPlane) :
    X0Model.meromorphicIncl (w : ℂ) (X0Model.fieldGerm N w (jGenField N)) =
      ((X0Model.analyticJ ∘ UpperHalfPlane.ofComplex : ℂ → ℂ) : PuncturedGerm (w : ℂ)) := by
  rw [X0Model.fieldGerm_j]
  exact Germ.coe_eq.mpr (Eventually.of_forall fun _ => by simp)

private theorem germ_inverse {z : ℂ} (u : X0Model.MeromorphicGerm z)
    (f : ℂ → ℂ) (he : (f : PuncturedGerm z) = X0Model.meromorphicIncl z u)
    (hu : u ≠ 0) :
    ((f⁻¹ : ℂ → ℂ) : PuncturedGerm z) = X0Model.meromorphicIncl z u⁻¹ := by
  obtain ⟨g, hg, hgm⟩ := u.property
  have hfg : f =ᶠ[𝓝[≠] z] g := Germ.coe_eq.mp (he.trans hg.symm)
  have hne : ∀ᶠ w in 𝓝[≠] z, f w ≠ 0 := by
    have h := hgm.eventually_eq_zero_or_eventually_ne_zero.resolve_left fun hz =>
      hu (Subtype.ext (hg.symm.trans (Germ.coe_eq.mpr hz)))
    filter_upwards [hfg, h] with w hw hw' using hw ▸ hw'
  have hm : (f : PuncturedGerm z) * ((f⁻¹ : ℂ → ℂ) : PuncturedGerm z) = 1 :=
    Germ.coe_eq.mpr (hne.mono fun _ h => mul_inv_cancel₀ h)
  calc
    _ = (X0Model.meromorphicIncl z u⁻¹ * (f : PuncturedGerm z)) *
        ((f⁻¹ : ℂ → ℂ) : PuncturedGerm z) := by
      rw [he, ← map_mul, inv_mul_cancel₀ hu, map_one, one_mul]
    _ = _ := by rw [mul_assoc, hm, mul_one]

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 80000 in
/-- On a tail whose two generator expansions are known, every function in
the rational function field has a convergent expansion and a representative
analytic at the interior parameters sufficiently far along the tail. -/
theorem branch_expansion (N : ℕ) [NeZero N] {K : Type} [Field K]
    (ι : K →+* ℂ) (e : modularFunctionField N →+* LaurentSeries K)
    {I : Type} {F : Filter I} [F.NeBot] (q : I → ℂ) (x : I → UpperHalfPlane)
    (hq : Tendsto q F (𝓝[≠] 0)) (hqn : ∀ i, q i ≠ 0)
    (hJ : ∀ᶠ i in F, HasSum (fun n : ℤ => ι ((e (jGenField N)).coeff n) * q i ^ n)
      (X0Model.analyticJ (x i)))
    (hJN : ∀ᶠ i in F, HasSum (fun n : ℤ => ι ((e (jNGenField N)).coeff n) * q i ^ n)
      (X0Model.analyticJN N (x i))) (a : modularFunctionField N) :
    ∃ f : ℂ → ℂ,
      (∀ w : UpperHalfPlane, (f : PuncturedGerm (w : ℂ)) =
        X0Model.meromorphicIncl (w : ℂ) (X0Model.fieldGerm N w a)) ∧
      ∀ᶠ i in F, AnalyticAt ℂ f (x i : ℂ) ∧
        HasSum (fun n : ℤ => ι ((e a).coeff n) * q i ^ n) (f (x i)) := by
  let E := (coeffMap ι).comp e
  simp_rw [← coeffMap_coeff, ← RingHom.comp_apply (coeffMap ι) e] at hJ hJN ⊢
  let R (a : modularFunctionField N) : Prop := ∃ f : ℂ → ℂ,
    (∀ w : UpperHalfPlane, (f : PuncturedGerm (w : ℂ)) =
      X0Model.meromorphicIncl (w : ℂ) (X0Model.fieldGerm N w a)) ∧
    ∀ᶠ i in F, AnalyticAt ℂ f (x i : ℂ) ∧
      HasSum (fun n : ℤ => (E a).coeff n * q i ^ n) (f (x i))
  change R a
  exact IntermediateField.adjoin_induction ℚ (s := {jq, jqN N})
    (motive := fun y hy => R ⟨y, hy⟩)
    (fun y hy => by
      rcases Set.mem_insert_iff.mp hy with rfl | hy
      · refine ⟨X0Model.analyticJ ∘ UpperHalfPlane.ofComplex,
          fun w => (fieldGerm_first N w).symm, ?_⟩
        filter_upwards [hJ] with i hi
        simpa only [Function.comp_apply, UpperHalfPlane.ofComplex_apply] using
          ⟨X0Model.analyticOn_j (x i) (x i).im_pos, hi⟩
      · obtain rfl := Set.mem_singleton_iff.mp hy
        refine ⟨X0Model.analyticJN N ∘ UpperHalfPlane.ofComplex,
          fun w => (X0Model.fieldGerm_jN N w).symm, ?_⟩
        filter_upwards [hJN] with i hi
        simpa only [Function.comp_apply, UpperHalfPlane.ofComplex_apply] using
          ⟨X0Model.analyticOn_jN N (x i) (x i).im_pos, hi⟩)
    (fun c => by
      have hc : (⟨algebraMap ℚ (LaurentSeries ℚ) c, (modularFunctionField N).algebraMap_mem c⟩ :
          modularFunctionField N) = (c : modularFunctionField N) := by
        apply Subtype.ext
        exact DFunLike.congr_fun (Subsingleton.elim (algebraMap ℚ (LaurentSeries ℚ))
          ((modularFunctionField N).subtype.comp (Rat.castHom (modularFunctionField N)))) c
      change R _
      rw [hc]
      refine ⟨fun _ => (c : ℂ), fun w => ?_, Eventually.of_forall fun i => ⟨analyticAt_const, ?_⟩⟩
      · change (X0Model.meromorphicIncl (w : ℂ)).comp (X0Model.constantGerm (w : ℂ)) (c : ℂ) = _
        simp only [RingHom.comp_apply, map_ratCast]
      · rw [map_ratCast]
        have hc' : (c : LaurentSeries ℂ) = HahnSeries.single 0 (c : ℂ) := by
          rw [← HahnSeries.C_apply, map_ratCast]
        rw [hc']
        simpa only [HahnSeries.coeff_single_same, zpow_zero, mul_one] using
          (hasSum_single (f := fun n : ℤ =>
            (HahnSeries.single 0 (c : ℂ)).coeff n * q i ^ n)
            0 (fun n hn => by rw [HahnSeries.coeff_single_of_ne hn, zero_mul])))
    (fun y z hy hz hy' hz' => by
      let b : modularFunctionField N := ⟨y, hy⟩
      let c : modularFunctionField N := ⟨z, hz⟩
      change R (b + c)
      obtain ⟨f, hfe, hf⟩ := hy'
      obtain ⟨g, hge, hg⟩ := hz'
      refine ⟨f + g, fun w => ?_, ?_⟩
      · rw [Germ.coe_add, hfe, hge]
        exact (((X0Model.meromorphicIncl (w : ℂ)).comp (X0Model.fieldGerm N w)).map_add b c).symm
      · filter_upwards [hf, hg] with i hi hi'
        refine ⟨hi.1.add hi'.1, ?_⟩
        simpa only [b, c, map_add, HahnSeries.coeff_add, add_mul, Pi.add_apply] using hi.2.add hi'.2)
    (fun y hy hy' => by
      let b : modularFunctionField N := ⟨y, hy⟩
      change R b⁻¹
      by_cases hb : b = 0
      · rw [hb, inv_zero]
        exact hb ▸ hy'
      obtain ⟨f, hfe, hf⟩ := hy'
      obtain ⟨i, hi⟩ := hf.exists
      have hn : E b ≠ 0 := (map_ne_zero_iff E E.injective).mpr hb
      have hInv := X0Model2.eventually_hasSum_laurent_inv hn (hqn i) hi.2
      refine ⟨f⁻¹, fun w => ?_, ?_⟩
      · rw [map_inv₀ (X0Model.fieldGerm N w)]
        exact germ_inverse _ f (hfe w) ((map_ne_zero_iff _ (X0Model.fieldGerm N w).injective).mpr hb)
      · filter_upwards [hf, hq.eventually hInv] with i hi hi'
        obtain ⟨hne, hs⟩ := hi' (f (x i)) hi.2
        refine ⟨hi.1.inv hne, ?_⟩
        simpa only [map_inv₀, Pi.inv_apply] using hs)
    (fun y z hy hz hy' hz' => by
      let b : modularFunctionField N := ⟨y, hy⟩
      let c : modularFunctionField N := ⟨z, hz⟩
      change R (b * c)
      obtain ⟨f, hfe, hf⟩ := hy'
      obtain ⟨g, hge, hg⟩ := hz'
      obtain ⟨i, hi⟩ := hf.exists
      obtain ⟨j, hj⟩ := hg.exists
      have hMul := X0Model2.eventually_hasSum_laurent_mul (hqn i) (hqn j) hi.2 hj.2
      refine ⟨f * g, fun w => ?_, ?_⟩
      · rw [Germ.coe_mul, hfe, hge]
        exact (((X0Model.meromorphicIncl (w : ℂ)).comp (X0Model.fieldGerm N w)).map_mul b c).symm
      · filter_upwards [hf, hg, hq.eventually hMul] with i hi hj hm
        exact ⟨hi.1.mul hj.1, by
          simpa only [b, c, map_mul, Pi.mul_apply] using hm (f (x i)) (g (x i)) hi.2 hj.2⟩)
    a.property


end ZInQ.Manuscript.RC.J0Cusps
