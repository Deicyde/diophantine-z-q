/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AutomorphicForm_norm_integral_mul_le_mul_setIntegral_norm_of_isCuspidalFn (git blob 3c682cdd9f8a181c0dcc2cb4c11566d2625cb251, sha256 c8353cbae4fe5fec6750dcfd793752c4fa9f8f338deebbc7ad0ef30bfbb18001).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ConstantTerm
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicBox
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_integral_mul_eq_integral_mul_weight_mul_tsum_sub_average_of_isCuspidalFn
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_NumberField_AdeleRing_finite_setOf_algebraMap_mem_of_isCompact

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AutomorphicForm_norm_integral_mul_le_mul_setIntegral_norm_of_isCuspidalFn

open NumberField NumberField.AdelicHaar NumberField.AdelicBox AutomorphicForm MeasureTheory
open scoped ProbabilityTheory

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.glBorel

namespace CuspidalUnfoldingWeight

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

variable (K : Type) [Field K] [NumberField K]

private scoped instance countable_numberField : Countable K :=
  (Module.finBasis ℚ K).equivFun.injective.countable





private theorem unip_inv (t : (AdeleRing (𝓞 K) K)) : (unipotentGL2 t)⁻¹ = unipotentGL2 (-t) :=
  inv_eq_of_mul_eq_one_right (by rw [← unipotentGL2_add, add_neg_cancel, unipotentGL2_zero])

private theorem continuous_unip : Continuous (fun t : (AdeleRing (𝓞 K) K) => unipotentGL2 t) := by
  have hval : Continuous (fun t : (AdeleRing (𝓞 K) K) => ((unipotentGL2 t : (GL (Fin 2) (AdeleRing (𝓞 K) K))) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))) := by
    refine continuous_matrix fun i j => ?_
    simp only [unipotentGL2_coe]
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  refine Units.continuous_iff.2 ⟨hval, ?_⟩
  simp only [unip_inv]
  exact hval.comp continuous_neg

private theorem continuous_entry : Continuous (fun g : (GL (Fin 2) (AdeleRing (𝓞 K) K)) => ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 1)) :=
  Units.continuous_val.matrix_elem 0 1

private theorem entry_unip (t : (AdeleRing (𝓞 K) K)) : ((unipotentGL2 t : (GL (Fin 2) (AdeleRing (𝓞 K) K))) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 1 = t := by
  simp [unipotentGL2_coe]

private theorem finite_setOf_unip_mul_mem {C : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))} (hC : IsCompact C) (y : (GL (Fin 2) (AdeleRing (𝓞 K) K))) :
    {β : K | unipotentGL2 ((algebraMap K (AdeleRing (𝓞 K) K)) β) * y ∈ C}.Finite := by
  have hD : IsCompact ((fun g : (GL (Fin 2) (AdeleRing (𝓞 K) K)) => ((g * y⁻¹ : (GL (Fin 2) (AdeleRing (𝓞 K) K))) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 1) '' C) :=
    hC.image ((continuous_entry K).comp (continuous_mul_const y⁻¹))
  refine (NumberField.AdeleRing.finite_setOf_algebraMap_mem_of_isCompact K hD).subset fun β hβ => ?_
  refine ⟨unipotentGL2 ((algebraMap K (AdeleRing (𝓞 K) K)) β) * y, hβ, ?_⟩
  show ((unipotentGL2 ((algebraMap K (AdeleRing (𝓞 K) K)) β) * y * y⁻¹ : (GL (Fin 2) (AdeleRing (𝓞 K) K))) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 1 = (algebraMap K (AdeleRing (𝓞 K) K)) β
  rw [mul_inv_cancel_right, entry_unip]

private theorem isCompact_translates {S : Set (AdeleRing (𝓞 K) K)} (hS : IsCompact S) (x : (GL (Fin 2) (AdeleRing (𝓞 K) K))) {T : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))} (hT : IsCompact T) :
    IsCompact (Set.image2 (fun (t : (AdeleRing (𝓞 K) K)) (c : (GL (Fin 2) (AdeleRing (𝓞 K) K))) => unipotentGL2 t * x * c) S T) := by
  have hcont : Continuous (fun p : (AdeleRing (𝓞 K) K) × (GL (Fin 2) (AdeleRing (𝓞 K) K)) => unipotentGL2 p.1 * x * p.2) :=
    (((continuous_unip K).comp continuous_fst).mul continuous_const).mul continuous_snd
  rw [← Set.image_prod]
  exact (hS.prod hT).image hcont

private theorem isCompact_closure_box : IsCompact (closure (adelicBox K)) := by
  obtain ⟨C, hC, hsub⟩ := exists_isCompact_adelicBox_subset K
  exact hC.closure_of_subset hsub

private noncomputable def mult (R : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))) (y : (GL (Fin 2) (AdeleRing (𝓞 K) K))) : ℝ :=
  ∑' β : K, R.indicator (fun _ => (1 : ℝ)) (unipotentGL2 ((algebraMap K (AdeleRing (𝓞 K) K)) β) * y)

private theorem mult_nonneg (R : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))) (y : (GL (Fin 2) (AdeleRing (𝓞 K) K))) : 0 ≤ mult K R y :=
  tsum_nonneg fun _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _

private theorem mult_unip_mul (R : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))) (γ : K) (y : (GL (Fin 2) (AdeleRing (𝓞 K) K))) :
    mult K R (unipotentGL2 ((algebraMap K (AdeleRing (𝓞 K) K)) γ) * y) = mult K R y := by
  unfold mult
  have h : ∀ β : K, R.indicator (fun _ => (1 : ℝ)) (unipotentGL2 ((algebraMap K (AdeleRing (𝓞 K) K)) β) * (unipotentGL2 ((algebraMap K (AdeleRing (𝓞 K) K)) γ) * y))
      = R.indicator (fun _ => (1 : ℝ)) (unipotentGL2 ((algebraMap K (AdeleRing (𝓞 K) K)) (β + γ)) * y) := by
    intro β
    rw [map_add, unipotentGL2_add, mul_assoc]
  rw [tsum_congr h]
  exact (Equiv.addRight γ).tsum_eq (fun β : K => R.indicator (fun _ => (1 : ℝ)) (unipotentGL2 ((algebraMap K (AdeleRing (𝓞 K) K)) β) * y))

private theorem summable_mult {R : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))} (hR : IsCompact R) (y : (GL (Fin 2) (AdeleRing (𝓞 K) K))) :
    Summable fun β : K => R.indicator (fun _ => (1 : ℝ)) (unipotentGL2 ((algebraMap K (AdeleRing (𝓞 K) K)) β) * y) := by
  refine summable_of_ne_finset_zero (s := (finite_setOf_unip_mul_mem K hR y).toFinset) fun β hβ => ?_
  rw [Set.Finite.mem_toFinset] at hβ
  exact Set.indicator_of_notMem hβ (fun _ => (1 : ℝ))

private theorem one_le_mult {R : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))} (hR : IsCompact R) {y : (GL (Fin 2) (AdeleRing (𝓞 K) K))} (hy : y ∈ R) : 1 ≤ mult K R y := by
  have h0 : R.indicator (fun _ => (1 : ℝ)) (unipotentGL2 ((algebraMap K (AdeleRing (𝓞 K) K)) (0 : K)) * y) = 1 := by
    rw [map_zero, unipotentGL2_zero, one_mul, Set.indicator_of_mem hy]
  have hle := (summable_mult K hR y).le_tsum 0 fun _ _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _
  rw [h0] at hle
  exact hle

private theorem measurable_mult {R : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))} (hRm : MeasurableSet R) : Measurable (mult K R) := by
  have h : ∀ β : K, Measurable fun y : (GL (Fin 2) (AdeleRing (𝓞 K) K)) => R.indicator (fun _ => (1 : ℝ)) (unipotentGL2 ((algebraMap K (AdeleRing (𝓞 K) K)) β) * y) :=
    fun β => (measurable_const.indicator hRm).comp (measurable_const_mul _)
  unfold mult
  exact Measurable.tsum h

private theorem exists_weight
    (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (x : GL (Fin 2) (AdeleRing (𝓞 K) K))
    (hfs : HasCompactSupport f) :
    IsCompact (Set.image2 (fun (t : AdeleRing (𝓞 K) K) (c : GL (Fin 2) (AdeleRing (𝓞 K) K)) =>
        unipotentGL2 t * x * c) (closure (adelicBox K)) (tsupport f))
    ∧ ∃ w : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℝ, Measurable w ∧ (∀ y, 0 ≤ w y)
      ∧ (∀ (t : AdeleRing (𝓞 K) K) (c : GL (Fin 2) (AdeleRing (𝓞 K) K)), c ∈ tsupport f →
          ∑' β : K, w (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) *
            (unipotentGL2 t * x * c)) = 1)
      ∧ ∀ y, w y ≤ (Set.image2 (fun (t : AdeleRing (𝓞 K) K)
            (c : GL (Fin 2) (AdeleRing (𝓞 K) K)) => unipotentGL2 t * x * c)
            (closure (adelicBox K)) (tsupport f)).indicator 1 y := by
  set R := Set.image2 (fun (t : AdeleRing (𝓞 K) K) (c : GL (Fin 2) (AdeleRing (𝓞 K) K)) =>
    unipotentGL2 t * x * c) (closure (adelicBox K)) (tsupport f) with hRdef
  have hR : IsCompact R := isCompact_translates K (isCompact_closure_box K) x hfs
  have hRm : MeasurableSet R := hR.isClosed.measurableSet
  refine ⟨hR, fun y => R.indicator (fun _ => (1 : ℝ)) y / mult K R y, ?_, ?_, ?_, ?_⟩
  · exact (measurable_const.indicator hRm).div (measurable_mult K hRm)
  · intro y
    exact div_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _) (mult_nonneg K R y)
  · intro t c hc
    have hpos : 0 < mult K R (unipotentGL2 t * x * c) := by
      obtain ⟨k, hk, -⟩ := existsUnique_algebraMap_add_mem_adelicBox K t
      have h : unipotentGL2 ((algebraMap K (AdeleRing (𝓞 K) K)) k + t) * x * c ∈ R := Set.mem_image2_of_mem (subset_closure hk) hc
      have hmem : unipotentGL2 ((algebraMap K (AdeleRing (𝓞 K) K)) k) * (unipotentGL2 t * x * c) ∈ R := by
        rw [unipotentGL2_add] at h
        simp only [mul_assoc] at h ⊢
        exact h
      have h1 := one_le_mult K hR hmem
      rw [mult_unip_mul] at h1
      exact lt_of_lt_of_le one_pos h1
    calc ∑' β : K, R.indicator (fun _ => (1 : ℝ)) (unipotentGL2 ((algebraMap K (AdeleRing (𝓞 K) K)) β) * (unipotentGL2 t * x * c))
            / mult K R (unipotentGL2 ((algebraMap K (AdeleRing (𝓞 K) K)) β) * (unipotentGL2 t * x * c))
        = ∑' β : K, R.indicator (fun _ => (1 : ℝ)) (unipotentGL2 ((algebraMap K (AdeleRing (𝓞 K) K)) β) * (unipotentGL2 t * x * c))
            / mult K R (unipotentGL2 t * x * c) := by
          refine tsum_congr fun β => ?_
          rw [mult_unip_mul]
      _ = (∑' β : K, R.indicator (fun _ => (1 : ℝ)) (unipotentGL2 ((algebraMap K (AdeleRing (𝓞 K) K)) β) * (unipotentGL2 t * x * c)))
            / mult K R (unipotentGL2 t * x * c) := tsum_div_const
      _ = mult K R (unipotentGL2 t * x * c) / mult K R (unipotentGL2 t * x * c) := rfl
      _ = 1 := div_self hpos.ne'
  · intro y
    dsimp only
    by_cases hy : y ∈ R
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, Pi.one_apply]
      exact div_le_one_of_le₀ (one_le_mult K hR hy) (mult_nonneg K R y)
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, zero_div]

end CuspidalUnfoldingWeight
open scoped _root_.P2MW.S_AutomorphicForm_norm_integral_mul_le_mul_setIntegral_norm_of_isCuspidalFn.CuspidalUnfoldingWeight

open CuspidalUnfoldingWeight in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (φ f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (x : GL (Fin 2) (AdeleRing (𝓞 K) K))
    (hφN : ∀ (β : K) (y : GL (Fin 2) (AdeleRing (𝓞 K) K)),
      φ (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) * y) = φ y)
    (hφi : LocallyIntegrable φ (adelicGLHaar (Fin 2) (𝓞 K) K))
    (hφc : IsCuspidalFn ((adelicAddHaar (𝓞 K) K)[|adelicBox K]) unipotentGL2 φ)
    (hf : Continuous f) (hfs : HasCompactSupport f)
    (ε : ℝ)
    (hP : ∀ y, ‖(∑' β : K, f (x⁻¹ * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) * y))
        - (((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ)⁻¹ *
            ∫ t, f (x⁻¹ * unipotentGL2 t * y) ∂(adelicAddHaar (𝓞 K) K)‖ ≤ ε) :
    ‖∫ y, φ y * f (x⁻¹ * y) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)‖
      ≤ ε * ∫ y in Set.image2 (fun (t : AdeleRing (𝓞 K) K) (c : GL (Fin 2) (AdeleRing (𝓞 K) K)) =>
          unipotentGL2 t * x * c) (closure (adelicBox K)) (tsupport f),
          ‖φ y‖ ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
  obtain ⟨hR, w, hw, hw0, hw1, hwR⟩ := exists_weight K f x hfs
  set R := Set.image2 (fun (t : AdeleRing (𝓞 K) K) (c : GL (Fin 2) (AdeleRing (𝓞 K) K)) =>
    unipotentGL2 t * x * c) (closure (adelicBox K)) (tsupport f) with hRdef
  rw [AutomorphicForm.integral_mul_eq_integral_mul_weight_mul_tsum_sub_average_of_isCuspidalFn
    K φ f x hφN hφi hφc hf hfs w hw hw0 hw1]
  haveI : OpensMeasurableSpace (GL (Fin 2) (AdeleRing (𝓞 K) K)) :=
    (NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 K) K).opensMeasurable
  have hRm : MeasurableSet R := hR.isClosed.measurableSet

  have hIR : IntegrableOn (fun y => ‖φ y‖) R (adelicGLHaar (Fin 2) (𝓞 K) K) :=
    (hφi.integrableOn_isCompact hR).norm
  have hdom : Integrable (fun y => ε * R.indicator (fun y => ‖φ y‖) y)
      (adelicGLHaar (Fin 2) (𝓞 K) K) :=
    (hIR.integrable_indicator hRm).const_mul ε
  calc ‖∫ y, φ y * (w y : ℂ) *
          ((∑' β : K, f (x⁻¹ * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) * y))
            - (((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ)⁻¹ *
                ∫ t, f (x⁻¹ * unipotentGL2 t * y) ∂(adelicAddHaar (𝓞 K) K))
          ∂(adelicGLHaar (Fin 2) (𝓞 K) K)‖
      ≤ ∫ y, ‖φ y * (w y : ℂ) *
          ((∑' β : K, f (x⁻¹ * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) * y))
            - (((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ)⁻¹ *
                ∫ t, f (x⁻¹ * unipotentGL2 t * y) ∂(adelicAddHaar (𝓞 K) K))‖
          ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := norm_integral_le_integral_norm _
    _ ≤ ∫ y, ε * R.indicator (fun y => ‖φ y‖) y ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => norm_nonneg _)
            hdom (Filter.Eventually.of_forall fun y => ?_)
          dsimp only
          rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hw0 y)]
          have h1 : w y ≤ R.indicator 1 y := hwR y
          by_cases hy : y ∈ R
          · have h1' : w y ≤ 1 := by simpa [Set.indicator_of_mem hy] using h1
            rw [Set.indicator_of_mem hy]
            calc ‖φ y‖ * w y * _ ≤ ‖φ y‖ * 1 * ε := by
                  gcongr
                  exact hP y
              _ = ε * ‖φ y‖ := by ring
          · rw [Set.indicator_of_notMem hy] at h1 ⊢
            have hw00 : w y = 0 := le_antisymm (by simpa using h1) (hw0 y)
            simp [hw00]
    _ = ε * ∫ y in R, ‖φ y‖ ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
          rw [integral_const_mul, integral_indicator hRm]
