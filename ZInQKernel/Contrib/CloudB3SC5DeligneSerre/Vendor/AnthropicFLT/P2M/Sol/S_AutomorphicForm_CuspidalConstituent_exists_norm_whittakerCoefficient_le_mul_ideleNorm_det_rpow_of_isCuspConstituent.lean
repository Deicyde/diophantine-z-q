/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AutomorphicForm_CuspidalConstituent_exists_norm_whittakerCoefficient_le_mul_ideleNorm_det_rpow_of_isCuspConstituent (git blob 4d8100a4ed9b8d6934440ab57e7ce99e8264dcb0, sha256 7a4ea46db22c98a5b75d16294907d5ac164cf29d47c016b62c662d3828fa1bc4).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CuspidalConstituent
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_RowIsometryInvariance
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_WhittakerCoefficient
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicTraceFin
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_TateGlobalZeta
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicBox
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_norm_le_mul_ideleNorm_det_rpow_of_isCuspConstituent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AutomorphicForm_CuspidalConstituent_exists_norm_whittakerCoefficient_le_mul_ideleNorm_det_rpow_of_isCuspConstituent

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open _root_.AutomorphicForm hiding continuous_unipotentGL2
open _root_.AutomorphicForm.WindowedSiegel
open _root_.AutomorphicForm.SiegelCovering
open _root_.IsDedekindDomain
open AutomorphicForm.CuspidalConstituent
open scoped ProbabilityTheory

namespace RS11WB

theorem det_unipotentGL2 {A : Type*} [CommRing A] (x : A) :
    Matrix.GeneralLinearGroup.det (unipotentGL2 x) = 1 := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply, unipotentGL2_coe, Matrix.det_fin_two_of]
  simp

theorem continuous_unipotentGL2 (A : Type*) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] :
    Continuous (fun x : A => (unipotentGL2 x : GL (Fin 2) A)) := by
  have hmat : ∀ s : A → A, Continuous s → Continuous (fun x : A => (!![1, s x; 0, 1] : Matrix (Fin 2) (Fin 2) A)) := by
    intro s hs
    refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp [hs, continuous_const]
  rw [Units.continuous_iff]
  constructor
  · have h__af := hmat id continuous_id
    simp [unipotentGL2_coe] at h__af
    exact h__af
  · have hinv : ∀ x : A, ((unipotentGL2 x : GL (Fin 2) A)⁻¹ : GL (Fin 2) A) = unipotentGL2 (-x) := by
      intro x
      rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← unipotentGL2_add, neg_add_cancel, unipotentGL2_zero]
    simp only [hinv]
    simpa [unipotentGL2_coe] using hmat Neg.neg continuous_neg

end RS11WB

theorem solution
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (ξ : (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).Z →* ℂˣ)
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥)
    (tys : AutomorphicForm.ArchTypeFamily K)
    (V : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ))
    (hV : IsCuspConstituent K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ξ V)
    (y : AdelicGL2 (𝓞 K) K → ℂ)
    (hy : y ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys)
    (w₀ : ℝ)
    (hξ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w₀) :
    ∃ M : ℝ, ∀ g : AdelicGL2 (𝓞 K) K,
      ‖whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1 g‖ ≤
        M * NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (w₀ / 2) := by
  classical
  obtain ⟨M, hM⟩ :=
    AutomorphicForm.CuspidalConstituent.exists_norm_le_mul_ideleNorm_det_rpow_of_isCuspConstituent
      K c u d₁ d₂ T hc hd₁ hd hcov ξ N hN tys V hV y hy w₀ hξ
  letI := adeleBorel (𝓞 K) K
  haveI := borelSpace_adeleBorel (𝓞 K) K
  set μ : Measure (AdeleRing (𝓞 K) K) := adelicAddHaar (𝓞 K) K with hμ
  set B : Set (AdeleRing (𝓞 K) K) := adelicBox K with hB
  set ψ := NumberField.StandardAddChar.stdAddChar K with hψ

  obtain ⟨C, hCc, hBC⟩ := exists_isCompact_adelicBox_subset K
  have hψc : Continuous fun x : AdeleRing (𝓞 K) K => ψ (-(algebraMap K (AdeleRing (𝓞 K) K) 1 * x)) :=
    (NumberField.StandardAddChar.adelicTraceData K).continuous_psiK.comp ((continuous_const.mul continuous_id).neg)
  obtain ⟨Cψ, hCψ⟩ := hCc.exists_bound_of_continuousOn (f := fun x => ψ (-(algebraMap K (AdeleRing (𝓞 K) K) 1 * x)))
    hψc.continuousOn
  have hCψ0 : 0 ≤ max Cψ 0 := le_max_right _ _
  have hBfin : μ B < ⊤ := adelicAddHaar_adelicBox_lt_top K
  have hBmeas : MeasurableSet B := measurableSet_adelicBox K
  refine ⟨M * max Cψ 0, fun g => ?_⟩
  set D : ℝ := NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (w₀ / 2) with hD
  have hMD : 0 ≤ M * D := (norm_nonneg _).trans (hM g)

  have hW : whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1 g =
      ((μ B)⁻¹).toReal • ∫ x in B, y (unipotentGL2 x * g) * ψ (-(algebraMap K (AdeleRing (𝓞 K) K) 1 * x)) ∂μ := by
    unfold whittakerCoefficient
    dsimp only [productionPinsOf]
    exact integral_smul_measure _ _

  have hpt : ∀ x ∈ B, ‖y (unipotentGL2 x * g) * ψ (-(algebraMap K (AdeleRing (𝓞 K) K) 1 * x))‖ ≤ M * D * max Cψ 0 := by
    intro x hx
    rw [norm_mul]
    refine mul_le_mul ?_ ((hCψ x (hBC hx)).trans (le_max_left _ _)) (norm_nonneg _) hMD
    have h := hM (unipotentGL2 x * g)
    rwa [map_mul, RS11WB.det_unipotentGL2, one_mul] at h
  have hint := norm_setIntegral_le_of_norm_le_const hBfin hpt
  rw [hW, norm_smul, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
  calc (μ B)⁻¹.toReal * ‖∫ x in B, y (unipotentGL2 x * g) * ψ (-(algebraMap K (AdeleRing (𝓞 K) K) 1 * x)) ∂μ‖
      ≤ (μ B)⁻¹.toReal * (M * D * max Cψ 0 * (μ B).toReal) :=
        mul_le_mul_of_nonneg_left hint ENNReal.toReal_nonneg
    _ = ((μ B)⁻¹.toReal * (μ B).toReal) * (M * max Cψ 0 * D) := by ring
    _ ≤ 1 * (M * max Cψ 0 * D) := by
        apply mul_le_mul_of_nonneg_right _ (by nlinarith [hMD, hCψ0])
        rw [ENNReal.toReal_inv]
        by_cases h0 : (μ B).toReal = 0
        · rw [h0, mul_zero]; exact zero_le_one
        · rw [inv_mul_cancel₀ h0]
    _ = M * max Cψ 0 * D := one_mul _
