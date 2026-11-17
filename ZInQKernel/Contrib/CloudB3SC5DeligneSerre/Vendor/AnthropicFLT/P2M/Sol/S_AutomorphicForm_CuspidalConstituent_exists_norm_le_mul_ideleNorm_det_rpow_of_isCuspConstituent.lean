/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AutomorphicForm_CuspidalConstituent_exists_norm_le_mul_ideleNorm_det_rpow_of_isCuspConstituent (git blob e52877c33fd54fa9b3e945a10c91d8d8b8f3ffec, sha256 056f03f995da11507e51f4d28176a3f7be3e3c4f4818d7e3b4c6eeab7e72ad1c).
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
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_eq_rightConv_of_mem_cut
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_exists_forall_norm_rightConv_le_of_ideleNorm_det_mem_Icc
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_CuspidalConstituent_continuous_and_isSmoothCuspAutomorphicFnAt_rightTranslate_of_mem_cuspKFiniteSubmodule
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AutomorphicForm_CuspidalConstituent_exists_norm_le_mul_ideleNorm_det_rpow_of_isCuspConstituent

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox
open _root_.AutomorphicForm hiding det_centralScalar
namespace AutomorphicForm
end AutomorphicForm
open _root_.P2MW.S_AutomorphicForm_CuspidalConstituent_exists_norm_le_mul_ideleNorm_det_rpow_of_isCuspConstituent.AutomorphicForm
open _root_.AutomorphicForm.WindowedSiegel
open _root_.AutomorphicForm.SiegelCovering
open _root_.IsDedekindDomain
open AutomorphicForm.CuspidalConstituent NumberField.TateGlobal
open scoped NNReal

noncomputable section

namespace AutomorphicForm
export _root_.AutomorphicForm (productionPinsOf AdelicGL2 centralScalar finiteAdelicGL2Subgroup lsXiMemberAt_iff ArchTypeFamily archCutSubmodule exists_forall_norm_rightConv_le_of_ideleNorm_det_mem_Icc)
open _root_.AutomorphicForm hiding det_centralScalar

namespace RegBdd

variable (K : Type) [Field K] [NumberField K]

theorem rightTranslate_one (φ : AdelicGL2 (𝓞 K) K → ℂ) : rightTranslate K 1 φ = φ := by
  funext x; simp [rightTranslate]

theorem det_centralScalar (z : (AdeleRing (𝓞 K) K)ˣ) :
    Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z) = z * z := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  change (Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 K) K)).det = _
  rw [Matrix.det_fin_two]
  simp

theorem main
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
      ‖y g‖ ≤ M * NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (w₀ / 2) := by

  obtain ⟨x', hx', α, hα, -, -, hyeq⟩ :=
    exists_eq_rightConv_of_mem_cut K c u d₁ d₂ T hc hd₁ hd hcov ξ V hV N hN tys y hy

  have hx'V : x' ∈ V := (Submodule.mem_inf.mp (Submodule.mem_inf.mp hx').1).1
  obtain ⟨hx'cont, hx'sm⟩ :=
    continuous_and_isSmoothCuspAutomorphicFnAt_rightTranslate_of_mem_cuspKFiniteSubmodule K _ _ _ ξ x' (hV.1.le hx'V)
  have hx'cusp := (hx'sm 1).1
  rw [rightTranslate_one] at hx'cusp
  obtain ⟨M, hM⟩ := exists_forall_norm_rightConv_le_of_ideleNorm_det_mem_Icc K c u d₁ d₂ T hd hcov ξ x' hx'cusp hx'cont
    α hα 1 1 one_pos

  have hyV : y ∈ V := (Submodule.mem_inf.mp (Submodule.mem_inf.mp hy).1).1
  obtain ⟨-, hysm⟩ :=
    continuous_and_isSmoothCuspAutomorphicFnAt_rightTranslate_of_mem_cuspKFiniteSubmodule K _ _ _ ξ y (hV.1.le hyV)
  have hycusp := (hysm 1).1
  rw [rightTranslate_one] at hycusp
  letI : MeasurableSpace (AdelicGL2 (𝓞 K) K) := NumberField.AdelicHaar.glBorel (Fin 2) (𝓞 K) K
  have hls := ((lsXiMemberAt_iff (𝓞 K) K _ _ ξ _ y).mp hycusp.1).1
  have hcent : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
      y (centralScalar (𝓞 K) K z * g) = ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * y g :=
    fun z g => hls.central_transform ⟨z, Subgroup.mem_top z⟩ g

  obtain ⟨sec, -, hsec, -⟩ := NumberField.TateGlobal.exists_continuous_monoidHom_ideleNorm_apply_eq K
  refine ⟨M, fun g => ?_⟩
  set r : ℝ := ideleNorm K (Matrix.GeneralLinearGroup.det g) with hr_def
  have hr : 0 < r := ideleNorm_pos _
  have hρpos : 0 < r ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hr _
  have hρne : (⟨r ^ (-(1 / 2 : ℝ)), hρpos.le⟩ : ℝ≥0) ≠ 0 := by
    intro h
    have h' := congrArg (fun x : ℝ≥0 => (x : ℝ)) h
    exact hρpos.ne' h'
  set ρ : ℝ≥0ˣ := Units.mk0 (⟨r ^ (-(1 / 2 : ℝ)), hρpos.le⟩ : ℝ≥0) hρne with hρ
  set z : (AdeleRing (𝓞 K) K)ˣ := sec ρ with hz_def
  have hz : ideleNorm K z = r ^ (-(1 / 2 : ℝ)) := by
    rw [hz_def, hsec]; rfl
  have hdet : ideleNorm K (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z * g)) = 1 := by
    rw [map_mul, det_centralScalar, ideleNorm_mul, ideleNorm_mul, hz, ← hr_def, ← Real.rpow_add hr,
      show (-(1 / 2 : ℝ)) + -(1 / 2 : ℝ) = -1 by ring, Real.rpow_neg_one, inv_mul_cancel₀ hr.ne']
  have hb := hM (centralScalar (𝓞 K) K z * g) ⟨le_of_eq hdet.symm, le_of_eq hdet⟩
  rw [← hyeq, hcent z g, norm_mul, hξ z, hz] at hb
  have hpow : ((r ^ (-(1 / 2 : ℝ))) ^ w₀ : ℝ) = (r ^ (w₀ / 2))⁻¹ := by
    rw [← Real.rpow_mul hr.le, ← Real.rpow_neg hr.le]
    congr 1
    ring
  have hpos : 0 < r ^ (w₀ / 2) := Real.rpow_pos_of_pos hr _
  rw [hpow] at hb
  calc ‖y g‖ = r ^ (w₀ / 2) * ((r ^ (w₀ / 2))⁻¹ * ‖y g‖) := by
        rw [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul]
    _ ≤ r ^ (w₀ / 2) * M := mul_le_mul_of_nonneg_left hb hpos.le
    _ = M * r ^ (w₀ / 2) := mul_comm _ _

end RegBdd

end AutomorphicForm

end

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
      ‖y g‖ ≤ M * NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (w₀ / 2) :=
  AutomorphicForm.RegBdd.main K c u d₁ d₂ T hc hd₁ hd hcov ξ N hN tys V hV y hy w₀ hξ
