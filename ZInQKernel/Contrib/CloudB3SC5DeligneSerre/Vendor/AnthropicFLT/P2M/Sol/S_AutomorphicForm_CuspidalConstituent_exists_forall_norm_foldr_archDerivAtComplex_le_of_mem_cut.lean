/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AutomorphicForm_CuspidalConstituent_exists_forall_norm_foldr_archDerivAtComplex_le_of_mem_cut (git blob 91252ad7c87f9fb3a62405f7e6cb3d51f62092ab, sha256 a17115bde10847e5fa0ed9b22f42c5328c77baaf88f5287435e8563b6072a3cb).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CuspidalConstituent
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_TateGlobalZeta
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_FactorizableTestFn
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_RightConvolution
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_eq_rightConv_of_mem_cut
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_archDerivAtComplex_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_exists_forall_norm_rightConv_le_of_ideleNorm_det_mem_Icc
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_CuspidalConstituent_continuous_and_isSmoothCuspAutomorphicFnAt_rightTranslate_of_mem_cuspKFiniteSubmodule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AutomorphicForm_CuspidalConstituent_exists_forall_norm_foldr_archDerivAtComplex_le_of_mem_cut

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open AutomorphicForm.CuspidalConstituent

noncomputable section

namespace CoreSupplyC

variable (K : Type) [Field K] [NumberField K]

theorem isFactorizableTestFn_leftDeriv {w : InfinitePlace K} (hw : w.IsComplex) (d : ArchDirComplex)
    (α : AdelicGL2 (𝓞 K) K → ℂ) (hα : IsFactorizableTestFn K α) :
    IsFactorizableTestFn K (fun y => deriv (fun t : ℝ => α (archFlowAtComplex hw d (-t) * y)) 0) := by
  obtain ⟨fa, ff, hfa, hff, hαeq⟩ := hα
  obtain ⟨fa', hfa', heq⟩ :=
    (AutomorphicForm.archDerivAtComplex_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn K hw d).2.1 fa ff hfa
  refine ⟨fa', ff, hfa', hff, fun y => ?_⟩
  have h1 : (fun t : ℝ => α (archFlowAtComplex hw d (-t) * y)) =
      fun t : ℝ => fa (glArch (𝓞 K) K (archFlowAtComplex hw d (-t) * y)) * ff (glFin (𝓞 K) K (archFlowAtComplex hw d (-t) * y)) := by
    funext t; exact hαeq _
  show deriv (fun t : ℝ => α (archFlowAtComplex hw d (-t) * y)) 0 = _
  rw [h1]
  exact congrFun heq y

theorem exists_foldr_eq_rightConv {w : InfinitePlace K} (hw : w.IsComplex) (x' α : AdelicGL2 (𝓞 K) K → ℂ)
    (hcont : Continuous x') (hα : IsFactorizableTestFn K α) (l : List ArchDirComplex) :
    ∃ γ : AdelicGL2 (𝓞 K) K → ℂ, IsFactorizableTestFn K γ ∧
      l.foldr (archDerivAtComplex hw) (rightConv K x' α) = rightConv K x' γ := by
  induction l with
  | nil => exact ⟨α, hα, rfl⟩
  | cons d l ih =>
    obtain ⟨γ, hγ, hfold⟩ := ih
    refine ⟨fun y => deriv (fun t : ℝ => γ (archFlowAtComplex hw d (-t) * y)) 0,
      isFactorizableTestFn_leftDeriv K hw d γ hγ, ?_⟩
    rw [List.foldr_cons, hfold]
    exact ((AutomorphicForm.archDerivAtComplex_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn K hw d).1 x' γ hcont hγ).2

theorem rightTranslate_one' (φ : AdelicGL2 (𝓞 K) K → ℂ) : rightTranslate K 1 φ = φ := by
  funext x; simp [rightTranslate]

def dirs : List ArchDirComplex := [.H, .E, .Fm, .iH, .iE, .iFm]

theorem mem_dirs (d : ArchDirComplex) : d ∈ dirs := by
  cases d <;> simp [dirs]

end CoreSupplyC

end

open CoreSupplyC in

theorem solution
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (ξ : (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).Z →* ℂˣ)
    (V : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ))
    (hV : IsCuspConstituent K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ξ V)
    (w₀ : ℝ)
    (hξ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w₀)
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (tys : AutomorphicForm.ArchTypeFamily K)
    (x : AdelicGL2 (𝓞 K) K → ℂ) (hx : x ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys)
    (w : InfinitePlace K) (hw : w.IsComplex)
    (e₁ e₂ : ℝ) (he₁ : 0 < e₁) (he : e₁ < e₂) (l : List ArchDirComplex) :
    ∃ B : ℝ, ∀ g : AdelicGL2 (𝓞 K) K,
      NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂ →
      ‖(l.foldr (archDerivAtComplex hw) x) g‖ ≤ B := by
  classical

  obtain ⟨x', hx', α, hα, -, -, hxeq⟩ :=
    AutomorphicForm.CuspidalConstituent.exists_eq_rightConv_of_mem_cut K c u d₁ d₂ T hc hd₁ hd hcov ξ V hV N hN tys x hx
  have hx'V : x' ∈ V := (Submodule.mem_inf.mp (Submodule.mem_inf.mp hx').1).1
  obtain ⟨hx'cont, hx'sm⟩ :=
    AutomorphicForm.CuspidalConstituent.continuous_and_isSmoothCuspAutomorphicFnAt_rightTranslate_of_mem_cuspKFiniteSubmodule
      K _ _ _ ξ x' (hV.1.le hx'V)
  have hx'cusp := (hx'sm 1).1
  rw [CoreSupplyC.rightTranslate_one'] at hx'cusp

  obtain ⟨γ, hγ, hfold⟩ := CoreSupplyC.exists_foldr_eq_rightConv K hw x' α hx'cont hα l
  obtain ⟨M, hM⟩ := AutomorphicForm.exists_forall_norm_rightConv_le_of_ideleNorm_det_mem_Icc K c u d₁ d₂ T hd hcov ξ x'
    hx'cusp hx'cont γ hγ e₁ e₂ he₁
  refine ⟨M, fun g hg => ?_⟩
  rw [hxeq, hfold]
  exact hM g hg
