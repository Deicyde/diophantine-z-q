/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AutomorphicForm_CuspidalConstituent_isArchSmoothAtComplex_and_continuous_foldr_archDerivAtComplex_of_mem_cut (git blob 73c917e527bbf651787715f8303d4723c16b5a72, sha256 265219061a25c09e4be4d817f13b61c50267d3ca74ce0118d59e93dc162b33ea).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CuspidalConstituent
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_FactorizableTestFn
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_RightConvolution
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_eq_rightConv_of_mem_cut
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_archDerivAtComplex_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_continuous_rightConv_and_contDiff_of_isFactorizableTestFn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AutomorphicForm_CuspidalConstituent_isArchSmoothAtComplex_and_continuous_foldr_archDerivAtComplex_of_mem_cut

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open AutomorphicForm.CuspidalConstituent

namespace E38SMOC

private theorem isFactorizableTestFn_leftDeriv (K : Type) [Field K] [NumberField K]
    {w : InfinitePlace K} (hw : w.IsComplex) (d : ArchDirComplex)
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

end E38SMOC

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
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (tys : AutomorphicForm.ArchTypeFamily K)
    (x : AdelicGL2 (𝓞 K) K → ℂ) (hx : x ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys)
    (w : InfinitePlace K) (hw : w.IsComplex) (l : List ArchDirComplex) :
    IsArchSmoothAtComplex hw (l.foldr (archDerivAtComplex hw) x) ∧ Continuous (l.foldr (archDerivAtComplex hw) x) := by
  classical
  obtain ⟨x', hx', α, hαf, -, -, hxeq⟩ :=
    AutomorphicForm.CuspidalConstituent.exists_eq_rightConv_of_mem_cut K c u d₁ d₂ T hc hd₁ hd hcov ξ V hV N hN tys x hx

  have hcont : Continuous x' := by
    have hxK : x' ∈ cuspKFiniteSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ξ := hV.1.le hx'.1.1
    refine Submodule.span_induction (p := fun φ _ => Continuous φ) ?_ ?_ ?_ ?_ hxK
    · rintro φ ⟨-, hφc, -⟩; exact hφc
    · exact continuous_zero
    · intro u v _ _ hu hv; exact hu.add hv
    · intro r u _ hu; exact hu.const_smul r
  subst hxeq

  suffices h : ∃ γ : AdelicGL2 (𝓞 K) K → ℂ, IsFactorizableTestFn K γ ∧
      l.foldr (archDerivAtComplex hw) (rightConv K x' α) = rightConv K x' γ by
    obtain ⟨γ, hγ, hfold⟩ := h
    rw [hfold]
    exact ⟨((AutomorphicForm.archDerivAtComplex_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn K hw ArchDirComplex.H).1
      x' γ hcont hγ).1, (AutomorphicForm.continuous_rightConv_and_contDiff_of_isFactorizableTestFn K x' hcont γ hγ).1⟩
  induction l with
  | nil => exact ⟨α, hαf, rfl⟩
  | cons d l ih =>
    obtain ⟨γ, hγ, hfold⟩ := ih
    refine ⟨fun y => deriv (fun t : ℝ => γ (archFlowAtComplex hw d (-t) * y)) 0,
      E38SMOC.isFactorizableTestFn_leftDeriv K hw d γ hγ, ?_⟩
    rw [List.foldr_cons, hfold]
    exact ((AutomorphicForm.archDerivAtComplex_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn K hw d).1 x' γ hcont hγ).2
