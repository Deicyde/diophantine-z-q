/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_eq_sum_su2String_highestWeight_of_mem_cut_of_isComplex (git blob d4b10b2f987d8a792fb575bbd4c012b6f201aa2d, sha256 cf5ba73c744dc280e66960a1d4e507e461f67d93aa4f2380b769d565e6fc1fff).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CuspidalConstituent
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_WhittakerCoefficient
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicTraceFin
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_TateGlobalZeta
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_CuspidalConstituent_exists_eq_sum_su2String_highestWeight_of_mem_cut_of_isComplex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.CuspidalConstituent.exists_eq_sum_su2String_highestWeight_of_mem_cut_of_isComplex

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
    (hX : V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys ≠ ⊥)
    (w : InfinitePlace K) (hw : w.IsComplex)
    (y : AdelicGL2 (𝓞 K) K → ℂ) (hy : y ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys)
    (w₀ : ℝ)
    (hξ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w₀)
    (lam lam' : ℂ)
    (hlam : ∀ x ∈ V, IsArchSmoothAtComplex hw x ∧ (∀ d : ArchDirComplex, Continuous (archDerivAtComplex hw d x)) ∧
      (∀ d d' : ArchDirComplex, Continuous (archDerivAtComplex hw d (archDerivAtComplex hw d' x))) ∧
      archCasimirAtComplex hw x = lam • x ∧ archCasimirBarAtComplex hw x = lam' • x) :
    ∃ (m : ℕ) (n : Fin m → ℕ) (x : (s : Fin m) → Fin (n s + 1) → (AdelicGL2 (𝓞 K) K → ℂ))
      (coef : (s : Fin m) → Fin (n s + 1) → ℂ)
      (E₁ E₂ : (s : Fin m) → ℝ → Matrix (Fin (n s + 1)) (Fin (n s + 1)) ℂ),
      y = ∑ s : Fin m, ∑ p : Fin (n s + 1), coef s p • x s p ∧
      ∀ s : Fin m,
        (∀ p, x s p ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys) ∧
        (x s 0 ≠ 0) ∧
        (n s = 0 → HasArchCharacterAt₀ K w 1 (x s 0)) ∧
        (archDerivAtComplex hw .iH (x s 0) = (Complex.I * (n s : ℂ)) • x s 0) ∧
        (archDerivAtComplex hw .Fm (x s 0) - archDerivAtComplex hw .E (x s 0)
          + Complex.I • (archDerivAtComplex hw .iE (x s 0) + archDerivAtComplex hw .iFm (x s 0)) = 0) ∧
        (∀ p, Continuous (x s p)) ∧
        (∀ p (γ : GL (Fin 2) K) (g' : AdelicGL2 (𝓞 K) K), x s p (globalPoints (𝓞 K) K γ * g') = x s p g') ∧
        (∀ p (z : (AdeleRing (𝓞 K) K)ˣ) (g' : AdelicGL2 (𝓞 K) K),
          x s p (centralScalar (𝓞 K) K z * g') = ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * x s p g') ∧
        (∀ p (l : List ArchDirComplex),
      IsArchSmoothAtComplex hw (l.foldr (archDerivAtComplex hw) (x s p)) ∧ Continuous (l.foldr (archDerivAtComplex hw) (x s p))) ∧
        (∀ p : Fin (n s + 1), HasCircleWeightAt hw ((n s : ℤ) - 2 * (p : ℕ)) (x s p)) ∧
        (E₁ s 0 = 1) ∧
        (E₂ s 0 = 1) ∧
        (∀ i j : Fin (n s + 1), HasDerivAt (fun r : ℝ => E₁ s r i j)
          (if (i : ℕ) = j + 1 then 1 else if (j : ℕ) = i + 1 then -((j : ℂ) * ((n s : ℂ) + 1 - j)) else 0) 0) ∧
        (∀ i j : Fin (n s + 1), HasDerivAt (fun r : ℝ => E₂ s r i j)
          (if (i : ℕ) = j + 1 then Complex.I else if (j : ℕ) = i + 1 then Complex.I * ((j : ℂ) * ((n s : ℂ) + 1 - j)) else 0) 0) ∧
        (∀ (p : Fin (n s + 1)) (r : ℝ) (g' : AdelicGL2 (𝓞 K) K),
          x s p (g' * archComplexLiftAt hw !![(Real.cos r : ℂ), -(Real.sin r : ℂ); (Real.sin r : ℂ), (Real.cos r : ℂ)]) = ∑ p' : Fin (n s + 1), E₁ s r p' p * x s p' g') ∧
        (∀ (p : Fin (n s + 1)) (r : ℝ) (g' : AdelicGL2 (𝓞 K) K),
          x s p (g' * archComplexLiftAt hw !![(Real.cos r : ℂ), (Real.sin r : ℂ) * Complex.I; (Real.sin r : ℂ) * Complex.I, (Real.cos r : ℂ)]) = ∑ p' : Fin (n s + 1), E₂ s r p' p * x s p' g') ∧
        (∀ p, archCasimirAtComplex hw (x s p) = lam • x s p ∧ archCasimirBarAtComplex hw (x s p) = lam' • x s p) ∧
        (∀ p, ∃ C₀ : ℝ, ∀ g' : AdelicGL2 (𝓞 K) K,
      ‖whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (x s p) 1 g'‖ ≤ C₀ * NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g') ^ (w₀ / 2)) := by
  revert K c u d₁ d₂ T hc hd₁ hd hcov ξ V hV N hN tys hX w hw y hy w₀ hξ lam lam' hlam
  exact @_root_.P2MW.S_AutomorphicForm_CuspidalConstituent_exists_eq_sum_su2String_highestWeight_of_mem_cut_of_isComplex.solution
