/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_forall_norm_archDerivAt_le_of_mem_cut_of_forall_hasArchCharacterAt (git blob 4cccc29e6320fcbdaa80434d7c48a33bc5336941, sha256 1a30b89a1f6fc92440010d519e5e1c02a7948339998c0ecfa11ecc0c685a6569).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CuspidalConstituent
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ArchDerivCasimir
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_TateGlobalZeta
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_CuspidalConstituent_exists_forall_norm_archDerivAt_le_of_mem_cut_of_forall_hasArchCharacterAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.CuspidalConstituent.exists_forall_norm_archDerivAt_le_of_mem_cut_of_forall_hasArchCharacterAt
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
    (w : InfinitePlace K) (hw : w.IsReal)
    (y : AdelicGL2 (𝓞 K) K → ℂ)
    (hy : y ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys)
    (hpure : ∀ (v : InfinitePlace K) (hv : v.IsReal), ∃ m : ℤ, HasArchCharacterAt₀ K v (archWeightCharAt hv m) y)
    (n : ℤ) (hyn : HasArchCharacterAt₀ K w (archWeightCharAt hw n) y)
    (e₁ e₂ : ℝ) (he₁ : 0 < e₁) (he : e₁ < e₂) :
    ∃ B : ℝ, ∀ g : AdelicGL2 (𝓞 K) K,
      NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂ →
      ‖y g‖ ≤ B ∧ (∀ d : ArchDir, ‖archDerivAt hw d y g‖ ≤ B) ∧
        (∀ d d' : ArchDir, ‖archDerivAt hw d (archDerivAt hw d' y) g‖ ≤ B) := by
  revert K c u d₁ d₂ T hc hd₁ hd hcov ξ V hV w₀ hξ N hN tys w hw y hy hpure n hyn e₁ e₂ he₁ he
  exact @_root_.P2MW.S_AutomorphicForm_CuspidalConstituent_exists_forall_norm_archDerivAt_le_of_mem_cut_of_forall_hasArchCharacterAt.solution
