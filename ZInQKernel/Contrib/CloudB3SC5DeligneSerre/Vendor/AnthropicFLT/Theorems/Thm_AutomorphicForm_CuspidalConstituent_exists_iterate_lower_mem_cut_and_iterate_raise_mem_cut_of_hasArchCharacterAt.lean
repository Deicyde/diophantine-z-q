/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_iterate_lower_mem_cut_and_iterate_raise_mem_cut_of_hasArchCharacterAt (git blob cb890109124f22bbaa99378ef972593b46aa1dc3, sha256 9cf42aa93882cfac364a8b6ab3a90bbab5c0597eff5b3aeda511ca99e1a0aadb).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CuspidalConstituent
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ArchDerivCasimir
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_CuspidalConstituent_exists_iterate_lower_mem_cut_and_iterate_raise_mem_cut_of_hasArchCharacterAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.CuspidalConstituent.exists_iterate_lower_mem_cut_and_iterate_raise_mem_cut_of_hasArchCharacterAt
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
    (w : InfinitePlace K) (hw : w.IsReal)
    (y : AdelicGL2 (𝓞 K) K → ℂ)
    (hy : y ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys)
    (hpure : ∀ (v : InfinitePlace K) (hv : v.IsReal), ∃ m : ℤ, HasArchCharacterAt₀ K v (archWeightCharAt hv m) y)
    (n : ℤ) (hyn : HasArchCharacterAt₀ K w (archWeightCharAt hw n) y) :
    let lower : (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ) :=
      fun x => archDerivAt hw .H x - Complex.I • (archDerivAt hw .E x + archDerivAt hw .Fm x)
    let raise : (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ) :=
      fun x => archDerivAt hw .H x + Complex.I • (archDerivAt hw .E x + archDerivAt hw .Fm x)
    (∀ j : ℕ,
      (∃ tys' : AutomorphicForm.ArchTypeFamily K,
        lower^[j] y ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
          (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) N ⊓ archCutSubmodule K tys') ∧
      (∀ (v : InfinitePlace K) (hv : v.IsReal) (m : ℤ), v ≠ w →
        HasArchCharacterAt₀ K v (archWeightCharAt hv m) y → HasArchCharacterAt₀ K v (archWeightCharAt hv m) (lower^[j] y)) ∧
      HasArchCharacterAt₀ K w (archWeightCharAt hw (n - 2 * j)) (lower^[j] y)) ∧
    (∀ j : ℕ,
      (∃ tys' : AutomorphicForm.ArchTypeFamily K,
        raise^[j] y ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
          (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) N ⊓ archCutSubmodule K tys') ∧
      (∀ (v : InfinitePlace K) (hv : v.IsReal) (m : ℤ), v ≠ w →
        HasArchCharacterAt₀ K v (archWeightCharAt hv m) y → HasArchCharacterAt₀ K v (archWeightCharAt hv m) (raise^[j] y)) ∧
      HasArchCharacterAt₀ K w (archWeightCharAt hw (n + 2 * j)) (raise^[j] y)) := by
  revert K c u d₁ d₂ T hc hd₁ hd hcov ξ V hV N hN tys w hw y hy hpure n hyn
  exact @_root_.P2MW.S_AutomorphicForm_CuspidalConstituent_exists_iterate_lower_mem_cut_and_iterate_raise_mem_cut_of_hasArchCharacterAt.solution
