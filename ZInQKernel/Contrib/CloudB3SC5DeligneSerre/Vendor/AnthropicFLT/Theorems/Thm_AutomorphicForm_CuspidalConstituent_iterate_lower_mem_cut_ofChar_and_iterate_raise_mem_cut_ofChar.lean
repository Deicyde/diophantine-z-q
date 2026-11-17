/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_CuspidalConstituent_iterate_lower_mem_cut_ofChar_and_iterate_raise_mem_cut_ofChar (git blob 6a096cd551d0b654c853a244ee692cfe074a8dbe, sha256 05c3682e61256da495fb58598c12a7563b12d1542c13e423004aa668797b5623).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CuspidalConstituent
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ArchDerivCasimir
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_CuspidalConstituent_iterate_lower_mem_cut_ofChar_and_iterate_raise_mem_cut_ofChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.CuspidalConstituent.iterate_lower_mem_cut_ofChar_and_iterate_raise_mem_cut_ofChar
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
    (hreal : ∀ v : InfinitePlace K, v.IsReal)
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (χ : ∀ v : InfinitePlace K, rowIsometrySubgroup₀ v.Completion →* ℂˣ)
    (w : InfinitePlace K) (hw : w.IsReal) (n : ℤ) (hχ : χ w = archWeightCharAt hw n)
    (χ' : ℤ → ∀ v : InfinitePlace K, rowIsometrySubgroup₀ v.Completion →* ℂˣ)
    (hχ' : ∀ (m : ℤ) (v : InfinitePlace K), v ≠ w → χ' m v = χ v)
    (hχ'w : ∀ m : ℤ, χ' m w = archWeightCharAt hw m)
    (y : AdelicGL2 (𝓞 K) K → ℂ)
    (hy : y ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K (ArchTypeFamily.ofChar K χ)) :
    let lower : (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ) :=
      fun x => archDerivAt hw .H x - Complex.I • (archDerivAt hw .E x + archDerivAt hw .Fm x)
    let raise : (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ) :=
      fun x => archDerivAt hw .H x + Complex.I • (archDerivAt hw .E x + archDerivAt hw .Fm x)
    (∀ j : ℕ, lower^[j] y ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K (ArchTypeFamily.ofChar K (χ' (n - 2 * j)))) ∧
    (∀ j : ℕ, raise^[j] y ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K (ArchTypeFamily.ofChar K (χ' (n + 2 * j)))) := by
  revert K c u d₁ d₂ T hc hd₁ hd hcov ξ V hV hreal N hN χ w hw n hχ χ' hχ' hχ'w y hy
  exact @_root_.P2MW.S_AutomorphicForm_CuspidalConstituent_iterate_lower_mem_cut_ofChar_and_iterate_raise_mem_cut_ofChar.solution
