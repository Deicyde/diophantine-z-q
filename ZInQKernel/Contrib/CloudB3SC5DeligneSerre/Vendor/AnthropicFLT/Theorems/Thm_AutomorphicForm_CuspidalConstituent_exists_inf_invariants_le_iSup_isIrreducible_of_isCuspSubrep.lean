/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_inf_invariants_le_iSup_isIrreducible_of_isCuspSubrep (git blob 2c8882770f3057def28ae5188e879dd436fcc86b, sha256 93dc307c068b1d60c9f6d8bca5e1839d96b1bf85316a5c7415697cc6b3173c45).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_FactorizableTestFn
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_CuspidalConstituent_exists_inf_invariants_le_iSup_isIrreducible_of_isCuspSubrep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate ENNReal InnerProductSpace

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.CuspidalConstituent.exists_inf_invariants_le_iSup_isIrreducible_of_isCuspSubrep
    (F : Type) [Field F] [NumberField F]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (U : Subgroup (AdelicGL2 (𝓞 F) F)) (hU : IsCompact (U : Set (AdelicGL2 (𝓞 F) F)))
    (O : Subgroup (AdelicGL2 (𝓞 F) F)) (hO : IsOpen (O : Set (AdelicGL2 (𝓞 F) F)))
    (hUO : U = O ⊓ finiteAdelicGL2Subgroup F)
    (tys : AutomorphicForm.ArchTypeFamily F)
    (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) (hV : IsCuspSubrep F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ V) :
    ∃ (n : ℕ) (τs : Fin n → ∀ w : InfinitePlace F, ArchRepAt F w),
      (∀ j w, (τs j w).ρ.IsIrreducible) ∧
      V ⊓ Representation.invariants ((rightRegular F).comp U.subtype) ⊓ archCutSubmodule F tys ≤
        ⨆ j : Fin n, V ⊓ Representation.invariants ((rightRegular F).comp U.subtype) ⊓ archCutSubmodule F (⟨fun _ => 1, fun w _ => τs j w⟩ : AutomorphicForm.ArchTypeFamily F) := by
  revert F c u d₁ d₂ T ξ U hU O hO hUO tys V hV
  exact @_root_.P2MW.S_AutomorphicForm_CuspidalConstituent_exists_inf_invariants_le_iSup_isIrreducible_of_isCuspSubrep.solution
