/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_exists_integral_rightConv_eq_rightConv (git blob 12e517302c900b5cf3cd1c024ae17d8e7e2bf226, sha256 df2fae13379084541469cca5605acb1919bc6ff6d3e1a35ca7fa67391937e499).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CuspidalConstituent
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_exists_integral_rightConv_eq_rightConv

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open MeasureTheory NumberField AutomorphicForm AutomorphicForm.CuspidalConstituent
open scoped BigOperators

theorem AutomorphicForm.exists_integral_rightConv_eq_rightConv
    (F : Type) [Field F] [NumberField F]
    (U : Subgroup (AdelicGL2 (𝓞 F) F)) (hU : IsCompact (U : Set (AdelicGL2 (𝓞 F) F)))
    (O : Subgroup (AdelicGL2 (𝓞 F) F)) (hO : IsOpen (O : Set (AdelicGL2 (𝓞 F) F)))
    (hUO : U = O ⊓ finiteAdelicGL2Subgroup F)
    [MeasurableSpace U] [BorelSpace U] (μ : Measure U) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
    (tys : ArchTypeFamily F)
    {y : AdelicGL2 (𝓞 F) F → ℂ} (hyc : Continuous y) (hyU : ∀ x : AdelicGL2 (𝓞 F) F, ∀ u ∈ U, y (x * u) = y x)
    {f : AdelicGL2 (𝓞 F) F → ℂ} (hf : IsFactorizableTestFn F f) (hbf : IsArchBiFinite F tys f) :
    ∃ f' : AdelicGL2 (𝓞 F) F → ℂ, IsFactorizableTestFn F f' ∧ IsArchBiFinite F tys f' ∧
      (∀ x : AdelicGL2 (𝓞 F) F, ∀ u ∈ U, f' (u * x) = f' x ∧ f' (x * u) = f' x) ∧
      ∀ x : AdelicGL2 (𝓞 F) F, ∫ u, rightConv F y f (x * (u : AdelicGL2 (𝓞 F) F)) ∂μ = rightConv F y f' x := by
  revert F U hU O hO hUO μ tys y hyc hyU f hf hbf
  exact @_root_.P2MW.S_AutomorphicForm_exists_integral_rightConv_eq_rightConv.solution
