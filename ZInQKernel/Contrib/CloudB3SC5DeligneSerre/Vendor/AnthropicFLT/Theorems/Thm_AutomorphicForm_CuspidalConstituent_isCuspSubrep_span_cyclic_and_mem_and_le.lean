/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_CuspidalConstituent_isCuspSubrep_span_cyclic_and_mem_and_le (git blob 4bd851e6b0a609c653fc9f82dba9c17431b3e8d3, sha256 e3c469c1d3b1ff64c6aba97b06fe88636c16c01f0b5dc52d2e655c254a7102ae).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CuspidalConstituent
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_CuspidalConstituent_isCuspSubrep_span_cyclic_and_mem_and_le

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.CuspidalConstituent.isCuspSubrep_span_cyclic_and_mem_and_le
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F) (B : Set (AdeleRing (𝓞 F) F))
    (ξ : (productionPinsOf F D U gen B).Z →* ℂˣ)
    (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) (hV : IsCuspSubrep F (productionPinsOf F D U gen B) ξ V)
    (Ψ : AdelicGL2 (𝓞 F) F → ℂ) (hΨ : Ψ ∈ V) :
    let C : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) := Submodule.span ℂ
      {φ | ∃ g ∈ finiteAdelicGL2Subgroup F, ∃ k ∈ (⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range),
        φ = rightTranslate F (g * k) Ψ ∨
        ∃ (f : AdelicGL2 (𝓞 F) F → ℂ) (tys : ArchTypeFamily F), IsFactorizableTestFn F f ∧ IsArchBiFinite F tys f ∧
          φ = rightTranslate F (g * k) (rightConv F Ψ f)}
    IsCuspSubrep F (productionPinsOf F D U gen B) ξ C ∧ Ψ ∈ C ∧ C ≤ V ∧
      (IsCuspConstituent F (productionPinsOf F D U gen B) ξ V → Ψ ≠ 0 → C = V) := by
  revert F D U gen B ξ V hV Ψ hΨ
  exact @_root_.P2MW.S_AutomorphicForm_CuspidalConstituent_isCuspSubrep_span_cyclic_and_mem_and_le.solution
