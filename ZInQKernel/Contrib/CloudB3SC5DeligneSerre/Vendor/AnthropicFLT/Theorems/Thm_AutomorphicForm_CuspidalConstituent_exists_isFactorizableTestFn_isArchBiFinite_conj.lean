/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_isFactorizableTestFn_isArchBiFinite_conj (git blob d75bd80c5cbeceb4d6335c7992ac94dfa63e7b1b, sha256 ccb0e0dd06ce30bd0759448482b144326195ade0b5f9d184230f0e46e7cf6cc0).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CuspidalConstituent
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_CuspidalConstituent_exists_isFactorizableTestFn_isArchBiFinite_conj

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.CuspidalConstituent.exists_isFactorizableTestFn_isArchBiFinite_conj
    (F : Type) [Field F] [NumberField F]
    (g : AdelicGL2 (𝓞 F) F) (hg : g ∈ finiteAdelicGL2Subgroup F)
    (k : AdelicGL2 (𝓞 F) F) (hk : k ∈ ⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (tys : ArchTypeFamily F)
    (hf : IsFactorizableTestFn F f) (hbf : IsArchBiFinite F tys f) :
    ∃ tys' : ArchTypeFamily F,
      IsFactorizableTestFn F (fun y => f ((g * k) * y * (g * k)⁻¹)) ∧
      IsArchBiFinite F tys' (fun y => f ((g * k) * y * (g * k)⁻¹)) := by
  revert F g hg k hk f tys hf hbf
  exact @_root_.P2MW.S_AutomorphicForm_CuspidalConstituent_exists_isFactorizableTestFn_isArchBiFinite_conj.solution
