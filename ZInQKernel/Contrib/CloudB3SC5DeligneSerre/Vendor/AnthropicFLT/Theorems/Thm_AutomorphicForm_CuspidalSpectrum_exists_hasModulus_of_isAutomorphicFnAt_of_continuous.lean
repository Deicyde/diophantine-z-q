/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_hasModulus_of_isAutomorphicFnAt_of_continuous (git blob 16aa625bcdf39cac93200e7d581605c94308570d, sha256 82407cf796d6288d53e1ce4d21ec03644df971cb75d7685f861d855daa1dc770).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_CuspidalSpectrum_exists_hasModulus_of_isAutomorphicFnAt_of_continuous

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate ENNReal InnerProductSpace BigOperators

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.CuspidalSpectrum.exists_hasModulus_of_isAutomorphicFnAt_of_continuous
    (F : Type) [Field F] [NumberField F] (D : Set (AdelicGL2 (𝓞 F) F))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : IsAutomorphicFnAt F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ φ)
    (hφc : Continuous φ) (hφ0 : φ ≠ 0) :
    ∃ σ : ℝ, HasModulus F ξ σ := by
  revert F D ξ φ hφ hφc hφ0
  exact @_root_.P2MW.S_AutomorphicForm_CuspidalSpectrum_exists_hasModulus_of_isAutomorphicFnAt_of_continuous.solution
