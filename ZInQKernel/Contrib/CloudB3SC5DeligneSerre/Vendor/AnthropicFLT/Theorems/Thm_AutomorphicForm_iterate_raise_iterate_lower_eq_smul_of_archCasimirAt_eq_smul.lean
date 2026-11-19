/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_iterate_raise_iterate_lower_eq_smul_of_archCasimirAt_eq_smul (git blob 5f2cc0c07f956be9407fe37434a3c6bd36405024, sha256 ad4f81f2f1f8f17b9e01e7c2d5b3b701924a702af5221519114283d5e65e72a3).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CuspidalConstituent
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ArchDerivCasimir
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_FactorizableTestFn
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_RightConvolution
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_iterate_raise_iterate_lower_eq_smul_of_archCasimirAt_eq_smul

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.iterate_raise_iterate_lower_eq_smul_of_archCasimirAt_eq_smul
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsReal)
    (θ : AdelicGL2 (𝓞 K) K → ℂ) (hθ : IsArchSmoothAt hw θ) (m lam : ℂ)
    (hm : archDerivAt hw .E θ - archDerivAt hw .Fm θ = m • θ)
    (hΩ : archCasimirAt hw θ = lam • θ) :
    let lower : (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ) :=
      fun x => archDerivAt hw .H x - Complex.I • (archDerivAt hw .E x + archDerivAt hw .Fm x)
    let raise : (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ) :=
      fun x => archDerivAt hw .H x + Complex.I • (archDerivAt hw .E x + archDerivAt hw .Fm x)
    (∀ j : ℕ, IsArchSmoothAt hw (lower^[j] θ) ∧
      archDerivAt hw .E (lower^[j] θ) - archDerivAt hw .Fm (lower^[j] θ) = (m - 2 * Complex.I * j) • lower^[j] θ ∧
      archCasimirAt hw (lower^[j] θ) = lam • lower^[j] θ) ∧
    (∀ j : ℕ, IsArchSmoothAt hw (raise^[j] θ) ∧
      archDerivAt hw .E (raise^[j] θ) - archDerivAt hw .Fm (raise^[j] θ) = (m + 2 * Complex.I * j) • raise^[j] θ ∧
      archCasimirAt hw (raise^[j] θ) = lam • raise^[j] θ) ∧
    (∀ M : ℕ, raise^[M] (lower^[M] θ) =
      (∏ j ∈ Finset.range M, (-4 * lam + (m - 2 * Complex.I * j) ^ 2 - 2 * Complex.I * (m - 2 * Complex.I * j))) • θ) ∧
    (∀ M : ℕ, lower^[M] (raise^[M] θ) =
      (∏ j ∈ Finset.range M, (-4 * lam + (m + 2 * Complex.I * j) ^ 2 + 2 * Complex.I * (m + 2 * Complex.I * j))) • θ) := by
  revert K w hw θ hθ m lam hm hΩ
  exact @_root_.P2MW.S_AutomorphicForm_iterate_raise_iterate_lower_eq_smul_of_archCasimirAt_eq_smul.solution
