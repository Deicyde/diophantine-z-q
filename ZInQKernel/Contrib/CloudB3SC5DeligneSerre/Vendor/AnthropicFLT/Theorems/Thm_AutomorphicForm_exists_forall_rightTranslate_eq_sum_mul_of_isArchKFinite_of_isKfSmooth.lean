/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_exists_forall_rightTranslate_eq_sum_mul_of_isArchKFinite_of_isKfSmooth (git blob 50c625bd8bde1fbde28944ca200b787c309ff28a, sha256 055eb105a38cceadd70de2d791f08a9617a2c2e1fa9e2ec58aed0006e44c75a7).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ArchKFinite
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_exists_forall_rightTranslate_eq_sum_mul_of_isArchKFinite_of_isKfSmooth

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open NumberField NumberField.AdelicLevel AutomorphicForm AutomorphicForm.WindowedSiegel

theorem AutomorphicForm.exists_forall_rightTranslate_eq_sum_mul_of_isArchKFinite_of_isKfSmooth
    (F : Type) [Field F] [NumberField F] (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (_hφK : IsArchKFinite F φ) (_hφf : IsKfSmooth F φ) (_hφc : Continuous φ) :
    ∃ (m : ℕ) (e : Fin m → AdelicGL2 (𝓞 F) F → ℂ) (a : Fin m → AdelicGL2 (𝓞 F) F → ℂ),
      (∀ j, (∃ (n : ℕ) (c : Fin n → ℂ) (k : Fin n → AdelicGL2 (𝓞 F) F),
          (∀ i, glFin (𝓞 F) F (k i) ∈ finiteIntegralGL2 (𝓞 F) F ∧
            ∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F (k i)))) ∧
          e j = fun x => ∑ i, c i * φ (x * k i)) ∧
        IsArchKFinite F (e j) ∧ IsKfSmooth F (e j)) ∧
      (∀ j, ContinuousOn (a j) {k | glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F ∧
          ∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))}) ∧
      ∀ k : AdelicGL2 (𝓞 F) F, glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
        (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) →
        ∀ x : AdelicGL2 (𝓞 F) F, φ (x * k) = ∑ j, a j k * e j x := by
  revert F φ _hφK _hφf _hφc
  exact @_root_.P2MW.S_AutomorphicForm_exists_forall_rightTranslate_eq_sum_mul_of_isArchKFinite_of_isKfSmooth.solution
