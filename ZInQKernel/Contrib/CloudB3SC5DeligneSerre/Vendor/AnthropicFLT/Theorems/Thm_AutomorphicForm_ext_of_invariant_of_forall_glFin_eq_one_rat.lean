/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_ext_of_invariant_of_forall_glFin_eq_one_rat (git blob 559b0017c2421d928b885b5318c87389a9cd2a1c, sha256 62372ce22322cc9812e9d187db083e21f9e8f961154dced1a8c594dd9afe00c3).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_LanglandsTunnell_DeltaLift
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AdelicDock_LocalEmbedding
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_ext_of_invariant_of_forall_glFin_eq_one_rat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

theorem AutomorphicForm.ext_of_invariant_of_forall_glFin_eq_one_rat
    {M : Type*} {N : Ideal (NumberField.RingOfIntegers ℚ)} (hN : N ≠ ⊥)
    {Ψ₁ Ψ₂ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → M}
    (h₁ : ∀ (γ : GL (Fin 2) ℚ) (x : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ),
      Ψ₁ (AutomorphicForm.globalPoints (NumberField.RingOfIntegers ℚ) ℚ γ * x) = Ψ₁ x)
    (h₂ : ∀ (γ : GL (Fin 2) ℚ) (x : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ),
      Ψ₂ (AutomorphicForm.globalPoints (NumberField.RingOfIntegers ℚ) ℚ γ * x) = Ψ₂ x)
    (h₁' : ∀ u ∈ NumberField.AdelicLevel.finiteLevelOne (NumberField.RingOfIntegers ℚ) ℚ N,
      ∀ x, Ψ₁ (x * AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ u) = Ψ₁ x)
    (h₂' : ∀ u ∈ NumberField.AdelicLevel.finiteLevelOne (NumberField.RingOfIntegers ℚ) ℚ N,
      ∀ x, Ψ₂ (x * AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ u) = Ψ₂ x)
    (heq : ∀ h : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ,
      NumberField.AdelicLevel.glFin (NumberField.RingOfIntegers ℚ) ℚ h = 1 →
        LanglandsTunnell.ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ → Ψ₁ h = Ψ₂ h) :
    Ψ₁ = Ψ₂ := by
  revert M N hN Ψ₁ Ψ₂ h₁ h₂ h₁' h₂' heq
  exact @_root_.P2MW.S_AutomorphicForm_ext_of_invariant_of_forall_glFin_eq_one_rat.solution
