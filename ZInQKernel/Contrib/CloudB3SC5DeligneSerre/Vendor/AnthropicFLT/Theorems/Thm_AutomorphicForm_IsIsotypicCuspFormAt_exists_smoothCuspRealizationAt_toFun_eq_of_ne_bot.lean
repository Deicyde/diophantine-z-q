/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_IsIsotypicCuspFormAt_exists_smoothCuspRealizationAt_toFun_eq_of_ne_bot (git blob a87d9ca1832473e79f9997a4d2822a5a58a70336, sha256 d363ba8765345c3e6df6f3de32d83793e5b3d6cfb91c31236a30aa4416375e8e).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CuspidalConstituent
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_IsIsotypicCuspFormAt_exists_smoothCuspRealizationAt_toFun_eq_of_ne_bot

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open MeasureTheory NumberField
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

theorem AutomorphicForm.IsIsotypicCuspFormAt.exists_smoothCuspRealizationAt_toFun_eq_of_ne_bot
    (F : Type) [Field F] [NumberField F] (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ)
    (N : Ideal (𝓞 F)) (hN : N ≠ ⊥) (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
    (Ψ : HeckeEigensystem F ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (h : IsIsotypicCuspFormAt F pins ξ N S Ψ φ) (h0 : φ ≠ 0) :
    ∃ (Ψ' : HeckeEigensystem F ℂ) (R : SmoothCuspRealizationAt F pins Ψ'.toRawCentral),
      Ψ'.level = N ∧ (∀ v, Ψ'.a v = Ψ.a v) ∧ (∀ v, Ψ'.b v = Ψ.b v) ∧
        R.toFun = φ ∧ R.centralChar = ξ ∧ R.exceptionalSet = S := by
  revert F pins ξ N hN S Ψ φ h h0
  exact @_root_.P2MW.S_AutomorphicForm_IsIsotypicCuspFormAt_exists_smoothCuspRealizationAt_toFun_eq_of_ne_bot.solution
