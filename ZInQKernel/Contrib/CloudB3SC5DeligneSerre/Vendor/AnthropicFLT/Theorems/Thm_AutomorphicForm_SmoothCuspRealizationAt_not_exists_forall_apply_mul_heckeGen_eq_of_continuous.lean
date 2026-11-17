/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_SmoothCuspRealizationAt_not_exists_forall_apply_mul_heckeGen_eq_of_continuous (git blob 5a1f2e432e90fecd6dfb0ccf7209afec13e14560, sha256 c0d37f6e2769ee66f59803a0bbc61861c1803af02e02964e3f7bfa62c9c8224c).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_SmoothCuspRealizationAt_not_exists_forall_apply_mul_heckeGen_eq_of_continuous

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

theorem AutomorphicForm.SmoothCuspRealizationAt.not_exists_forall_apply_mul_heckeGen_eq_of_continuous
    (Ψ : AutomorphicForm.HeckeEigensystem ℚ ℂ)
    (R : AutomorphicForm.SmoothCuspRealizationAt ℚ (AutomorphicForm.productionPinsGeneral ℚ) Ψ)
    (hR : AutomorphicForm.IsGenuineCuspRealizationAt ℚ (AutomorphicForm.productionPinsGeneral ℚ) Ψ R)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (hv : ¬ v.asIdeal ∣ Ψ.level) :
    ¬ ∃ c : ℂ, ∀ g : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ,
      R.toFun (g * NumberField.AdelicLevel.heckeGen (NumberField.RingOfIntegers ℚ) ℚ v) = c * R.toFun g := by
  revert Ψ R hR v hv
  exact @_root_.P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_not_exists_forall_apply_mul_heckeGen_eq_of_continuous.solution
