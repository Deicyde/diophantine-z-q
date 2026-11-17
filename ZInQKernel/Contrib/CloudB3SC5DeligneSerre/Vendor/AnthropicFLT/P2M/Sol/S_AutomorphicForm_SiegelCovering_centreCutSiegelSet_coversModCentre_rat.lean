/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AutomorphicForm_SiegelCovering_centreCutSiegelSet_coversModCentre_rat (git blob fb8d0ab3dd9e52bfecf48daabfb9871a24dc43de, sha256 69f467470fb7c5b524923ff6952d1c693426bed1ceb6eaa0b267e79d38a5d1da).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_SiegelCovering
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_NumberField_AdelicLevel_exists_globalPoints_mul_mem_finiteIntegralGL2_rat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AutomorphicForm_SiegelCovering_centreCutSiegelSet_coversModCentre_rat

set_option autoImplicit false

namespace M4aP1R

namespace SiegelCovering

theorem centreCutSiegelSet_coversModCentre_rat_impl {c u d₁ d₂ : ℝ}
    (hc : c ≤ Real.sqrt 3 / 2) (hu : 1 / 2 ≤ u) (hd₂ : 0 < d₂) (hd : d₁ ≤ d₂) :
    AutomorphicForm.SiegelCovering.CoversModCentre ℚ
      (AutomorphicForm.WindowedSiegel.centreCutSiegelSet ℚ c u d₁ d₂) :=
  AutomorphicForm.SiegelCovering.coversModCentre_centreCutSiegelSet_rat
    (fun g => NumberField.AdelicLevel.exists_globalPoints_mul_mem_finiteIntegralGL2_rat g) hc hu hd₂ hd

end SiegelCovering

end M4aP1R

#print axioms M4aP1R.SiegelCovering.centreCutSiegelSet_coversModCentre_rat_impl

theorem solution {c u d₁ d₂ : ℝ}
    (hc : c ≤ Real.sqrt 3 / 2) (hu : 1 / 2 ≤ u) (hd₂ : 0 < d₂) (hd : d₁ ≤ d₂) :
    AutomorphicForm.SiegelCovering.CoversModCentre ℚ
      (AutomorphicForm.WindowedSiegel.centreCutSiegelSet ℚ c u d₁ d₂) := by
  exact M4aP1R.SiegelCovering.centreCutSiegelSet_coversModCentre_rat_impl hc hu hd₂ hd
