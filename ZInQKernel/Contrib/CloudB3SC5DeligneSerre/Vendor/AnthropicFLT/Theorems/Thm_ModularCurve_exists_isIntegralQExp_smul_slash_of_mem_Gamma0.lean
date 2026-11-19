/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_exists_isIntegralQExp_smul_slash_of_mem_Gamma0 (git blob 75cf257834d5d1b020f4a6c9cc9d7475663cb041, sha256 686cd965d51067c39fff5061ff576c5e19e09352fe89288042afca5097988a12).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X1
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_exists_isIntegralQExp_smul_slash_of_mem_Gamma0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open scoped MatrixGroups ModularForm in

theorem ModularCurve.exists_isIntegralQExp_smul_slash_of_mem_Gamma0 (M : ℕ) [NeZero M] {k : ℤ}
    (f : ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) k)
    {p : PowerSeries ℤ} (hp : ModularCurve.IsIntegralQExp f p)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) :
    ∃ (D : ℤ) (f₁ : ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) k)
      (p₁ : PowerSeries ℤ), D ≠ 0 ∧ ModularCurve.IsIntegralQExp f₁ p₁ ∧
        (⇑f₁ : UpperHalfPlane → ℂ) = (D : ℂ) • ((⇑f : UpperHalfPlane → ℂ) ∣[k] γ) := by
  revert M k f p hp γ hγ
  exact @_root_.P2MW.S_ModularCurve_exists_isIntegralQExp_smul_slash_of_mem_Gamma0.solution
