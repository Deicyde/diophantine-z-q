/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_exists_isIntegralQExp_smul_atkinLehnerSlash_of_even (git blob 9d9db0529e669eeb6fbd4ca7eabb6caf421763cc, sha256 51b579fed641599023a8839cb3f4dee47f0e516e832add6e20074aca2e189f18).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X1
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularForm_HeckeOperator
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_exists_isIntegralQExp_smul_atkinLehnerSlash_of_even

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open scoped MatrixGroups ModularForm in

theorem ModularCurve.exists_isIntegralQExp_smul_atkinLehnerSlash_of_even (M ℓ : ℕ) [NeZero M]
    [NeZero ℓ] {k : ℤ} (hk : Even k)
    (f : ModularForm ((CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 (M * ℓ) :
      Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k)
    {p : PowerSeries ℤ} (hp : ModularCurve.IsIntegralQExp f p)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) (hγℓ : (ℓ : ℤ) ∣ γ 1 1) :
    ∃ (D : ℤ) (p₁ : PowerSeries ℤ), D ≠ 0 ∧
      ModularCurve.IsIntegralQExp
        ((D : ℂ) • fun τ : UpperHalfPlane =>
          ((⇑f : UpperHalfPlane → ℂ) ∣[k] γ) (ModularForm.heckeDiagMatrix ℓ • τ)) p₁ := by
  revert M ℓ k hk f p hp γ hγ hγℓ
  exact @_root_.P2MW.S_ModularCurve_exists_isIntegralQExp_smul_atkinLehnerSlash_of_even.solution
