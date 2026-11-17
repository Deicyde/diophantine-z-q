/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_Period_exists_basis_parabolicHoms_castAddHom_comp (git blob 7342c3eea53985d69bae0c31d587b82e2c04b077, sha256 0670bd8fe998a4370018d545e228054fb13354bbde313ba9397d9439c29114e1).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PeriodMap
import Mathlib.LinearAlgebra.Basis.Defs
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_Period_exists_basis_parabolicHoms_castAddHom_comp

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.Period.exists_basis_parabolicHoms_castAddHom_comp
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℤ (ModularCurve.Period.parabolicHoms ℤ Γ ℤ)),
      ∀ (K : Type*) [Field K] [CharZero K],
        ∃ bK : Module.Basis (Fin n) K (ModularCurve.Period.parabolicHoms K Γ K),
          ∀ i, (bK i : Additive Γ →+ K) = (Int.castAddHom K).comp (b i : Additive Γ →+ ℤ) := by
  revert Γ
  exact @_root_.P2MW.S_ModularCurve_Period_exists_basis_parabolicHoms_castAddHom_comp.solution
