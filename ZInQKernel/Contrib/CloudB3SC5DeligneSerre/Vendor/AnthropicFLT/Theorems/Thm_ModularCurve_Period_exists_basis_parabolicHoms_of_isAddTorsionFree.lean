/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_Period_exists_basis_parabolicHoms_of_isAddTorsionFree (git blob 2278cab87f1f31c7d07fd5ac7d926daa68d3fb57, sha256 77236bc5fdb25a81aa122cd86d32096e613028b447716765df09e3478b951bb9).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PeriodMap
import Mathlib.LinearAlgebra.Basis.Defs
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_Period_exists_basis_parabolicHoms_of_isAddTorsionFree

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.Period.exists_basis_parabolicHoms_of_isAddTorsionFree
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℤ (ModularCurve.Period.parabolicHoms ℤ Γ ℤ)),
      ∀ (R : Type*) [CommRing R] [IsAddTorsionFree R],
        ∃ bR : Module.Basis (Fin n) R (ModularCurve.Period.parabolicHoms R Γ R),
          ∀ i, (bR i : Additive Γ →+ R) = (Int.castAddHom R).comp (b i : Additive Γ →+ ℤ) := by
  revert Γ
  exact @_root_.P2MW.S_ModularCurve_Period_exists_basis_parabolicHoms_of_isAddTorsionFree.solution
