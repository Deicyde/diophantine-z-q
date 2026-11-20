/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_exists_basis_periodLatticeOf_linearIndependent_real_span_eq_top_of_isCongruenceSubgroup (git blob 31655f0560810521db0bcd23ce39e24d54ed8446, sha256 7d96e8a482d5adc22f0ff8e0f97816fc6ae0f05e28ea39c754165011f4c6c47c).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PeriodOf
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_exists_basis_periodLatticeOf_linearIndependent_real_span_eq_top_of_isCongruenceSubgroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.exists_basis_periodLatticeOf_linearIndependent_real_span_eq_top_of_isCongruenceSubgroup
    (Γ : Subgroup SL(2, ℤ)) (hΓ : CongruenceSubgroup.IsCongruenceSubgroup Γ) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℤ (ModularCurve.periodLatticeOf Γ)),
      LinearIndependent ℝ (fun i => ((b i : ModularCurve.periodLatticeOf Γ) :
          Module.Dual ℂ (CuspForm Γ 2))) ∧
        Submodule.span ℝ (Set.range fun i => ((b i : ModularCurve.periodLatticeOf Γ) :
          Module.Dual ℂ (CuspForm Γ 2))) = ⊤ := by
  revert Γ hΓ
  exact @_root_.P2MW.S_ModularCurve_exists_basis_periodLatticeOf_linearIndependent_real_span_eq_top_of_isCongruenceSubgroup.solution
