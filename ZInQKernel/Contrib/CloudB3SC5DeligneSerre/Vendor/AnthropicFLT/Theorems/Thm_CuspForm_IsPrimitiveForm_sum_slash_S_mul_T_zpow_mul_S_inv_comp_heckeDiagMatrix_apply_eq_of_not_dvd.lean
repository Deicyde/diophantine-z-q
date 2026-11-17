/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_CuspForm_IsPrimitiveForm_sum_slash_S_mul_T_zpow_mul_S_inv_comp_heckeDiagMatrix_apply_eq_of_not_dvd (git blob 674f56a2873327ab484df6e7e08040574d1b297a, sha256 e5e554ec4dbdbc71845771ddbe2ca47a12e81c0a855de5310e2eeac43d288eb9).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularForm_HeckeOperator
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CuspForm_PrimitiveFormGamma1
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_CuspForm_IsPrimitiveForm_sum_slash_S_mul_T_zpow_mul_S_inv_comp_heckeDiagMatrix_apply_eq_of_not_dvd

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open scoped MatrixGroups ModularForm in

theorem CuspForm.IsPrimitiveForm.sum_slash_S_mul_T_zpow_mul_S_inv_comp_heckeDiagMatrix_apply_eq_of_not_dvd
    (M : ℕ) [NeZero M] (k : ℤ) (ε : DirichletCharacter ℂ M)
    (g : CuspForm (CongruenceSubgroup.Gamma1 M) k) (hg : CuspForm.IsPrimitiveForm ε g)
    {q : ℕ} (hq : q.Prime) (hqM : ¬ q ∣ M) (τ : UpperHalfPlane) :
    ∑ j ∈ Finset.range q,
        ((fun σ : UpperHalfPlane => g (ModularForm.heckeDiagMatrix q • σ)) ∣[k]
          (ModularGroup.S * ModularGroup.T ^ ((j : ℤ) * M) * ModularGroup.S⁻¹ : SL(2, ℤ))) τ
      = (q : ℂ) ^ (1 - k) * starRingEnd ℂ (ModularFormClass.qCoeff g q) * g τ
          - starRingEnd ℂ (ε (q : ZMod M)) * (q : ℂ) ^ (-k) *
              g (ModularForm.heckeMatrix q 0 • τ) := by
  revert M k ε g hg q hq hqM τ
  exact @_root_.P2MW.S_CuspForm_IsPrimitiveForm_sum_slash_S_mul_T_zpow_mul_S_inv_comp_heckeDiagMatrix_apply_eq_of_not_dvd.solution
