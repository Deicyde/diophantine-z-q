/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_CuspForm_norm_sq_lt_of_hasNebentypus_qCoeff_hecke_eigen (git blob 53bc5b93db7378f8ba4ba51f25c299e4154c5694, sha256 c8f5e4c40184ee111f6ab5725b371f49b48f38ddd44e10b0e5c0e1644c15db8b).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_FLTPrelim_Modularity
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CuspForm_PrimitiveFormGamma1
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_CuspForm_norm_sq_lt_of_hasNebentypus_qCoeff_hecke_eigen

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups

theorem CuspForm.norm_sq_lt_of_hasNebentypus_qCoeff_hecke_eigen
    (M : ℕ) [NeZero M] (k : ℤ) (ε : DirichletCharacter ℂ M) (g : CuspForm (Gamma1 M) k)
    (hg0 : g ≠ 0) (hg : CuspForm.HasNebentypus ε g) {p : ℕ} (hp : p.Prime) (hpM : ¬ p ∣ M) (a : ℂ)
    (ha : ∀ n : ℕ, ModularFormClass.qCoeff g (p * n)
      + ε (p : ZMod M) * (p : ℂ) ^ (k - 1) * (if p ∣ n then ModularFormClass.qCoeff g (n / p) else 0)
        = a * ModularFormClass.qCoeff g n) :
    ‖a‖ ^ 2 < ((p : ℝ) + 1) ^ 2 * (p : ℝ) ^ (k - 2) := by
  revert M k ε g hg0 hg p hp hpM a ha
  exact @_root_.P2MW.S_CuspForm_norm_sq_lt_of_hasNebentypus_qCoeff_hecke_eigen.solution
