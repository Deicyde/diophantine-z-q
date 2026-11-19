/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_CuspForm_hasNebentypus_inv_and_qCoeff_hecke_eigen_of_fricke (git blob 3ab74a9005c7158496807c90a35bd1b75a73f5cc, sha256 5479c6a9b1aa9c64f4cd8df47250efc332ee7223da5baae3db8338ba7ea565a9).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_FLTPrelim_Modularity
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CuspForm_PrimitiveFormGamma1
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_CuspForm_hasNebentypus_inv_and_qCoeff_hecke_eigen_of_fricke

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups

theorem CuspForm.hasNebentypus_inv_and_qCoeff_hecke_eigen_of_fricke
    (M : ℕ) [NeZero M] (k : ℤ) (ε : DirichletCharacter ℂ M) (g h : CuspForm (Gamma1 M) k)
    (hg : CuspForm.HasNebentypus ε g)
    (hh : ∀ τ τ' : UpperHalfPlane, (τ' : ℂ) * ((M : ℂ) * (τ : ℂ)) = -1 →
      g τ' = (τ : ℂ) ^ k * h τ) :
    CuspForm.HasNebentypus ε⁻¹ h ∧
      ∀ p : ℕ, p.Prime → ¬ p ∣ M → ∀ lam : ℂ,
        (∀ n : ℕ, ModularFormClass.qCoeff g (p * n) +
            ε (p : ZMod M) * (p : ℂ) ^ (k - 1) *
              (if p ∣ n then ModularFormClass.qCoeff g (n / p) else 0) =
          lam * ModularFormClass.qCoeff g n) →
        ∀ n : ℕ, ModularFormClass.qCoeff h (p * n) +
            ε⁻¹ (p : ZMod M) * (p : ℂ) ^ (k - 1) *
              (if p ∣ n then ModularFormClass.qCoeff h (n / p) else 0) =
          ε⁻¹ (p : ZMod M) * lam * ModularFormClass.qCoeff h n := by
  revert M k ε g h hg hh
  exact @_root_.P2MW.S_CuspForm_hasNebentypus_inv_and_qCoeff_hecke_eigen_of_fricke.solution
