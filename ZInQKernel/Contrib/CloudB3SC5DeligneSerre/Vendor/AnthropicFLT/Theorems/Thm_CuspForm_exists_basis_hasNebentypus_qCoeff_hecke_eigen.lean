/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_CuspForm_exists_basis_hasNebentypus_qCoeff_hecke_eigen (git blob 4792868d510bd3d4fa5072b1e0d4907c5af0bd93, sha256 4c08d4b78b16e9391a5cd8c00f669e1ec147bb6270112114450d0e148e036da3).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_FLTPrelim_Modularity
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CuspForm_PrimitiveFormGamma1
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_CuspForm_exists_basis_hasNebentypus_qCoeff_hecke_eigen

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups

theorem CuspForm.exists_basis_hasNebentypus_qCoeff_hecke_eigen
    (N : ℕ) [NeZero N] (k : ℤ) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℂ (CuspForm (Gamma1 N) k)),
      ∀ i, ∃ ε : DirichletCharacter ℂ N, CuspForm.HasNebentypus ε (b i) ∧
        ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∃ lam : ℂ, ∀ m : ℕ,
          ModularFormClass.qCoeff (b i) (p * m) +
              ε (p : ZMod N) * (p : ℂ) ^ (k - 1) *
                (if p ∣ m then ModularFormClass.qCoeff (b i) (m / p) else 0) =
            lam * ModularFormClass.qCoeff (b i) m := by
  revert N k
  exact @_root_.P2MW.S_CuspForm_exists_basis_hasNebentypus_qCoeff_hecke_eigen.solution
