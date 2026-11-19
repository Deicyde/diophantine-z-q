/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_CuspForm_exists_hasNebentypus_of_qCoeff_hecke_eigen (git blob 5993b365909aaa0159d4c87251a5baff118f1b73, sha256 98e6816ba919a24bd238e46e09923df861c1d876cc68f00fb0e7a7701fff4ff7).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_FLTPrelim_Modularity
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CuspForm_PrimitiveFormGamma1
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_CuspForm_exists_hasNebentypus_of_qCoeff_hecke_eigen

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups

theorem CuspForm.exists_hasNebentypus_of_qCoeff_hecke_eigen
    (N : ℕ) [NeZero N] (k : ℤ) (f : CuspForm (Gamma1 N) k) (hf0 : f ≠ 0)
    (χ : ℕ → ℂ)
    (hf : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∃ lam : ℂ, ∀ n : ℕ,
        ModularFormClass.qCoeff f (p * n) +
            χ p * (if p ∣ n then ModularFormClass.qCoeff f (n / p) else 0) =
          lam * ModularFormClass.qCoeff f n) :
    ∃ ε : DirichletCharacter ℂ N, CuspForm.HasNebentypus ε f ∧
      ∀ p : ℕ, p.Prime → ¬ p ∣ N → ε (p : ZMod N) * (p : ℂ) ^ (k - 1) = χ p := by
  revert N k f hf0 χ hf
  exact @_root_.P2MW.S_CuspForm_exists_hasNebentypus_of_qCoeff_hecke_eigen.solution
