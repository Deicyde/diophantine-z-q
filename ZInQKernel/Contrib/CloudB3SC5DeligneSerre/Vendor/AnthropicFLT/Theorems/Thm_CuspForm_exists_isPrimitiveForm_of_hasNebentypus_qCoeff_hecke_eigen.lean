/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_CuspForm_exists_isPrimitiveForm_of_hasNebentypus_qCoeff_hecke_eigen (git blob 6dd54e39e99aa53f26a52cb553800cfb032c9960, sha256 2bc150d769da3b0fddce18e56255f98026d500b7db44ecc2c39fc09691f76d22).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_FLTPrelim_Modularity
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CuspForm_PrimitiveFormGamma1
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_CuspForm_exists_isPrimitiveForm_of_hasNebentypus_qCoeff_hecke_eigen

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups

theorem CuspForm.exists_isPrimitiveForm_of_hasNebentypus_qCoeff_hecke_eigen
    (N : ℕ) [NeZero N] (k : ℤ) (ε : DirichletCharacter ℂ N) (f : CuspForm (Gamma1 N) k) (hf0 : f ≠ 0)
    (hε : CuspForm.HasNebentypus ε f) (lam : ℕ → ℂ)
    (hf : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ n : ℕ,
        ModularFormClass.qCoeff f (p * n) +
            ε (p : ZMod N) * (p : ℂ) ^ (k - 1) * (if p ∣ n then ModularFormClass.qCoeff f (n / p) else 0) =
          lam p * ModularFormClass.qCoeff f n) :
    ∃ (M : ℕ) (_ : NeZero M) (εM : DirichletCharacter ℂ M) (g : CuspForm (Gamma1 M) k),
      M ∣ N ∧ CuspForm.IsPrimitiveForm εM g ∧
      ∀ p : ℕ, p.Prime → ¬ p ∣ N →
        ModularFormClass.qCoeff g p = lam p ∧ εM (p : ZMod M) = ε (p : ZMod N) := by
  revert N k ε f hf0 hε lam hf
  exact @_root_.P2MW.S_CuspForm_exists_isPrimitiveForm_of_hasNebentypus_qCoeff_hecke_eigen.solution
