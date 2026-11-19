/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_CuspForm_exists_qCoeff_eq_sum_isPrimitiveForm_of_hasNebentypus (git blob eaa723b52cffe8760386a67ae5d310a4db8bbc5a, sha256 9effa0e170dcbd99719673712be81dabb20f811452b46a91af8ffd0ff5fbb236).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_FLTPrelim_Modularity
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CuspForm_PrimitiveFormGamma1
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_CuspForm_exists_qCoeff_eq_sum_isPrimitiveForm_of_hasNebentypus

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups

theorem CuspForm.exists_qCoeff_eq_sum_isPrimitiveForm_of_hasNebentypus
    (N : ℕ) [NeZero N] (k : ℤ) (ε : DirichletCharacter ℂ N) (f : CuspForm (Gamma1 N) k)
    (hf : CuspForm.HasNebentypus ε f) :
    ∃ (n : ℕ) (M d : Fin n → ℕ) (hM : ∀ i, M i * d i ∣ N)
      (εM : (i : Fin n) → DirichletCharacter ℂ (M i))
      (g : (i : Fin n) → CuspForm (Gamma1 (M i)) k) (c : Fin n → ℂ),
      (∀ i, CuspForm.IsPrimitiveForm (εM i) (g i) ∧
        DirichletCharacter.changeLevel (dvd_of_mul_right_dvd (hM i)) (εM i) = ε) ∧
      ∀ m : ℕ, ModularFormClass.qCoeff f m =
        ∑ i, c i * (if d i ∣ m then ModularFormClass.qCoeff (g i) (m / d i) else 0) := by
  revert N k ε f hf
  exact @_root_.P2MW.S_CuspForm_exists_qCoeff_eq_sum_isPrimitiveForm_of_hasNebentypus.solution
