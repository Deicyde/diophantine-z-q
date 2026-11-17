/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_CuspForm_exists_degeneracy_gamma1_hasNebentypus (git blob 2dfba746f489c3fff222f0f3196662eaee8eee22, sha256 3c31e82dc04ed78bd3295ce043fc538673addf3a84ba25d558cf3f822dc959cd).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularForm_HeckeOperator
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_FLTPrelim_Modularity
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CuspForm_PrimitiveFormGamma1
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_CuspForm_exists_degeneracy_gamma1_hasNebentypus

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups

theorem CuspForm.exists_degeneracy_gamma1_hasNebentypus
    {k : ℤ} {M N d : ℕ} [NeZero N] (hd : M * d ∣ N) (g : CuspForm (Gamma1 M) k) :
    ∃ G : CuspForm (Gamma1 N) k,
      (∀ τ : UpperHalfPlane, G τ = g (ModularForm.heckeDiagMatrix d • τ)) ∧
      (∀ n : ℕ, ModularFormClass.qCoeff G n =
        if d ∣ n then ModularFormClass.qCoeff g (n / d) else 0) ∧
      ∀ ε : DirichletCharacter ℂ M, CuspForm.HasNebentypus ε g →
        CuspForm.HasNebentypus (DirichletCharacter.changeLevel (dvd_of_mul_right_dvd hd) ε) G := by
  revert k M N d hd g
  exact @_root_.P2MW.S_CuspForm_exists_degeneracy_gamma1_hasNebentypus.solution
