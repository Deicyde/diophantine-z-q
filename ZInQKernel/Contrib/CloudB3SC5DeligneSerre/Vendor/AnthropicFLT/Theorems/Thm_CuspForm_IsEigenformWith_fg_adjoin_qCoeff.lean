/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_CuspForm_IsEigenformWith_fg_adjoin_qCoeff (git blob 86eb98caa7a0f42907a9a02ab0a8133ff1539f8d, sha256 6501179f6816458045397b3aa770a020b53e77fecd12123c2dec0e5552e8b4e6).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CuspForm_PrimitiveFormGamma1
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_CuspForm_IsEigenformWith_fg_adjoin_qCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

theorem CuspForm.IsEigenformWith.fg_adjoin_qCoeff
    {M : ℕ} [NeZero M] {ε : DirichletCharacter ℂ M}
    {h : CuspForm (CongruenceSubgroup.Gamma1 M) 2} (hh : CuspForm.IsEigenformWith ε h) :
    (Subalgebra.toSubmodule (Algebra.adjoin ℤ
      ((Set.range fun n : ℕ => ModularFormClass.qCoeff h n) ∪
        Set.range fun u : (ZMod M)ˣ => ε (u : ZMod M)))).FG := by
  revert M ε h hh
  exact @_root_.P2MW.S_CuspForm_IsEigenformWith_fg_adjoin_qCoeff.solution
