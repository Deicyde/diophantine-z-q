/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_CuspForm_peterssonOn_add_smul_conj (git blob b4017a3cba2b68f8349e88d6a9ef5b25852ddcae, sha256 c6f18e381856d2e3a18c3bc3c19c1f0a8fdfd24052badcb9726f76a224b68def).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CuspForm_PeterssonOn
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_CuspForm_peterssonOn_add_smul_conj

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open scoped MatrixGroups

theorem CuspForm.peterssonOn_add_smul_conj (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (k : ℤ)
    (f g h : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (c : ℂ) :
    CuspForm.peterssonOn Γ k f (g + h) = CuspForm.peterssonOn Γ k f g + CuspForm.peterssonOn Γ k f h ∧
    CuspForm.peterssonOn Γ k f (c • g) = c * CuspForm.peterssonOn Γ k f g ∧
    starRingEnd ℂ (CuspForm.peterssonOn Γ k g f) = CuspForm.peterssonOn Γ k f g := by
  revert Γ k f g h c
  exact @_root_.P2MW.S_CuspForm_peterssonOn_add_smul_conj.solution
