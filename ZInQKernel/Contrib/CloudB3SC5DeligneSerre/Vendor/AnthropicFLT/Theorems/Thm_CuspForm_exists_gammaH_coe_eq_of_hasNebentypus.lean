/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_CuspForm_exists_gammaH_coe_eq_of_hasNebentypus (git blob 4f836e9798031d0d7744f819bcd57de9713125c2, sha256 500805a831db7e8eba4e6533820a2c2b706d36fa4ee556c66f38f1f26a02275c).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CohCarrier_Level
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CuspForm_PrimitiveFormGamma1
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_CuspForm_exists_gammaH_coe_eq_of_hasNebentypus

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open scoped MatrixGroups

theorem CuspForm.exists_gammaH_coe_eq_of_hasNebentypus
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) (ε : DirichletCharacter ℂ M)
    (hε : ∀ d : (ZMod M)ˣ, d ∈ H → ε (d : ZMod M) = 1)
    (g : CuspForm (CongruenceSubgroup.Gamma1 M) k) (hg : CuspForm.HasNebentypus ε g) :
    ∃ f : CuspForm (CohCarrier.GammaH M H) k, (⇑f : UpperHalfPlane → ℂ) = ⇑g := by
  revert M H k ε hε g hg
  exact @_root_.P2MW.S_CuspForm_exists_gammaH_coe_eq_of_hasNebentypus.solution
