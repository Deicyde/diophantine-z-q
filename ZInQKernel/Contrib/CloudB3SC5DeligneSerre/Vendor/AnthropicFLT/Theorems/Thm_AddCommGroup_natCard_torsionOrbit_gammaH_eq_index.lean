/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AddCommGroup_natCard_torsionOrbit_gammaH_eq_index (git blob df872c17ac62ea140bc41d3d2224e5b0bbe7254a, sha256 6aca2cb25705ea878ecb58b02c809335dd85c6af702dbcc4591ab19e781388dd).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CohCarrier_Level
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AddCommGroup_natCard_torsionOrbit_gammaH_eq_index

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open scoped MatrixGroups

theorem AddCommGroup.natCard_torsionOrbit_gammaH_eq_index
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) {A : Type*} [AddCommGroup A]
    (e : ZMod M × ZMod M ≃+ Submodule.torsionBy ℤ A M) :
    Nat.card {s : Set A // ∃ P : A, addOrderOf P = M ∧
        s = {T | ∃ u : (ZMod M)ˣ, u ∈ H ⊔ Subgroup.zpowers (-1) ∧ T = (u : ZMod M).val • P}} =
      (CohCarrier.GammaH M H ⊔ Subgroup.zpowers (-1)).index := by
  revert M H A e
  exact @_root_.P2MW.S_AddCommGroup_natCard_torsionOrbit_gammaH_eq_index.solution
