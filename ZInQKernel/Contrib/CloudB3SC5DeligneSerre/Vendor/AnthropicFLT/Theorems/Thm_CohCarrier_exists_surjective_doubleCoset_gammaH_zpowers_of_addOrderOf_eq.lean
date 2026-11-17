/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_CohCarrier_exists_surjective_doubleCoset_gammaH_zpowers_of_addOrderOf_eq (git blob abff2458fc69d3b44ed5f4c101be759261d5d1c9, sha256 fa2b438a79848a518ab1b72254e1f04b3ce65ea08932873be645356c8c651bac).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CohCarrier_Level
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_CohCarrier_exists_surjective_doubleCoset_gammaH_zpowers_of_addOrderOf_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open scoped MatrixGroups

theorem CohCarrier.exists_surjective_doubleCoset_gammaH_zpowers_of_addOrderOf_eq
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (g : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    ∃ c : {v : Fin 2 → ZMod M // addOrderOf v = M} →
        DoubleCoset.Quotient (CohCarrier.GammaH M H : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ))
          (Subgroup.zpowers g : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ)),
      Function.Surjective c ∧
      ∀ v v', c v = c v' ↔ ∃ (k : ℤ) (h : (ZMod M)ˣ), h ∈ H ∧
        v'.1 = (h : ZMod M) •
          ((Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) (g ^ k)).1.mulVec v.1) := by
  revert M H g
  exact @_root_.P2MW.S_CohCarrier_exists_surjective_doubleCoset_gammaH_zpowers_of_addOrderOf_eq.solution
