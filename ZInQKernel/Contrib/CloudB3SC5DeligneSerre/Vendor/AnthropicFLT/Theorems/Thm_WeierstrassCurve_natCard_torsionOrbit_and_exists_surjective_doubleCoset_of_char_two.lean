/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_WeierstrassCurve_natCard_torsionOrbit_and_exists_surjective_doubleCoset_of_char_two (git blob 876479df494b6e68df86599af0ca28100237f35f, sha256 54d11b71d5b54b96cc6813ae7bd42c6a04d3ab7708140983dfe4453d3fdfdbed).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CohCarrier_Level
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_WeierstrassCurve_natCard_torsionOrbit_and_exists_surjective_doubleCoset_of_char_two

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open WeierstrassCurve WeierstrassCurve.Affine
open scoped MatrixGroups

theorem WeierstrassCurve.natCard_torsionOrbit_and_exists_surjective_doubleCoset_of_char_two
    {L : Type*} [Field L] [DecidableEq L] [IsAlgClosed L] [CharP L 2]
    (w : Lˣ) (hw : (w : L) ^ 3 = 1) (hw1 : (w : L) ≠ 1)
    (M : ℕ) [NeZero M] (hM : (M : L) ≠ 0) (H : Subgroup (ZMod M)ˣ) :
    Nat.card {s : Set (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve L).toAffine.Point //
        ∃ P : (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve L).toAffine.Point, addOrderOf P = M ∧
          s = {T | ∃ u : (ZMod M)ˣ, u ∈ H ⊔ Subgroup.zpowers (-1) ∧ T = (u : ZMod M).val • P}} =
      (CohCarrier.GammaH M H ⊔ Subgroup.zpowers (-1)).index ∧
    (∃ c : {s : Set (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve L).toAffine.Point //
          ∃ P : (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve L).toAffine.Point, addOrderOf P = M ∧
            s = {T | ∃ u : (ZMod M)ˣ, u ∈ H ⊔ Subgroup.zpowers (-1) ∧ T = (u : ZMod M).val • P}} →
        DoubleCoset.Quotient (CohCarrier.GammaH M H : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ))
          (Subgroup.zpowers (ModularGroup.S * ModularGroup.T) :
            Set (Matrix.SpecialLinearGroup (Fin 2) ℤ)),
      Function.Surjective c ∧
      ∀ s s', c s = c s' ↔ ∃ k : ℕ, ∀ T ∈ s.1, ∃ T' ∈ s'.1,
        HEq (Point.vcInvFun ((⟨w, 0, 0, 0⟩ : VariableChange L) ^ k)
          (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve L).toAffine T) T') ∧
    (∃ c : {s : Set (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve L).toAffine.Point //
          ∃ P : (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve L).toAffine.Point, addOrderOf P = M ∧
            s = {T | ∃ u : (ZMod M)ˣ, u ∈ H ⊔ Subgroup.zpowers (-1) ∧ T = (u : ZMod M).val • P}} →
        DoubleCoset.Quotient (CohCarrier.GammaH M H : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ))
          (Subgroup.zpowers ModularGroup.S : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ)),
      Function.Surjective c ∧
      ∀ s s', c s = c s' ↔ ∃ k : ℕ, ∀ T ∈ s.1, ∃ T' ∈ s'.1,
        HEq (Point.vcInvFun ((⟨1, 1, 1, (w : L)⟩ : VariableChange L) ^ k)
          (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve L).toAffine T) T') := by
  revert L w hw hw1 M hM H
  exact @_root_.P2MW.S_WeierstrassCurve_natCard_torsionOrbit_and_exists_surjective_doubleCoset_of_char_two.solution
