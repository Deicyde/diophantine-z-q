/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicGeometry_isIso_lift_baseChange_fst_baseChange_snd
Modified for the Z-in-Q kernel (2026-11-16, task neron-flt): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_isIso_lift_baseChange_fst_baseChange_snd

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.isIso_lift_baseChange_fst_baseChange_snd
    {S S' Z X : Scheme.{u}} (z : Z ⟶ S) (f : X ⟶ S) (ι : S' ⟶ S) :
    IsIso
      (pullback.lift
        (pullback.lift (pullback.fst (pullback.fst z f ≫ z) ι ≫ pullback.fst z f)
          (pullback.snd (pullback.fst z f ≫ z) ι)
          (by rw [Category.assoc]; exact pullback.condition))
        (pullback.lift (pullback.fst (pullback.fst z f ≫ z) ι ≫ pullback.snd z f)
          (pullback.snd (pullback.fst z f ≫ z) ι)
          (by rw [Category.assoc, ← pullback.condition (f := z) (g := f)]; exact pullback.condition))
        (by rw [pullback.lift_snd, pullback.lift_snd]) :
        pullback (pullback.fst z f ≫ z) ι ⟶ pullback (pullback.snd z ι) (pullback.snd f ι)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isIso_lift_baseChange_fst_baseChange_snd.solution
