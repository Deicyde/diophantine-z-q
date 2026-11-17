/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_mul_mul_tensor_iso. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_SheafOfModules_Monoidal
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesTensorPow
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_mul_mul_tensor_iso

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

open scoped CategoryTheory.MonObj

theorem AlgebraicGeometry.Scheme.Modules.nonempty_pullback_mul_mul_tensor_iso
    (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}} (t : X ⟶ Spec (CommRingCat.of k))
    [GrpObj (Over.mk t)] [IsCommMonObj (Over.mk t)]
    (hsm : Smooth t) (hpr : IsProper t) (hgc : GeometricallyConnected t)
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L)
    {Y : Over (Spec (CommRingCat.of k))} (f g h : Y ⟶ Over.mk t) :
    Nonempty (
      (Scheme.Modules.pullback (f * g * h).left).obj L ⊗ (Scheme.Modules.pullback f.left).obj L ⊗
          (Scheme.Modules.pullback g.left).obj L ⊗ (Scheme.Modules.pullback h.left).obj L ≅
        (Scheme.Modules.pullback (f * g).left).obj L ⊗ (Scheme.Modules.pullback (f * h).left).obj L ⊗
          (Scheme.Modules.pullback (g * h).left).obj L) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_mul_mul_tensor_iso.solution
