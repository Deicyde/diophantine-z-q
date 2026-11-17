/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_unit_of_forall_pullbackAlong_point. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_unit_of_forall_pullbackAlong_point

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra

theorem AlgebraicGeometry.RelPicard.RigidifiedLineBundle.nonempty_iso_unit_of_forall_pullbackAlong_point
    (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of k))
    [IsProper c] [IsIntegral X] (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType t] [IsReduced T]
    (M : RigidifiedLineBundle c ε t)
    (hM : ∀ τ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) t,
      Nonempty ((M.pullbackAlong τ).L ≅
        SheafOfModules.unit (Limits.pullback c (𝟙 (Spec (CommRingCat.of k)))).ringCatSheaf)) :
    Nonempty (M.L ≅ SheafOfModules.unit (Limits.pullback c t).ringCatSheaf) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_unit_of_forall_pullbackAlong_point.solution
