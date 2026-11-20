/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_exists_iso_map_pullback_rigSection_comp_eq. Apache-2.0.
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
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_exists_iso_map_pullback_rigSection_comp_eq

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra

theorem AlgebraicGeometry.RelPicard.RigidifiedLineBundle.exists_iso_map_pullback_rigSection_comp_eq
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M M' : RigidifiedLineBundle c ε t)
    (α : (Scheme.Modules.pullback (rigSection c t ε)).obj M.L ≅ SheafOfModules.unit T.ringCatSheaf)
    (α' : (Scheme.Modules.pullback (rigSection c t ε)).obj M'.L ≅ SheafOfModules.unit T.ringCatSheaf)
    (φ : M.L ≅ M'.L) :
    ∃ φ' : M.L ≅ M'.L, (Scheme.Modules.pullback (rigSection c t ε)).mapIso φ' ≪≫ α' = α := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_exists_iso_map_pullback_rigSection_comp_eq.solution
