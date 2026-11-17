/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_unit_pullback_rigSection_of_squareZero_of_pullback_iso. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_unit_pullback_rigSection_of_squareZero_of_pullback_iso

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra TensorProduct

set_option autoImplicit false

theorem AlgebraicGeometry.RelPicard.RigidifiedLineBundle.nonempty_iso_unit_pullback_rigSection_of_squareZero_of_pullback_iso
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    {B : Type u} [CommRing B] [Algebra R B] (I : Ideal B) (hI : I ^ 2 = ⊥)
    (ι : SchemeHomOver
      (Spec.map (CommRingCat.ofHom (algebraMap R (B ⧸ I))))
      (Spec.map (CommRingCat.ofHom (algebraMap R B))))
    (hι : ι.1 = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
    (M : RigidifiedLineBundle c ε (Spec.map (CommRingCat.ofHom (algebraMap R (B ⧸ I)))))
    (L' : (pullback c (Spec.map (CommRingCat.ofHom (algebraMap R B)))).Modules)
    (hL' : Scheme.Modules.IsInvertible L')
    (isoL : Nonempty ((Scheme.Modules.pullback (baseChangeSnd c ι)).obj L' ≅ M.L)) :
    Nonempty
      ((Scheme.Modules.pullback (rigSection c (Spec.map (CommRingCat.ofHom (algebraMap R B))) ε)).obj L'
        ≅ SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_unit_pullback_rigSection_of_squareZero_of_pullback_iso.solution
