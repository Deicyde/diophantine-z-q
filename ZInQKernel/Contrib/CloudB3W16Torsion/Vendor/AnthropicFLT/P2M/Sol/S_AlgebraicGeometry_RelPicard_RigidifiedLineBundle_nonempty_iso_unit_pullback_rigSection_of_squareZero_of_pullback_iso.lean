/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_unit_pullback_rigSection_of_squareZero_of_pullback_iso. Apache-2.0.
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
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_unit_of_pullback_squareZero
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_unit_pullback_rigSection_of_squareZero_of_pullback_iso

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 24000000

theorem solution
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
        ≅ SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf) := by
  have hεL'inv : Scheme.Modules.IsInvertible
      ((Scheme.Modules.pullback
        (rigSection c (Spec.map (CommRingCat.ofHom (algebraMap R B))) ε)).obj L') :=
    hL'.pullback _

  have step1 :
      (Scheme.Modules.pullback ι.1).obj
        ((Scheme.Modules.pullback
          (rigSection c (Spec.map (CommRingCat.ofHom (algebraMap R B))) ε)).obj L')
        ≅ SheafOfModules.unit (Spec (CommRingCat.of (B ⧸ I))).ringCatSheaf :=
    (Scheme.Modules.pullbackComp _ _).app L' ≪≫
      (Scheme.Modules.pullbackCongr (rigSection_baseChangeSnd c ε ι).symm).app L' ≪≫
      ((Scheme.Modules.pullbackComp _ _).app L').symm ≪≫
      (Scheme.Modules.pullback _).mapIso isoL.some ≪≫
      M.rigidified.some

  have htriv : Nonempty ((Scheme.Modules.pullback
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).obj
        ((Scheme.Modules.pullback
          (rigSection c (Spec.map (CommRingCat.ofHom (algebraMap R B))) ε)).obj L')
        ≅ SheafOfModules.unit (Spec (CommRingCat.of (B ⧸ I))).ringCatSheaf) := by
    rw [← hι]; exact ⟨step1⟩
  exact Scheme.Modules.IsInvertible.nonempty_iso_unit_of_pullback_squareZero I hI _ hεL'inv htriv
