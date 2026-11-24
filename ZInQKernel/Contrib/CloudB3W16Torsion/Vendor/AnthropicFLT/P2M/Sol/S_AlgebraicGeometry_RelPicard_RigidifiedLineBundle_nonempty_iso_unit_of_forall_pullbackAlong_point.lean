/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_unit_of_forall_pullbackAlong_point. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_bijective_algebraMap_sections_baseChange_of_bijective_of_field
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_bijective_algebraMap_sections_of_isProper_of_isIntegral
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_nonempty_pullback_baseChangeSnd_iso_unit_of_forall_point
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_unit_of_forall_pullbackAlong_point

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra

namespace P2mSeesawTriv

variable (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of k))
  [IsProper c] [IsIntegral X] (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c)
  {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType t] [IsReduced T]

theorem hH0 (A : Type u) [CommRing A] [Algebra k A] :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom
      (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap k A)) ⊤
    Function.Bijective (algebraMap A Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap k A), ⊤)) :=
  Scheme.bijective_algebraMap_sections_baseChange_of_bijective_of_field k c
    (Scheme.bijective_algebraMap_sections_of_isProper_of_isIntegral k c) A

theorem main (M : RigidifiedLineBundle c ε t)
    (hM : ∀ τ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) t,
      Nonempty ((M.pullbackAlong τ).L ≅
        SheafOfModules.unit (Limits.pullback c (𝟙 (Spec (CommRingCat.of k)))).ringCatSheaf)) :
    Nonempty (M.L ≅ SheafOfModules.unit (Limits.pullback c t).ringCatSheaf) := by

  have hloc := fun x : T =>
    Scheme.Modules.IsInvertible.exists_nonempty_pullback_baseChangeSnd_iso_unit_of_forall_point k c t M.L
      M.isInvertible hM x
  choose U hxU hU using hloc

  have key := RigidifiedLineBundle.nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections k c ε (hH0 k c) t
    (ι := T) (U := fun x => (U x : Scheme.{u})) (fun x => (U x).ι ≫ t)
    (fun x => (⟨(U x).ι, rfl⟩ : SchemeHomOver ((U x).ι ≫ t) t))
    (fun x => ⟨x, by simpa only [Scheme.Opens.range_ι, SetLike.mem_coe] using hxU x⟩)
    M (RigidifiedLineBundle.unit t)
    (fun x => ⟨(hU x).some ≪≫ (Scheme.Modules.pullbackUnitIso _).symm⟩)
  exact key

end P2mSeesawTriv

theorem solution
    (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of k))
    [IsProper c] [IsIntegral X] (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType t] [IsReduced T]
    (M : RigidifiedLineBundle c ε t)
    (hM : ∀ τ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) t,
      Nonempty ((M.pullbackAlong τ).L ≅
        SheafOfModules.unit (Limits.pullback c (𝟙 (Spec (CommRingCat.of k)))).ringCatSheaf)) :
    Nonempty (M.L ≅ SheafOfModules.unit (Limits.pullback c t).ringCatSheaf) :=
  P2mSeesawTriv.main k c ε t M hM
