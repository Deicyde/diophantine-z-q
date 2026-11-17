import ZInQKernel.Contrib.CloudB3W17bOka.Oka.AnalyticSpace.PullbackModulesStalk
import ZInQKernel.Contrib.CloudB3W17bOka.Oka.Algebra.Category.ModuleCat.Sheaf.PullbackStalk
import ZInQKernel.Contrib.CloudB3W17bAnalyticIdeal.UnitStalk
import ZInQKernel.Contrib.CloudB3W17bAnalyticIdeal.ExtendScalars

/-!
# Inverse-image ideals along morphisms of locally ringed spaces: stalks and vanishing locus

For `H : X ⟶ Y` a morphism of locally ringed spaces and an ideal `ιJ : J ⟶ 𝒪_Y`, the
inverse-image ideal is the image of `H^* J ⟶ H^* 𝒪_Y ≅ 𝒪_X`. Its vanishing locus (the support
of `𝒪_X ⧸ I`, i.e. where the stalk of the ideal inclusion is not surjective; not the support of
the module `I`) is `H⁻¹` of the vanishing locus of `J`. No analytic hypothesis is used here.
-/

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace ZInQ.Contrib.CloudB3W17bAnalyticIdeal

section UnitStalk

variable (Y : LocallyRingedSpace.{u}) (y : Y)

/-- **The stalk of the unit sheaf of modules on a locally ringed space is the stalk ring.** -/
noncomputable def lrsUnitStalkEquiv :
    (Y.stalkFunctor y).obj (SheafOfModules.unit Y.ringSheaf) ≃ₗ[Y.presheaf.stalk y]
      Y.presheaf.stalk y :=
  PM.unitStalkEquiv Y.presheaf y

theorem lrsUnitStalkEquiv_symm_apply (r : Y.presheaf.stalk y) :
    (lrsUnitStalkEquiv Y y).symm r = r • PM.unitStalkGen Y.presheaf y :=
  rfl

end UnitStalk

section Epi

variable {Y : LocallyRingedSpace.{u}}

/-- **Stalks send epimorphisms to surjections**: the module stalk functor is a left adjoint. -/
theorem lrs_surjective_stalk_of_epi {M N : SheafOfModules.{u} Y.ringSheaf} (φ : M ⟶ N) [Epi φ]
    (y : Y) : Function.Surjective ((Y.stalkFunctor y).map φ) := by
  have hadj : (Y.stalkFunctor y).IsLeftAdjoint :=
    ⟨_, ⟨SheafOfModules.stalkSkyscraperAdj (hR := Y.isSheaf_ringSheaf) y⟩⟩
  have : Epi ((Y.stalkFunctor y).map φ) := Functor.map_epi _ _
  exact (ModuleCat.epi_iff_surjective _).mp this

end Epi

section InverseImage

variable {X Y : LocallyRingedSpace.{u}}

/-- `H^* J ⟶ H^* 𝒪_Y ≅ 𝒪_X`. -/
noncomputable def invImageMap (H : X ⟶ Y) {J : SheafOfModules.{u} Y.ringSheaf}
    (ιJ : J ⟶ SheafOfModules.unit Y.ringSheaf) :
    H.pullbackModules.obj J ⟶ SheafOfModules.unit X.ringSheaf :=
  H.pullbackModules.map ιJ ≫ LocallyRingedSpace.Hom.pullbackModulesUnitToUnit H

/-- The inverse-image ideal `H⁻¹ J · 𝒪_X`: the image of `invImageMap`. -/
noncomputable abbrev invImageIdeal (H : X ⟶ Y) {J : SheafOfModules.{u} Y.ringSheaf}
    (ιJ : J ⟶ SheafOfModules.unit Y.ringSheaf) : SheafOfModules.{u} X.ringSheaf :=
  Abelian.image (invImageMap H ιJ)

/-- Its inclusion into `𝒪_X`. -/
noncomputable abbrev invImageIdealι (H : X ⟶ Y) {J : SheafOfModules.{u} Y.ringSheaf}
    (ιJ : J ⟶ SheafOfModules.unit Y.ringSheaf) :
    invImageIdeal H ιJ ⟶ SheafOfModules.unit X.ringSheaf :=
  Abelian.image.ι (invImageMap H ιJ)

instance (H : X ⟶ Y) {J : SheafOfModules.{u} Y.ringSheaf}
    (ιJ : J ⟶ SheafOfModules.unit Y.ringSheaf) : Mono (invImageIdealι H ιJ) :=
  inferInstanceAs (Mono (Abelian.image.ι _))

theorem factor_invImageIdealι (H : X ⟶ Y) {J : SheafOfModules.{u} Y.ringSheaf}
    (ιJ : J ⟶ SheafOfModules.unit Y.ringSheaf) :
    Abelian.factorThruImage (invImageMap H ιJ) ≫ invImageIdealι H ιJ = invImageMap H ιJ :=
  Abelian.image.fac _

/-- **Stalk reduction.** The stalk of `invImageMap` at `x` is surjective iff the extension of
scalars along `𝒪_{Y,Hx} → 𝒪_{X,x}` of the stalk of `ιJ` is. -/
theorem surjective_stalk_invImageMap_iff (H : X ⟶ Y) {J : SheafOfModules.{u} Y.ringSheaf}
    (ιJ : J ⟶ SheafOfModules.unit Y.ringSheaf) (x : X) :
    Function.Surjective ((X.stalkFunctor x).map (invImageMap H ιJ)) ↔
      Function.Surjective ((ModuleCat.extendScalars (H.stalkMap x).hom).map
        ((Y.stalkFunctor (H.base x)).map ιJ)) := by
  have nat := (LocallyRingedSpace.Hom.pullbackModulesStalkIso H x).hom.naturality ιJ
  simp only [Functor.comp_map] at nat
  have hO : Function.Bijective ((LocallyRingedSpace.Hom.pullbackModulesStalkIso H x).hom.app
      (SheafOfModules.unit Y.ringSheaf)) := ConcreteCategory.bijective_of_isIso _
  have hJ : Function.Bijective ((LocallyRingedSpace.Hom.pullbackModulesStalkIso H x).hom.app J) :=
    ConcreteCategory.bijective_of_isIso _
  have hU : Function.Bijective ((X.stalkFunctor x).map
      (LocallyRingedSpace.Hom.pullbackModulesUnitToUnit H)) := ConcreteCategory.bijective_of_isIso _
  have hfun : ⇑((LocallyRingedSpace.Hom.pullbackModulesStalkIso H x).hom.app
        (SheafOfModules.unit Y.ringSheaf)) ∘
        ⇑((X.stalkFunctor x).map (H.pullbackModules.map ιJ)) =
      ⇑((ModuleCat.extendScalars (H.stalkMap x).hom).map ((Y.stalkFunctor (H.base x)).map ιJ)) ∘
        ⇑((LocallyRingedSpace.Hom.pullbackModulesStalkIso H x).hom.app J) := by
    funext t
    exact congrArg (fun φ => φ t) nat
  have hmap : ⇑((X.stalkFunctor x).map (invImageMap H ιJ)) =
      ⇑((X.stalkFunctor x).map (LocallyRingedSpace.Hom.pullbackModulesUnitToUnit H)) ∘
        ⇑((X.stalkFunctor x).map (H.pullbackModules.map ιJ)) := by
    funext t
    rw [invImageMap, Functor.map_comp]
    rfl
  have h2 := Function.Surjective.of_comp_iff' hO
    (⇑((X.stalkFunctor x).map (H.pullbackModules.map ιJ)))
  exact (congrArg Function.Surjective hmap).to_iff.trans
    ((Function.Surjective.of_comp_iff' hU _).trans (h2.symm.trans
      ((congrArg Function.Surjective hfun).to_iff.trans
        (Function.Surjective.of_comp_iff _ hJ.2))))

/-- **Point-locus formula for `invImageMap`.** -/
theorem surjective_stalk_invImageMap_iff_stalk (H : X ⟶ Y) {J : SheafOfModules.{u} Y.ringSheaf}
    (ιJ : J ⟶ SheafOfModules.unit Y.ringSheaf) (x : X) :
    Function.Surjective ((X.stalkFunctor x).map (invImageMap H ιJ)) ↔
      Function.Surjective ((Y.stalkFunctor (H.base x)).map ιJ) :=
  (surjective_stalk_invImageMap_iff H ιJ x).trans
    (surjective_extendScalars_map_iff (H.stalkMap x).hom _ (lrsUnitStalkEquiv Y (H.base x)))

/-- The vanishing locus of an ideal `ι : I ⟶ 𝒪_Z`: where the stalk of `ι` is not surjective
(the support of `𝒪_Z ⧸ I`, not the support of the module `I`). -/
def vanishingLocus {Z : LocallyRingedSpace.{u}} {I : SheafOfModules.{u} Z.ringSheaf}
    (ι : I ⟶ SheafOfModules.unit Z.ringSheaf) : Set Z :=
  {z | ¬ Function.Surjective ((Z.stalkFunctor z).map ι)}

/-- The stalk of the image inclusion is surjective iff that of `invImageMap` is. -/
theorem surjective_stalk_invImageIdealι_iff (H : X ⟶ Y) {J : SheafOfModules.{u} Y.ringSheaf}
    (ιJ : J ⟶ SheafOfModules.unit Y.ringSheaf) (x : X) :
    Function.Surjective ((X.stalkFunctor x).map (invImageIdealι H ιJ)) ↔
      Function.Surjective ((X.stalkFunctor x).map (invImageMap H ιJ)) := by
  have hf : Function.Surjective ((X.stalkFunctor x).map
      (Abelian.factorThruImage (invImageMap H ιJ))) := lrs_surjective_stalk_of_epi _ x
  have hmap : ⇑((X.stalkFunctor x).map (invImageMap H ιJ)) =
      ⇑((X.stalkFunctor x).map (invImageIdealι H ιJ)) ∘
        ⇑((X.stalkFunctor x).map (Abelian.factorThruImage (invImageMap H ιJ))) := by
    have e := congrArg (fun φ => (X.stalkFunctor x).map φ) (factor_invImageIdealι H ιJ)
    simp only [Functor.map_comp] at e
    funext t
    exact (congrArg (fun φ => φ t) e).symm
  exact ((congrArg Function.Surjective hmap).to_iff.trans
    (Function.Surjective.of_comp_iff _ hf)).symm

/-- **Vanishing locus of the inverse-image ideal.** `V(H⁻¹ J · 𝒪_X) = H⁻¹ V(J)`. -/
theorem vanishingLocus_invImageIdeal (H : X ⟶ Y) {J : SheafOfModules.{u} Y.ringSheaf}
    (ιJ : J ⟶ SheafOfModules.unit Y.ringSheaf) :
    vanishingLocus (invImageIdealι H ιJ) = H.base ⁻¹' vanishingLocus ιJ := by
  ext x
  simp only [vanishingLocus, Set.mem_ofPred_eq]
  rw [surjective_stalk_invImageIdealι_iff, surjective_stalk_invImageMap_iff_stalk H ιJ x]
  exact Iff.rfl

end InverseImage

end ZInQ.Contrib.CloudB3W17bAnalyticIdeal
