/-
Copyright (c) 2026 H5/NOS Round-2 Lane5 contributors.
Released under Apache 2.0 license as described in the project LICENSE.

Upgrade the ACTUAL constructed generic comparison to a GROUP iso. Its
base change is literally the original generic GROUP identification after
the restricted cartesian GROUP iso. Actual fpqc faithfulness reflects the
unit/multiplication diagrams; no IsMonHom or output generic-iso premise is
supplied and no scheme-only surrogate is substituted for good reduction.
-/
import ZInQKernel.Contrib.CloudR2NOS.GoodDescent.Effective.GenericOutput
import ZInQKernel.Contrib.CloudR2NOS.GoodDescent.Effective.GenericCoverGroup
import ZInQKernel.Contrib.CloudR2NOS.GoodDescent.Effective.ReflectMonHom
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective
open TensorCofaces TensorNerve

/-- The original generic SCHEME comparison, as an iso in the native Over
    category, with only the canonical open/pullback comparison inserted. -/
def genericOutputOverIso {S : Scheme.{u}} (V : S.Opens) (D : Grp (Over S))
    (A : Grp (Over V.toScheme)) (i : (D.X.hom ⁻¹ᵁ V).toScheme ≅ A.X.left)
    (hi : i.hom ≫ A.X.hom = D.X.hom ∣_ V) :
    ((Over.pullback V.ι).mapGrp.obj D).X ≅ A.X :=
  Over.isoMk (pullbackRestrictIsoRestrict D.X.hom V ≪≫ i) (by
    change (pullbackRestrictIsoRestrict D.X.hom V).hom ≫ i.hom ≫ A.X.hom = pullback.snd D.X.hom V.ι
    rw [hi, pullbackRestrictIsoRestrict_hom_morphismRestrict])

/-- Construct the generic GROUP iso on the SAME effective output. The
    original coordinate comparison and its inverse are not caller inputs. -/
theorem exists_genericGroupIso_on_effective_output
    {R : Type u} [CommRing R] (R' : Type u) [CommRing R'] [Algebra R R']
    [Module.FaithfullyFlat R R'] (V : (Base R).Opens)
    (G : Grp (Over (Cover R'))) (A : Grp (Over V.toScheme))
    (e : (Over.pullback ((baseMap R R') ⁻¹ᵁ V).ι).mapGrp.obj G ≅
      (Over.pullback ((baseMap R R') ∣_ V)).mapGrp.obj A)
    [Etale (baseMap R R')] (c : Base R)
    [Mono ((baseMap R R').fiberToSpecResidueField c)]
    (hV : ∀ z : Base R, z ∉ V → z = c)
    (D : Grp (Over (Base R))) (q : G.X.left ⟶ D.X.left)
    (hq : IsPullback q G.X.hom D.X.hom (baseMap R R'))
    (iG : G ≅ (Over.pullback (baseMap R R')).mapGrp.obj D)
    (hiG : iG.hom.hom.hom.left ≫ pullback.fst D.X.hom (baseMap R R') = q)
    (hco : projection1 (R := R) R' G ≫ q = projection2 R' V G A e c hV ≫ q) :
    Nonempty ((Over.pullback V.ι).mapGrp.obj D ≅ A) := by
  obtain ⟨i, hi, hib⟩ := exists_genericSchemeIso_on_effective_output R' V G A e c hV D q hq hco
  let p := baseMap R R'
  let g := p ∣_ V
  let DG := (Over.pullback V.ι).mapGrp.obj D
  let GG := (Over.pullback (p ⁻¹ᵁ V).ι).mapGrp.obj G
  let HG := (Over.pullback g).mapGrp.obj DG
  let HA := (Over.pullback g).mapGrp.obj A
  letI : GrpObj ((Over.pullback g).obj DG.X) := HG.grp
  letI : GrpObj ((Over.pullback g).obj A.X) := HA.grp
  let C := genericCoverGroupIso p V G D iG
  let C₀ : GG.X ≅ HG.X := (Grp.forget _).mapIso C
  let e₀ : GG.X ≅ HA.X := (Grp.forget _).mapIso e
  let E : DG.X ≅ A.X := genericOutputOverIso V D A i hib
  let rG := pullbackRestrictIsoRestrict G.X.hom (p ⁻¹ᵁ V)
  let rD := pullbackRestrictIsoRestrict D.X.hom V
  let a : pullback G.X.hom (p ⁻¹ᵁ V).ι ⟶ pullback (pullback.snd D.X.hom V.ι) g := C₀.hom.left
  let er : pullback G.X.hom (p ⁻¹ᵁ V).ι ⟶ pullback A.X.hom g := e₀.hom.left
  let F := Over.pullback g
  let fr : pullback (pullback.snd D.X.hom V.ι) g ⟶ pullback A.X.hom g := (F.map E.hom).left
  have hfr₁ : fr ≫ pullback.fst A.X.hom g = pullback.fst (pullback.snd D.X.hom V.ι) g ≫ E.hom.left :=
    pullback.lift_fst _ _ _
  have hfr₂ : fr ≫ pullback.snd A.X.hom g = pullback.snd (pullback.snd D.X.hom V.ι) g := pullback.lift_snd _ _ _
  have hRD : rD.hom ≫ (D.X.hom ⁻¹ᵁ V).ι = pullback.fst D.X.hom V.ι := pullbackRestrictIsoRestrict_hom_ι _ _
  have hRG : rG.hom ≫ (modelGenericOpen R' V G).ι = pullback.fst G.X.hom (p ⁻¹ᵁ V).ι :=
    pullbackRestrictIsoRestrict_hom_ι _ _
  have ht : a ≫ pullback.fst (pullback.snd D.X.hom V.ι) g ≫ pullback.fst D.X.hom V.ι =
      pullback.fst G.X.hom (p ⁻¹ᵁ V).ι ≫ q := genericCoverGroupIso_coordinate p V G D iG q hiG
  have hopen : a ≫ pullback.fst (pullback.snd D.X.hom V.ι) g ≫ rD.hom = rG.hom ≫ genericCartMap hq V := by
    apply (cancel_mono (D.X.hom ⁻¹ᵁ V).ι).mp
    calc
      (a ≫ pullback.fst (pullback.snd D.X.hom V.ι) g ≫ rD.hom) ≫ (D.X.hom ⁻¹ᵁ V).ι =
          a ≫ pullback.fst (pullback.snd D.X.hom V.ι) g ≫ pullback.fst D.X.hom V.ι := by
        rw [Category.assoc, Category.assoc, hRD]
      _ = pullback.fst G.X.hom (p ⁻¹ᵁ V).ι ≫ q := ht
      _ = (rG.hom ≫ genericCartMap hq V) ≫ (D.X.hom ⁻¹ᵁ V).ι := by
        rw [Category.assoc, genericCartMap_ι, ← Category.assoc, hRG]
  have hE : E.hom.left = rD.hom ≫ i.hom := rfl
  have hraw : a ≫ fr = er := by
    apply pullback.hom_ext
    · rw [Category.assoc, hfr₁, hE]
      have h₁ : a ≫ pullback.fst (pullback.snd D.X.hom V.ι) g ≫ (rD.hom ≫ i.hom) =
          (rG.hom ≫ genericCartMap hq V) ≫ i.hom := by
        simpa only [Category.assoc] using congrArg
          (fun m : pullback G.X.hom (p ⁻¹ᵁ V).ι ⟶ (D.X.hom ⁻¹ᵁ V).toScheme => m ≫ i.hom) hopen
      have hi' : genericCartMap hq V ≫ i.hom = (genericModelOfGroupIso p V G A e).q := hi
      have h₂ : (rG.hom ≫ genericCartMap hq V) ≫ i.hom =
          rG.hom ≫ (genericModelOfGroupIso p V G A e).q :=
        (Category.assoc rG.hom (genericCartMap hq V) i.hom).trans (congrArg (rG.hom ≫ ·) hi')
      have h₃ : rG.hom ≫ (genericModelOfGroupIso p V G A e).q = er ≫ pullback.fst A.X.hom g := by
        change rG.hom ≫ (rG.inv ≫ er ≫ pullback.fst A.X.hom g) = _
        rw [Iso.hom_inv_id_assoc]
      exact h₁.trans (h₂.trans h₃)
    · rw [Category.assoc, hfr₂]
      have hC : a ≫ pullback.snd (pullback.snd D.X.hom V.ι) g = pullback.snd G.X.hom (p ⁻¹ᵁ V).ι := by
        have h := Over.w C₀.hom
        change a ≫ pullback.snd (pullback.snd D.X.hom V.ι) g = pullback.snd G.X.hom (p ⁻¹ᵁ V).ι at h
        exact h
      have he : er ≫ pullback.snd A.X.hom g = pullback.snd G.X.hom (p ⁻¹ᵁ V).ι := by
        have h := Over.w e₀.hom
        change er ≫ pullback.snd A.X.hom g = pullback.snd G.X.hom (p ⁻¹ᵁ V).ι at h
        exact h
      exact hC.trans he.symm
  have hOver : C₀.hom ≫ F.map E.hom = e₀.hom := by
    apply Over.OverMorphism.ext
    exact hraw
  have hmap : F.map E.hom = C₀.inv ≫ e₀.hom := by
    apply (cancel_epi C₀.hom).mp
    calc
      C₀.hom ≫ F.map E.hom = e₀.hom := hOver
      _ = C₀.hom ≫ (C₀.inv ≫ e₀.hom) := by
        rw [← Category.assoc, C₀.hom_inv_id, Category.id_comp]
  have hf : IsMonHom (F.map E.hom) := by
    rw [hmap]
    change IsMonHom (C.inv.hom.hom ≫ e.hom.hom.hom)
    infer_instance
  haveI : Surjective p := by
    constructor
    exact PrimeSpectrum.comap_surjective_of_faithfullyFlat
  haveI : Surjective g := MorphismProperty.of_isPullback (isPullback_morphismRestrict p V).flip inferInstance
  haveI : (Over.pullback g).Faithful := inferInstance
  haveI : IsMonHom E.hom := isMonHom_of_faithful_map F E.hom hf
  exact ⟨Grp.mkIso' E⟩

#print axioms exists_genericGroupIso_on_effective_output

end ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective
