import ZInQKernel.OneProof.H.TailZ7
import ZInQKernel.OneProof.H.TailC
import ZInQKernel.Contrib.OneProof.CMFibreSplit.CurveOrder
import ZInQKernel.Contrib.OneProof.CMFibreSplit.Reduction
import ZInQKernel.Contrib.AVB1.BaseChange
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.CategoryTheory.Comma.Over.Pullback
import Mathlib.Tactic.IrreducibleDef

/-!
# Base change of endomorphisms along a tower, and transport along isomorphisms of fields

For an abelian variety `A/K` and a tower `K → K' → L'`, `bcEndTower A K' L'` is the base change
`End(A_{K'}) → End(A_{L'})` into the direct base change `A_{L'}`, through the canonical
isomorphism `(A_{K'})_{L'} ≅ A_{L'}`. It is injective, bijective exactly when the base change
`End(A_{K'}) → End((A_{K'})_{L'})` is, transitive in towers, and compatible with the transport of
endomorphisms along an isomorphism `Ω₁ ≅ Ω₂` over `K'`. The comparison `A_{L'} → A_{K'}` over
`Spec L' → Spec K'` characterizes it: an endomorphism of `A_{L'}` is the base change of `f` exactly
when it is compatible with `f` through the comparison (`A_{L'}` is a pullback of `A_{K'}`).
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits
open scoped CategoryTheory.MonObj

namespace HDec.CMSerreTate

namespace BaseChangeEndTransportAux

theorem comp_eq_comp_left {C : Type*} [Category C] {X Y Z : C} (f : X ⟶ Y) {g h : Y ⟶ Z}
    (w : g = h) : f ≫ g = f ≫ h := by
  rw [w]

theorem comp_eq_comp_right {C : Type*} [Category C] {X Y Z : C} {f g : X ⟶ Y} (w : f = g)
    (h : Y ⟶ Z) : f ≫ h = g ≫ h := by
  rw [w]

theorem specMap_tower (K K' L' : Type) [Field K] [Field K'] [Field L'] [Algebra K K']
    [Algebra K' L'] [Algebra K L'] [IsScalarTower K K' L'] :
    Spec.map (CommRingCat.ofHom (algebraMap K' L')) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K K')) =
      Spec.map (CommRingCat.ofHom (algebraMap K L')) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

/-- The two-step base-change isomorphism of a group object (the shape of `ReductSplit.bcbcGrpIso`)
preserves the projection to the original object. -/
theorem grpComp_fst {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (hfg : f ≫ g = h)
    (p : Over.pullback (f ≫ g) = Over.pullback h) (𝒢 : Grp (Over Z)) :
    ((Grp.forget _).mapIso ((Functor.mapGrpCompIso.app 𝒢).symm ≪≫
        (Functor.mapGrpNatIso (Over.pullbackComp f g).symm).app 𝒢 ≪≫
        (Functor.mapGrpNatIso (eqToIso p)).app 𝒢)).hom.left ≫ pullback.fst 𝒢.X.hom h =
      pullback.fst (pullback.snd 𝒢.X.hom g) f ≫ pullback.fst 𝒢.X.hom g := by
  subst hfg
  have e := Over.pullbackComp_hom_app_left_fst_fst f g 𝒢.X
  have hx : ((Grp.forget _).mapIso ((Functor.mapGrpCompIso.app 𝒢).symm ≪≫
        (Functor.mapGrpNatIso (Over.pullbackComp f g).symm).app 𝒢 ≪≫
        (Functor.mapGrpNatIso (eqToIso p)).app 𝒢)).hom =
      𝟙 _ ≫ (Over.pullbackComp f g).inv.app 𝒢.X ≫ 𝟙 _ := rfl
  rw [hx, Category.id_comp, Category.comp_id, ← e]
  have h2 : ((Over.pullbackComp f g).inv.app 𝒢.X).left ≫
      ((Over.pullbackComp f g).hom.app 𝒢.X).left = 𝟙 _ := by
    rw [← Over.comp_left, ← NatTrans.comp_app, Iso.inv_hom_id]; rfl
  calc _ = (((Over.pullbackComp f g).inv.app 𝒢.X).left ≫
        ((Over.pullbackComp f g).hom.app 𝒢.X).left) ≫
        pullback.fst (pullback.snd 𝒢.X.hom g) f ≫ pullback.fst 𝒢.X.hom g := by
          simp only [Category.assoc]; rfl
    _ = _ := by rw [h2, Category.id_comp]

/-- `Over.pullback` on a morphism commutes with the first projection. -/
theorem pullback_map_left_fst {X Y : Scheme.{0}} (φ : X ⟶ Y) {W : Over Y} (u : W ⟶ W) :
    ((Over.pullback φ).map u).left ≫ pullback.fst W.hom φ = pullback.fst W.hom φ ≫ u.left := by
  simp only [Over.pullback_map_left, pullback.lift_fst]

end BaseChangeEndTransportAux

variable {K : Type} [Field K] (A : _root_.PkgI3.AbVar K)

/-- The comparison `A_{L'} → A_{K'}` over `Spec L' → Spec K'` (first projection unchanged). -/
noncomputable def bcCmp (K' L' : Type) [Field K'] [Field L'] [Algebra K K'] [Algebra K' L']
    [Algebra K L'] [IsScalarTower K K' L'] :
    (A.baseChange L').X.left ⟶ (A.baseChange K').X.left :=
  pullback.lift (pullback.fst A.X.hom (Spec.map (CommRingCat.ofHom (algebraMap K L'))))
    (pullback.snd A.X.hom (Spec.map (CommRingCat.ofHom (algebraMap K L'))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K' L')))
    ((pullback.condition (f := A.X.hom)
        (g := Spec.map (CommRingCat.ofHom (algebraMap K L')))).trans
      ((congrArg (pullback.snd A.X.hom (Spec.map (CommRingCat.ofHom (algebraMap K L'))) ≫ ·)
        (BaseChangeEndTransportAux.specMap_tower K K' L')).symm.trans
          (Category.assoc _ _ _).symm))

namespace BaseChangeEndTransportAux

theorem bcCmp_fst (K' L' : Type) [Field K'] [Field L'] [Algebra K K'] [Algebra K' L']
    [Algebra K L'] [IsScalarTower K K' L'] :
    bcCmp A K' L' ≫ pullback.fst A.X.hom (Spec.map (CommRingCat.ofHom (algebraMap K K'))) =
      pullback.fst A.X.hom (Spec.map (CommRingCat.ofHom (algebraMap K L'))) :=
  pullback.lift_fst _ _ _

theorem bcCmp_snd (K' L' : Type) [Field K'] [Field L'] [Algebra K K'] [Algebra K' L']
    [Algebra K L'] [IsScalarTower K K' L'] :
    bcCmp A K' L' ≫ pullback.snd A.X.hom (Spec.map (CommRingCat.ofHom (algebraMap K K'))) =
      pullback.snd A.X.hom (Spec.map (CommRingCat.ofHom (algebraMap K L'))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K' L')) :=
  pullback.lift_snd _ _ _

/-- A morphism of `A_{L'}` over `Spec L'` is determined by its composite with `bcCmp`. -/
theorem bcCmp_ext (K' L' : Type) [Field K'] [Field L'] [Algebra K K'] [Algebra K' L']
    [Algebra K L'] [IsScalarTower K K' L'] {u v : (A.baseChange L').X ⟶ (A.baseChange L').X}
    (h : u.left ≫ bcCmp A K' L' = v.left ≫ bcCmp A K' L') : u = v := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact Eq.trans (comp_eq_comp_left u.left (bcCmp_fst A K' L').symm)
      (Eq.trans (Category.assoc _ _ _).symm
        (Eq.trans (comp_eq_comp_right h _)
          (Eq.trans (Category.assoc _ _ _) (comp_eq_comp_left v.left (bcCmp_fst A K' L')))))
  · exact (Over.w u).trans (Over.w v).symm

/-- The comparisons compose along a tower `K → K' → L' → L''`. -/
theorem bcCmp_trans (K' L' L'' : Type) [Field K'] [Field L'] [Field L''] [Algebra K K']
    [Algebra K' L'] [Algebra K L'] [Algebra L' L''] [Algebra K' L''] [Algebra K L'']
    [IsScalarTower K K' L'] [IsScalarTower K L' L''] [IsScalarTower K K' L'']
    [IsScalarTower K' L' L''] :
    bcCmp A K' L'' = bcCmp A L' L'' ≫ bcCmp A K' L' := by
  apply pullback.hom_ext
  · exact Eq.trans (bcCmp_fst A K' L'')
      (Eq.trans (bcCmp_fst A L' L'').symm
        (Eq.trans (comp_eq_comp_left (bcCmp A L' L'') (bcCmp_fst A K' L').symm)
          (Category.assoc _ _ _).symm))
  · exact Eq.trans (bcCmp_snd A K' L'')
      (Eq.trans (comp_eq_comp_left _ (specMap_tower K' L' L'').symm)
        (Eq.trans (Category.assoc _ _ _).symm
          (Eq.trans (comp_eq_comp_right (bcCmp_snd A L' L'').symm _)
            (Eq.trans (Category.assoc _ _ _)
              (Eq.trans (comp_eq_comp_left (bcCmp A L' L'') (bcCmp_snd A K' L').symm)
                (Category.assoc _ _ _).symm)))))

/-- The canonical isomorphism `(A_{K'})_{L'} ≅ A_{L'}` composes the two first projections. -/
theorem bcbcIso_hom_fst (K' L' : Type) [Field K'] [Field L'] [Algebra K K'] [Algebra K' L']
    [Algebra K L'] [IsScalarTower K K' L'] :
    (_root_.ReductSplit.bcbcIso A K' L').hom.left ≫
        pullback.fst A.X.hom (Spec.map (CommRingCat.ofHom (algebraMap K L'))) =
      pullback.fst (pullback.snd A.X.hom (Spec.map (CommRingCat.ofHom (algebraMap K K'))))
          (Spec.map (CommRingCat.ofHom (algebraMap K' L'))) ≫
        pullback.fst A.X.hom (Spec.map (CommRingCat.ofHom (algebraMap K K'))) := by
  have p : Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K' L')) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K K'))) =
        Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L'))) := by
    rw [specMap_tower K K' L']
  have hI : _root_.ReductSplit.bcbcIso A K' L' = (Grp.forget _).mapIso
      ((Functor.mapGrpCompIso.app (Grp.mk A.X)).symm ≪≫
        (Functor.mapGrpNatIso (Over.pullbackComp (Spec.map (CommRingCat.ofHom (algebraMap K' L')))
          (Spec.map (CommRingCat.ofHom (algebraMap K K')))).symm).app (Grp.mk A.X) ≪≫
        (Functor.mapGrpNatIso (eqToIso p)).app (Grp.mk A.X)) := rfl
  rw [hI]
  exact grpComp_fst _ _ _ (specMap_tower K K' L') p (Grp.mk A.X)

theorem bcbcIso_hom_bcCmp (K' L' : Type) [Field K'] [Field L'] [Algebra K K'] [Algebra K' L']
    [Algebra K L'] [IsScalarTower K K' L'] :
    (_root_.ReductSplit.bcbcIso A K' L').hom.left ≫ bcCmp A K' L' =
      pullback.fst (pullback.snd A.X.hom (Spec.map (CommRingCat.ofHom (algebraMap K K'))))
        (Spec.map (CommRingCat.ofHom (algebraMap K' L'))) := by
  have hw : (_root_.ReductSplit.bcbcIso A K' L').hom.left ≫
      pullback.snd A.X.hom (Spec.map (CommRingCat.ofHom (algebraMap K L'))) =
        pullback.snd (pullback.snd A.X.hom (Spec.map (CommRingCat.ofHom (algebraMap K K'))))
          (Spec.map (CommRingCat.ofHom (algebraMap K' L'))) :=
    Over.w (_root_.ReductSplit.bcbcIso A K' L').hom
  apply pullback.hom_ext
  · exact Eq.trans (Category.assoc _ _ _)
      (Eq.trans (comp_eq_comp_left _ (bcCmp_fst A K' L')) (bcbcIso_hom_fst A K' L'))
  · exact Eq.trans (Category.assoc _ _ _)
      (Eq.trans (comp_eq_comp_left _ (bcCmp_snd A K' L'))
        (Eq.trans (Category.assoc _ _ _).symm
          (Eq.trans (comp_eq_comp_right hw _)
            (pullback.condition
              (f := pullback.snd A.X.hom (Spec.map (CommRingCat.ofHom (algebraMap K K'))))
              (g := Spec.map (CommRingCat.ofHom (algebraMap K' L')))).symm)))

/-- The canonical isomorphism `(A_{K'})_{L'} ≅ A_{L'}`, opaque to the kernel. -/
irreducible_def bcIsoW (K' L' : Type) [Field K'] [Field L'] [Algebra K K'] [Algebra K' L']
    [Algebra K L'] [IsScalarTower K K' L'] :
    ((A.baseChange K').baseChange L').X ≅ (A.baseChange L').X :=
  _root_.ReductSplit.bcbcIso A K' L'

theorem bcIsoW_isMonHom (K' L' : Type) [Field K'] [Field L'] [Algebra K K'] [Algebra K' L']
    [Algebra K L'] [IsScalarTower K K' L'] : IsMonHom (bcIsoW A K' L').hom := by
  rw [bcIsoW_def]
  exact _root_.ReductSplit.bcbcIso_isMonHom A K' L'

/-- Conjugation by the canonical isomorphism `(A_{K'})_{L'} ≅ A_{L'}`. -/
noncomputable def bcConj (K' L' : Type) [Field K'] [Field L'] [Algebra K K'] [Algebra K' L']
    [Algebra K L'] [IsScalarTower K K' L'] :
    _root_.PkgI3.AbVar.End ((A.baseChange K').baseChange L') ≃+*
      _root_.PkgI3.AbVar.End (A.baseChange L') :=
  haveI : IsMonHom (bcIsoW A K' L').hom := bcIsoW_isMonHom A K' L'
  haveI : IsMonHom (bcIsoW A K' L').inv := by
    infer_instance
  HDec.CMBranch.FibreSplit.endEquivOfIso
    (_root_.PkgI3.AbVar.Hom.mk' (bcIsoW A K' L').hom)
    (_root_.PkgI3.AbVar.Hom.mk' (bcIsoW A K' L').inv)
    (Iso.hom_inv_id _) (Iso.inv_hom_id _)

theorem bcConj_apply_hom (K' L' : Type) [Field K'] [Field L'] [Algebra K K'] [Algebra K' L']
    [Algebra K L'] [IsScalarTower K K' L']
    (u : _root_.PkgI3.AbVar.End ((A.baseChange K').baseChange L')) :
    (bcConj A K' L' u).hom = (bcIsoW A K' L').inv ≫ u.hom ≫ (bcIsoW A K' L').hom :=
  rfl

theorem endBC_apply_hom {K' : Type} [Field K'] (B : _root_.PkgI3.AbVar K') (L' : Type) [Field L']
    [Algebra K' L'] (g : _root_.PkgI3.AbVar.End B) :
    (HDec.G0ModField.KernelField.endBC B L' g).hom =
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K' L')))).map g.hom :=
  rfl

theorem endBC_eq_bcHom {K' : Type} [Field K'] (B : _root_.PkgI3.AbVar K') (L' : Type) [Field L']
    [Algebra K' L'] (g : _root_.PkgI3.AbVar.End B) :
    HDec.G0ModField.KernelField.endBC B L' g = _root_.ZInQ.Contrib.AVB1.bcHom L' B B g := by
  apply _root_.PkgI3.AbVar.Hom.ext'
  rw [endBC_apply_hom, _root_.ZInQ.Contrib.AVB1.bcHom_hom]

end BaseChangeEndTransportAux

/-- Base change of endomorphisms along `K → K' → L'`, into the DIRECT base change `A_{L'}`. -/
noncomputable def bcEndTower (K' L' : Type) [Field K'] [Field L'] [Algebra K K'] [Algebra K' L']
    [Algebra K L'] [IsScalarTower K K' L'] :
    _root_.PkgI3.AbVar.End (A.baseChange K') →+* _root_.PkgI3.AbVar.End (A.baseChange L') :=
  (BaseChangeEndTransportAux.bcConj A K' L').toRingHom.comp
    (HDec.G0ModField.KernelField.endBC (A.baseChange K') L')

namespace BaseChangeEndTransportAux

theorem bcEndTower_apply (K' L' : Type) [Field K'] [Field L'] [Algebra K K'] [Algebra K' L']
    [Algebra K L'] [IsScalarTower K K' L'] (f : _root_.PkgI3.AbVar.End (A.baseChange K')) :
    bcEndTower A K' L' f =
      bcConj A K' L' (HDec.G0ModField.KernelField.endBC (A.baseChange K') L' f) := by
  rw [bcEndTower, RingHom.comp_apply]
  rfl

end BaseChangeEndTransportAux

theorem bcEndTower_hom (K' L' : Type) [Field K'] [Field L'] [Algebra K K'] [Algebra K' L']
    [Algebra K L'] [IsScalarTower K K' L'] (f : _root_.PkgI3.AbVar.End (A.baseChange K')) :
    (bcEndTower A K' L' f).hom =
      (_root_.ReductSplit.bcbcIso A K' L').inv ≫
        (HDec.G0ModField.KernelField.endBC (A.baseChange K') L' f).hom ≫
          (_root_.ReductSplit.bcbcIso A K' L').hom := by
  rw [BaseChangeEndTransportAux.bcEndTower_apply, BaseChangeEndTransportAux.bcConj_apply_hom,
    BaseChangeEndTransportAux.bcIsoW_def]

namespace BaseChangeEndTransportAux

/-- `bcEndTower A K' L' f` is compatible with `f` through `bcCmp`. -/
theorem bcEndTower_comp_bcCmp (K' L' : Type) [Field K'] [Field L'] [Algebra K K']
    [Algebra K' L'] [Algebra K L'] [IsScalarTower K K' L']
    (f : _root_.PkgI3.AbVar.End (A.baseChange K')) :
    (bcEndTower A K' L' f).hom.left ≫ bcCmp A K' L' = bcCmp A K' L' ≫ f.hom.left := by
  have h1 := bcbcIso_hom_bcCmp A K' L'
  have hinv : (_root_.ReductSplit.bcbcIso A K' L').inv.left ≫
      (_root_.ReductSplit.bcbcIso A K' L').hom.left = 𝟙 _ :=
    (Over.comp_left _ _ _ _ _).symm.trans
      ((congrArg (fun t => t.left) (_root_.ReductSplit.bcbcIso A K' L').inv_hom_id).trans
        (Over.id_left _))
  have h2 : (_root_.ReductSplit.bcbcIso A K' L').inv.left ≫
      pullback.fst (pullback.snd A.X.hom (Spec.map (CommRingCat.ofHom (algebraMap K K'))))
        (Spec.map (CommRingCat.ofHom (algebraMap K' L'))) = bcCmp A K' L' :=
    Eq.trans (comp_eq_comp_left _ h1.symm)
      (Eq.trans (Category.assoc _ _ _).symm
        (Eq.trans (comp_eq_comp_right hinv _) (Category.id_comp _)))
  have h3 : ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K' L')))).map f.hom).left ≫
      pullback.fst (pullback.snd A.X.hom (Spec.map (CommRingCat.ofHom (algebraMap K K'))))
        (Spec.map (CommRingCat.ofHom (algebraMap K' L'))) =
      pullback.fst (pullback.snd A.X.hom (Spec.map (CommRingCat.ofHom (algebraMap K K'))))
        (Spec.map (CommRingCat.ofHom (algebraMap K' L'))) ≫ f.hom.left :=
    pullback_map_left_fst (Spec.map (CommRingCat.ofHom (algebraMap K' L'))) f.hom
  have h0 : (bcEndTower A K' L' f).hom.left = (_root_.ReductSplit.bcbcIso A K' L').inv.left ≫
      (((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K' L')))).map f.hom).left ≫
        (_root_.ReductSplit.bcbcIso A K' L').hom.left) :=
    (congrArg (fun t => t.left) (bcEndTower_hom A K' L' f)).trans
      ((Over.comp_left _ _ _ _ _).trans (comp_eq_comp_left _ (Over.comp_left _ _ _ _ _)))
  exact Eq.trans (comp_eq_comp_right h0 _)
    (Eq.trans (Category.assoc _ _ _)
      (Eq.trans (comp_eq_comp_left _ (Category.assoc _ _ _))
        (Eq.trans (comp_eq_comp_left _ (comp_eq_comp_left _ h1))
          (Eq.trans (comp_eq_comp_left _ h3)
            (Eq.trans (Category.assoc _ _ _).symm (comp_eq_comp_right h2 _))))))

/-- `cσ` intertwines the comparisons, for an isomorphism `Ω₁ ≅ Ω₂` over `K'`. -/
theorem cσ_bcCmp (K' Ω₁ Ω₂ : Type) [Field K'] [Field Ω₁] [Field Ω₂] [Algebra K K']
    [Algebra K' Ω₁] [Algebra K Ω₁] [IsScalarTower K K' Ω₁] [Algebra K' Ω₂] [Algebra K Ω₂]
    [IsScalarTower K K' Ω₂] (ψ : Ω₁ ≃ₐ[K'] Ω₂) :
    HDec.CMBranch.FibreSplit.cσ A (ψ.restrictScalars K) ≫ bcCmp A K' Ω₁ = bcCmp A K' Ω₂ := by
  have hcfst : HDec.CMBranch.FibreSplit.cσ A (ψ.restrictScalars K) ≫
      pullback.fst A.X.hom (Spec.map (CommRingCat.ofHom (algebraMap K Ω₁))) =
        pullback.fst A.X.hom (Spec.map (CommRingCat.ofHom (algebraMap K Ω₂))) :=
    pullback.lift_fst _ _ _
  have hcsnd : HDec.CMBranch.FibreSplit.cσ A (ψ.restrictScalars K) ≫
      pullback.snd A.X.hom (Spec.map (CommRingCat.ofHom (algebraMap K Ω₁))) =
        pullback.snd A.X.hom (Spec.map (CommRingCat.ofHom (algebraMap K Ω₂))) ≫
          Spec.map (CommRingCat.ofHom
            (((ψ.restrictScalars K : Ω₁ ≃ₐ[K] Ω₂) : Ω₁ ≃+* Ω₂) : Ω₁ →+* Ω₂)) :=
    pullback.lift_snd _ _ _
  have hσ : Spec.map (CommRingCat.ofHom
      (((ψ.restrictScalars K : Ω₁ ≃ₐ[K] Ω₂) : Ω₁ ≃+* Ω₂) : Ω₁ →+* Ω₂)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K' Ω₁)) =
      Spec.map (CommRingCat.ofHom (algebraMap K' Ω₂)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    exact ψ.commutes x
  apply pullback.hom_ext
  · exact Eq.trans (Category.assoc _ _ _)
      (Eq.trans (comp_eq_comp_left _ (bcCmp_fst A K' Ω₁))
        (Eq.trans hcfst (bcCmp_fst A K' Ω₂).symm))
  · exact Eq.trans (Category.assoc _ _ _)
      (Eq.trans (comp_eq_comp_left _ (bcCmp_snd A K' Ω₁))
        (Eq.trans (Category.assoc _ _ _).symm
          (Eq.trans (comp_eq_comp_right hcsnd _)
            (Eq.trans (Category.assoc _ _ _)
              (Eq.trans (comp_eq_comp_left _ hσ) (bcCmp_snd A K' Ω₂).symm)))))

end BaseChangeEndTransportAux

theorem bcEndTower_injective (K' L' : Type) [Field K'] [Field L'] [Algebra K K'] [Algebra K' L']
    [Algebra K L'] [IsScalarTower K K' L'] : Function.Injective (bcEndTower A K' L') := by
  intro f g h
  apply _root_.ZInQ.Contrib.AVB1.bcHom_injective (L := L') (A.baseChange K') (A.baseChange K')
  apply (BaseChangeEndTransportAux.bcConj A K' L').injective
  rw [← BaseChangeEndTransportAux.endBC_eq_bcHom, ← BaseChangeEndTransportAux.endBC_eq_bcHom,
    ← BaseChangeEndTransportAux.bcEndTower_apply, ← BaseChangeEndTransportAux.bcEndTower_apply]
  exact h

theorem bijective_bcHom_iff_bcEndTower (K' L' : Type) [Field K'] [Field L'] [Algebra K K']
    [Algebra K' L'] [Algebra K L'] [IsScalarTower K K' L'] :
    Function.Bijective (_root_.ZInQ.Contrib.AVB1.bcHom L' (A.baseChange K') (A.baseChange K')) ↔
      Function.Bijective (bcEndTower A K' L') := by
  have h : ⇑(bcEndTower A K' L') = ⇑(BaseChangeEndTransportAux.bcConj A K' L') ∘
      ⇑(_root_.ZInQ.Contrib.AVB1.bcHom L' (A.baseChange K') (A.baseChange K')) := by
    funext f
    rw [Function.comp_apply, BaseChangeEndTransportAux.bcEndTower_apply,
      BaseChangeEndTransportAux.endBC_eq_bcHom]
  rw [h, Function.Bijective.of_comp_iff' (BaseChangeEndTransportAux.bcConj A K' L').bijective]

theorem bcEndTower_eq_of_comp_bcCmp (K' L' : Type) [Field K'] [Field L'] [Algebra K K']
    [Algebra K' L'] [Algebra K L'] [IsScalarTower K K' L']
    (f : _root_.PkgI3.AbVar.End (A.baseChange K')) (g : _root_.PkgI3.AbVar.End (A.baseChange L'))
    (h : g.hom.left ≫ bcCmp A K' L' = bcCmp A K' L' ≫ f.hom.left) :
    bcEndTower A K' L' f = g := by
  apply _root_.PkgI3.AbVar.Hom.ext'
  apply BaseChangeEndTransportAux.bcCmp_ext A K' L'
  exact (BaseChangeEndTransportAux.bcEndTower_comp_bcCmp A K' L' f).trans h.symm

theorem bcEndTower_comp (K' L' L'' : Type) [Field K'] [Field L'] [Field L''] [Algebra K K']
    [Algebra K' L'] [Algebra K L'] [Algebra L' L''] [Algebra K' L''] [Algebra K L'']
    [IsScalarTower K K' L'] [IsScalarTower K L' L''] [IsScalarTower K K' L'']
    [IsScalarTower K' L' L''] :
    (bcEndTower A L' L'').comp (bcEndTower A K' L') = bcEndTower A K' L'' := by
  apply RingHom.ext
  intro f
  rw [RingHom.comp_apply]
  symm
  apply bcEndTower_eq_of_comp_bcCmp
  exact Eq.trans (BaseChangeEndTransportAux.comp_eq_comp_left _
      (BaseChangeEndTransportAux.bcCmp_trans A K' L' L''))
    (Eq.trans (Category.assoc _ _ _).symm
      (Eq.trans (BaseChangeEndTransportAux.comp_eq_comp_right
          (BaseChangeEndTransportAux.bcEndTower_comp_bcCmp A L' L'' (bcEndTower A K' L' f)) _)
        (Eq.trans (Category.assoc _ _ _)
          (Eq.trans (BaseChangeEndTransportAux.comp_eq_comp_left _
              (BaseChangeEndTransportAux.bcEndTower_comp_bcCmp A K' L' f))
            (Eq.trans (Category.assoc _ _ _).symm
              (BaseChangeEndTransportAux.comp_eq_comp_right
                (BaseChangeEndTransportAux.bcCmp_trans A K' L' L'').symm _))))))

theorem trEquiv_comp_bcEndTower (K' Ω₁ Ω₂ : Type) [Field K'] [Field Ω₁] [Field Ω₂] [Algebra K K']
    [Algebra K' Ω₁] [Algebra K Ω₁] [IsScalarTower K K' Ω₁] [Algebra K' Ω₂] [Algebra K Ω₂]
    [IsScalarTower K K' Ω₂] (ψ : Ω₁ ≃ₐ[K'] Ω₂) :
    (HDec.CMBranch.FibreSplit.trEquiv (X := A) (σ := ψ.restrictScalars K)).toRingHom.comp
        (bcEndTower A K' Ω₁) = bcEndTower A K' Ω₂ := by
  apply RingHom.ext
  intro f
  rw [RingHom.comp_apply]
  symm
  apply bcEndTower_eq_of_comp_bcCmp
  have ht : ((HDec.CMBranch.FibreSplit.trEquiv (X := A) (σ := ψ.restrictScalars K)).toRingHom
      (bcEndTower A K' Ω₁ f)).hom.left ≫ HDec.CMBranch.FibreSplit.cσ A (ψ.restrictScalars K) =
        HDec.CMBranch.FibreSplit.cσ A (ψ.restrictScalars K) ≫ (bcEndTower A K' Ω₁ f).hom.left :=
    HDec.CMBranch.FibreSplit.tr_left (X := A) (σ := ψ.restrictScalars K) (bcEndTower A K' Ω₁ f)
  exact Eq.trans (BaseChangeEndTransportAux.comp_eq_comp_left _
      (BaseChangeEndTransportAux.cσ_bcCmp A K' Ω₁ Ω₂ ψ).symm)
    (Eq.trans (Category.assoc _ _ _).symm
      (Eq.trans (BaseChangeEndTransportAux.comp_eq_comp_right ht _)
        (Eq.trans (Category.assoc _ _ _)
          (Eq.trans (BaseChangeEndTransportAux.comp_eq_comp_left _
              (BaseChangeEndTransportAux.bcEndTower_comp_bcCmp A K' Ω₁ f))
            (Eq.trans (Category.assoc _ _ _).symm
              (BaseChangeEndTransportAux.comp_eq_comp_right
                (BaseChangeEndTransportAux.cσ_bcCmp A K' Ω₁ Ω₂ ψ) _))))))

end HDec.CMSerreTate
