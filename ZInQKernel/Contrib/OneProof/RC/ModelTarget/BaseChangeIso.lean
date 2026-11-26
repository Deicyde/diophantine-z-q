import ZInQKernel.Contrib.OneProof.RC.ModelTarget.BaseChangeInv
import ZInQKernel.Contrib.OneProof.RC.ModelTarget.GroupLaw

/-! The base change of the projective cubic along `ψ : R → S` is the projective cubic of
the mapped equation: the two comparison maps are mutually inverse, as checked on field
points (both sources are reduced and both targets separated). The isomorphism is the
identity in homogeneous coordinates. On the spot (c). -/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits WeierstrassCurve
open scoped WeierstrassCurve.Projective

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace ZInQ.Manuscript.RC.ModelTarget

variable {R S : Type} [CommRing R] [CommRing S] (W : WeierstrassCurve R) (ψ : R →+* S)

theorem fieldValue_eq_invVec {F : Type} [Field F] (g : S →+* F)
    (p : Spec (.of F) ⟶ Proj (W.map ψ).toProjective.grading)
    (hp : p ≫ projStructure (W.map ψ) = Spec.map (CommRingCat.ofHom g)) :
    fieldValue (W.map ψ) g p hp =
      Projective.Point.toAffine ((W.map ψ).toProjective.map g) (invVec W ψ p) := by
  have hg : pointRing (projStructure (W.map ψ)) p = g := by
    have := (pointRing_spec (projStructure (W.map ψ)) p).symm.trans hp
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective this)
  obtain ⟨hv, i, hi, e⟩ := invVec_spec W ψ p
  have hv' : ((W.map ψ).toProjective.map g).Equation (invVec W ψ p) := hg ▸ hv
  exact fieldValue_eq (W.map ψ) g p hp _ hv' i hi (e.trans (chartMorphism_ring_congr _ hg _ _ _ _ _))

theorem fieldValue_eq_bcVec {F : Type} [Field F] (g : S →+* F) (p : Spec (.of F) ⟶ baseChangeScheme W ψ)
    (hp : p ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom g)) :
    fieldValue W (g.comp ψ) (p ≫ pullback.fst _ _) (fst_structure W ψ g p hp) =
      Projective.Point.toAffine (W.toProjective.map (g.comp ψ)) (bcVec W ψ g p hp) := by
  obtain ⟨hv, i, hi, e⟩ := bcVec_spec W ψ g p hp
  exact fieldValue_eq W (g.comp ψ) _ _ _ hv i hi e

variable [W.IsElliptic] [(W.map ψ).IsElliptic] [IsReduced (baseChangeScheme W ψ)]
  [IsReduced (Proj (W.map ψ).toProjective.grading)]

/-- The comparison `Proj W ×_R S → Proj (W.map ψ)` over `S`. -/
def bcHom : (Over.pullback (Spec.map (CommRingCat.ofHom ψ))).obj (cubic W) ⟶ cubic (W.map ψ) :=
  Over.homMk (exists_baseChangeHom W ψ).choose (exists_baseChangeHom W ψ).choose_spec.choose

theorem bcHom_value {F : Type} [Field F] (g : S →+* F) (p : Spec (.of F) ⟶ baseChangeScheme W ψ)
    (hp : p ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom g)) :
    fieldValue (W.map ψ) g (p ≫ (bcHom W ψ).left)
        (comp_structure (W.map ψ) (exists_baseChangeHom W ψ).choose_spec.choose hp) =
      Projective.Point.toAffine ((W.map ψ).toProjective.map g) (bcVec W ψ g p hp) :=
  (exists_baseChangeHom W ψ).choose_spec.choose_spec F g p hp

/-- The comparison `Proj (W.map ψ) → Proj W ×_R S` over `S`. -/
def bcInv : cubic (W.map ψ) ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom ψ))).obj (cubic W) :=
  Over.homMk (pullback.lift (exists_baseChangeInvHom W ψ).choose (projStructure (W.map ψ))
    (exists_baseChangeInvHom W ψ).choose_spec.choose) (pullback.lift_snd _ _ _)

theorem bcInv_fst : (bcInv W ψ).left ≫ pullback.fst _ _ = (exists_baseChangeInvHom W ψ).choose :=
  pullback.lift_fst _ _ _

private theorem equiv_nonsingular {F : Type} [Field F] (g : R →+* F) {v v' : Fin 3 → F}
    (hv : (W.toProjective.map g).Equation v) (hv' : (W.toProjective.map g).Equation v')
    {i j : Fin 3} (hi : IsUnit (v i)) (hj : IsUnit (v' j))
    (h : Projective.Point.toAffine (W.toProjective.map g) v =
      Projective.Point.toAffine (W.toProjective.map g) v') : v ≈ v' :=
  equiv_of_toAffine_eq _ (nonsingular_of_unit_coord W g v hv i hi.ne_zero)
    (nonsingular_of_unit_coord W g v' hv' j hj.ne_zero) h

theorem bcInv_hom : bcInv W ψ ≫ bcHom W ψ = 𝟙 _ := by
  haveI : IsReduced (cubic (W.map ψ)).left :=
    inferInstanceAs (IsReduced (Proj (W.map ψ).toProjective.grading))
  apply cubicHom_ext (W.map ψ)
  intro F _ g p
  rw [Category.comp_id]
  have hP : (p ≫ bcInv W ψ).left ≫ pullback.snd (projStructure W) (Spec.map (CommRingCat.ofHom ψ)) =
      Spec.map (CommRingCat.ofHom g) := Over.w (p ≫ bcInv W ψ)
  change fieldValue (W.map ψ) g ((p ≫ bcInv W ψ).left ≫ (bcHom W ψ).left) _ = fieldValue _ g p.left _
  rw [bcHom_value W ψ g _ hP, fieldValue_eq_invVec W ψ g p.left (Over.w p)]
  apply Projective.Point.toAffine_of_equiv
  -- compare in `Proj W` over `g.comp ψ`
  have hw : p.left ≫ projStructure (W.map ψ) = Spec.map (CommRingCat.ofHom g) := Over.w p
  have hp' : p.left ≫ structR W ψ = Spec.map (CommRingCat.ofHom (g.comp ψ)) := by
    rw [structR, ← Category.assoc, hw, ← Spec.map_comp, CommRingCat.ofHom_comp]
  have e1 := (exists_baseChangeInvHom W ψ).choose_spec.choose_spec F (g.comp ψ) p.left hp'
  have e2 := fieldValue_eq_bcVec W ψ g _ hP
  have e3 : fieldValue W (g.comp ψ) ((p ≫ bcInv W ψ).left ≫ pullback.fst _ _) (fst_structure W ψ g _ hP) =
      fieldValue W (g.comp ψ) (p.left ≫ (exists_baseChangeInvHom W ψ).choose)
        (comp_structure W (exists_baseChangeInvHom W ψ).choose_spec.choose hp') :=
    fieldValue_congr W _ (by rw [Over.comp_left, Category.assoc, bcInv_fst]) _ _
  obtain ⟨hb, i, hi, -⟩ := bcVec_spec W ψ g _ hP
  obtain ⟨hv, j, hj, -⟩ := invVec_spec W ψ p.left
  have hg : pointRing (projStructure (W.map ψ)) p.left = g := by
    have := (pointRing_spec (projStructure (W.map ψ)) p.left).symm.trans (Over.w p)
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective this)
  have hv' : (W.toProjective.map (g.comp ψ)).Equation (invVec W ψ p.left) := by
    have := hg ▸ hv
    exact this
  exact equiv_nonsingular W (g.comp ψ) hb hv' hi hj (e2.symm.trans (e3.trans e1))

theorem bcHom_inv : bcHom W ψ ≫ bcInv W ψ = 𝟙 _ := by
  haveI : IsReduced ((Over.pullback (Spec.map (CommRingCat.ofHom ψ))).obj (cubic W)).left :=
    inferInstanceAs (IsReduced (baseChangeScheme W ψ))
  have hbw : (bcHom W ψ).left ≫ projStructure (W.map ψ) =
      pullback.snd (projStructure W) (Spec.map (CommRingCat.ofHom ψ)) := Over.w (bcHom W ψ)
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · rw [Over.comp_left, Category.assoc, bcInv_fst, Over.id_left, Category.id_comp]
    have hs : ((bcHom W ψ).left ≫ (exists_baseChangeInvHom W ψ).choose) ≫ projStructure W =
        pullback.fst (projStructure W) (Spec.map (CommRingCat.ofHom ψ)) ≫ projStructure W := by
      rw [Category.assoc, (exists_baseChangeInvHom W ψ).choose_spec.choose, structR,
        ← Category.assoc, hbw, pullback.condition]
    apply eq_of_fieldValues W _ _ _ hs rfl
    intro F _ gR p hp
    let gS := pointRing (pullback.snd (projStructure W) (Spec.map (CommRingCat.ofHom ψ))) p
    have hpS := pointRing_spec (pullback.snd (projStructure W) (Spec.map (CommRingCat.ofHom ψ))) p
    have hgR : gR = gS.comp ψ := by
      rw [pullback.condition, ← Category.assoc, hpS, ← Spec.map_comp] at hp
      exact (congrArg CommRingCat.Hom.hom (Spec.map_injective hp)).symm
    subst hgR
    have hα : (p ≫ (bcHom W ψ).left) ≫ projStructure (W.map ψ) = Spec.map (CommRingCat.ofHom gS) := by
      rw [Category.assoc, hbw]; exact hpS
    have hαR : (p ≫ (bcHom W ψ).left) ≫ structR W ψ = Spec.map (CommRingCat.ofHom (gS.comp ψ)) := by
      rw [structR, ← Category.assoc, hα, ← Spec.map_comp, CommRingCat.ofHom_comp]
    have e1 := (exists_baseChangeInvHom W ψ).choose_spec.choose_spec F (gS.comp ψ) _ hαR
    have e2 := fieldValue_eq_bcVec W ψ gS p hpS
    have e3 := bcHom_value W ψ gS p hpS
    have e4 := fieldValue_eq_invVec W ψ gS _ hα
    calc _ = fieldValue W (gS.comp ψ) ((p ≫ (bcHom W ψ).left) ≫ (exists_baseChangeInvHom W ψ).choose)
          (comp_structure W (exists_baseChangeInvHom W ψ).choose_spec.choose hαR) :=
          fieldValue_congr W _ (Category.assoc _ _ _).symm _ _
      _ = _ := e1
      _ = Projective.Point.toAffine (W.toProjective.map (gS.comp ψ)) (bcVec W ψ gS p hpS) := by
          apply Projective.Point.toAffine_of_equiv
          obtain ⟨hb, i, hi, -⟩ := bcVec_spec W ψ gS p hpS
          obtain ⟨hv, j, hj, -⟩ := invVec_spec W ψ (p ≫ (bcHom W ψ).left)
          have hg : pointRing (projStructure (W.map ψ)) (p ≫ (bcHom W ψ).left) = gS := by
            have := (pointRing_spec (projStructure (W.map ψ)) _).symm.trans hα
            exact congrArg CommRingCat.Hom.hom (Spec.map_injective this)
          have hv' : ((W.map ψ).toProjective.map gS).Equation (invVec W ψ (p ≫ (bcHom W ψ).left)) :=
            hg ▸ hv
          have hb' : ((W.map ψ).toProjective.map gS).Equation (bcVec W ψ gS p hpS) := hb
          exact equiv_of_toAffine_eq _ (nonsingular_of_unit_coord (W.map ψ) gS _ hv' j hj.ne_zero)
            (nonsingular_of_unit_coord (W.map ψ) gS _ hb' i hi.ne_zero) (e4.symm.trans e3)
      _ = _ := e2.symm
  · rw [Over.comp_left, Category.assoc, Over.id_left, Category.id_comp]
    change _ ≫ (pullback.lift _ _ _ ≫ pullback.snd _ _) = _
    rw [pullback.lift_snd]
    exact hbw

/-- **Base change of the projective cubic.** `Proj W ×_R S ≅ Proj (W.map ψ)` over `S`, the
identity in homogeneous coordinates. -/
def bcIso : (Over.pullback (Spec.map (CommRingCat.ofHom ψ))).obj (cubic W) ≅ cubic (W.map ψ) where
  hom := bcHom W ψ
  inv := bcInv W ψ
  hom_inv_id := bcHom_inv W ψ
  inv_hom_id := bcInv_hom W ψ

#print axioms fieldValue_eq_invVec
#print axioms bcInv_hom
#print axioms bcHom_inv
#print axioms bcIso

end ZInQ.Manuscript.RC.ModelTarget
