import ZInQKernel.Contrib.OneProof.ColmezTiltIso.BdR

/-!
# The Galois action on Colmez's `B_dR^+` and `B_dR`

The componentwise action `galAct p σ` of `σ ∈ G_{ℚ_p}` on `R` gives `WittVector.map` on `W(R)`, then
`colmezLocAct p σ` on `W(R)[1/p]` (universal property of the localization), then
`colmezBdRPlusAct p σ` on `ColmezBdRPlus 𝓞_ℂ_[p] p = lim← W(R)[1/p]/(Ker θ)^n` (the map of adic
completions, level by level), and `colmezBdRAct p σ` on its fraction field (universal property).

* `colmezBdRPlusAct_of`: on the image of `w ∈ W(R)`, the action is `WittVector.map (galAct p σ)`;
  `colmezBdRPlusAct_inv_apply`: `σ⁻¹` undoes `σ`.
* **`colmezBdRPlusEquiv_act`**: `colmezBdRPlusEquiv` intertwines `colmezBdRPlusAct p σ` with the
  tree's action `DR.bdrPlusMap p (oAct p σ)` on `B_dR^+`, on all of `ColmezBdRPlus`.
* **`colmezBdREquiv_act`**: `colmezBdREquiv` intertwines `colmezBdRAct p σ` with the tree's action
  `bdrAct p σ` on `B_dR`, on all of the fraction field.
-/

namespace ZInQ.Contrib.ColmezTiltIso

set_option linter.unusedSectionVars false

open Ideal WittVector ZInQ.Contrib.G9 ZInQ.Contrib.G9.PkgI4

section Adic

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]

theorem adicMap_comp (J₁ : Ideal A) (J₂ : Ideal B) (J₃ : Ideal C) (f : A →+* B) (g : B →+* C)
    (h₁ : J₁ ≤ J₂.comap f) (h₂ : J₂ ≤ J₃.comap g) (h₃ : J₁ ≤ J₃.comap (g.comp f))
    (x : AdicCompletion J₁ A) :
    DR.adicMap J₂ J₃ g h₂ (DR.adicMap J₁ J₂ f h₁ x) = DR.adicMap J₁ J₃ (g.comp f) h₃ x := by
  refine AdicCompletion.ext_evalₐ fun n => ?_
  rw [DR.adicMap_evalₐ, DR.adicMap_evalₐ]
  simp only [DR.adicMapAux, RingHom.comp_apply]
  erw [DR.adicMap_evalₐ]
  simp only [DR.adicMapAux, RingHom.comp_apply]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (I := J₁ ^ n) (AdicCompletion.evalₐ J₁ n x)
  erw [← ha]
  simp only [Ideal.quotientMap_mk, RingHom.comp_apply]

theorem adicMap_id (J : Ideal A) (h : J ≤ J.comap (RingHom.id A)) (x : AdicCompletion J A) :
    DR.adicMap J J (RingHom.id A) h x = x := by
  refine AdicCompletion.ext_evalₐ fun n => ?_
  rw [DR.adicMap_evalₐ]
  simp only [DR.adicMapAux, RingHom.comp_apply]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (I := J ^ n) (AdicCompletion.evalₐ J n x)
  erw [← ha]
  simp only [Ideal.quotientMap_mk, RingHom.id_apply]

theorem adicMap_eq_self (J : Ideal A) {g : A →+* A} (e : g = RingHom.id A)
    (h : J ≤ J.comap g) (x : AdicCompletion J A) : DR.adicMap J J g h x = x := by
  subst e
  exact adicMap_id J h x

theorem adicMap_congr (J : Ideal A) (J' : Ideal B) {g g' : A →+* B} (e : g = g')
    (h : J ≤ J'.comap g) (h' : J ≤ J'.comap g') (x : AdicCompletion J A) :
    DR.adicMap J J' g h x = DR.adicMap J J' g' h' x := by
  subst e
  rfl

end Adic

variable (p : ℕ) [Fact p.Prime]

/-- The tree's two names for `B_dR` (`G9/KerTheta.lean`, `G9/I4Layer.lean`) are the same type. -/
theorem bdrKer_BdR_eq : BdrKer.BdR 𝓞_ℂ_[p] p = BdR p :=
  rfl

/-- The two canonical maps `W(O♭)[1/p] → B_dR^+` of the tree agree. -/
theorem ofLoc_eq_ofPlus (y : Localization.Away (p : WittVector p (PreTilt 𝓞_ℂ_[p] p))) :
    ofLoc p y = BdrKer.ofPlus 𝓞_ℂ_[p] p y := by
  rw [ofLoc]
  erw [AdicCompletion.algebraMap_apply]
  rfl

theorem galAct_inv_apply (σ : GQp p) (x : ColmezR 𝓞_ℂ_[p] p) :
    galAct p σ⁻¹ (galAct p σ x) = x := by
  ext n
  simp only [galAct, ColmezR.mapHom_seq, oAct_inv_apply]

/-- `σ` on `W(R)[1/p]`: the localization of `WittVector.map (galAct p σ)`. -/
noncomputable def colmezLocAct (σ : GQp p) :
    Localization.Away (p : WittVector p (ColmezR 𝓞_ℂ_[p] p)) →+*
      Localization.Away (p : WittVector p (ColmezR 𝓞_ℂ_[p] p)) :=
  Localization.awayLift ((algebraMap _ _).comp (WittVector.map (galAct p σ))) _ (by
    rw [RingHom.comp_apply, map_natCast]
    exact IsLocalization.Away.algebraMap_isUnit _)

theorem colmezLocAct_algebraMap (σ : GQp p) (w : WittVector p (ColmezR 𝓞_ℂ_[p] p)) :
    colmezLocAct p σ (algebraMap _ _ w) = algebraMap _ _ (WittVector.map (galAct p σ) w) := by
  simp only [colmezLocAct, Localization.awayLift, IsLocalization.Away.lift, IsLocalization.lift_eq,
    RingHom.comp_apply]

/-- `locEquiv` intertwines `colmezLocAct p σ` with the tree's `DR.locMap p (oAct p σ)`. -/
theorem locEquiv_comp_colmezLocAct (σ : GQp p) :
    (locEquiv (O := 𝓞_ℂ_[p]) (p := p)).toRingHom.comp (colmezLocAct p σ) =
      (DR.locMap p (oAct p σ)).comp locEquiv.toRingHom := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (p : WittVector p (ColmezR 𝓞_ℂ_[p] p)))
  ext w
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    colmezLocAct_algebraMap, locEquiv_algebraMap, locMap_algebraMap, wittEquiv_map_galAct]

theorem colmezLocAct_inv_comp (σ : GQp p) :
    (colmezLocAct p σ⁻¹).comp (colmezLocAct p σ) = RingHom.id _ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (p : WittVector p (ColmezR 𝓞_ℂ_[p] p)))
  ext w
  simp only [RingHom.comp_apply, RingHom.id_apply, colmezLocAct_algebraMap]
  congr 1
  refine WittVector.ext fun n => ?_
  rw [map_coeff, map_coeff, galAct_inv_apply]

theorem ker_le_comap_colmezLocAct (σ : GQp p) :
    RingHom.ker (colmezThetaInvertP 𝓞_ℂ_[p] p) ≤
      (RingHom.ker (colmezThetaInvertP 𝓞_ℂ_[p] p)).comap (colmezLocAct p σ) := by
  intro x hx
  rw [ker_colmezThetaInvertP, Ideal.mem_comap] at hx
  rw [Ideal.mem_comap, ker_colmezThetaInvertP, Ideal.mem_comap]
  have h := DR.ker_le_comap_locMap p (oAct p σ) hx
  rw [Ideal.mem_comap] at h
  have e := congrArg (fun φ => φ x) (locEquiv_comp_colmezLocAct p σ)
  simp only [RingHom.comp_apply] at e
  rw [e]
  exact h

/-- **The action of `σ ∈ G_{ℚ_p}` on Colmez's `B_dR^+`**: the map of adic completions induced by
`colmezLocAct p σ` on `W(R)[1/p]`. -/
noncomputable def colmezBdRPlusAct (σ : GQp p) :
    ColmezBdRPlus 𝓞_ℂ_[p] p →+* ColmezBdRPlus 𝓞_ℂ_[p] p :=
  DR.adicMap _ _ (colmezLocAct p σ) (ker_le_comap_colmezLocAct p σ)

/-- On the image of `W(R)`, the action is `WittVector.map (galAct p σ)`. -/
theorem colmezBdRPlusAct_of (σ : GQp p) (w : WittVector p (ColmezR 𝓞_ℂ_[p] p)) :
    colmezBdRPlusAct p σ (AdicCompletion.of _ _ (algebraMap _ _ w)) =
      AdicCompletion.of _ _ (algebraMap _ _ (WittVector.map (galAct p σ) w)) := by
  rw [colmezBdRPlusAct, DR.adicMap_of, colmezLocAct_algebraMap]

/-- **`colmezBdRPlusEquiv` intertwines the actions on `B_dR^+`**: Colmez's `colmezBdRPlusAct p σ`
and the tree's `DR.bdrPlusMap p (oAct p σ)`, on all of `ColmezBdRPlus`. -/
theorem colmezBdRPlusEquiv_act (σ : GQp p) (x : ColmezBdRPlus 𝓞_ℂ_[p] p) :
    colmezBdRPlusEquiv (colmezBdRPlusAct p σ x) =
      DR.bdrPlusMap p (oAct p σ) (colmezBdRPlusEquiv x) := by
  change DR.adicMap _ _ locEquiv.toRingHom _ (DR.adicMap _ _ (colmezLocAct p σ) _ x) =
    DR.adicMap _ _ (DR.locMap p (oAct p σ)) _ (DR.adicMap _ _ locEquiv.toRingHom _ x)
  rw [adicMap_comp, adicMap_comp]
  · exact adicMap_congr _ _ (locEquiv_comp_colmezLocAct p σ) _ _ x
  · exact fun y hy => DR.ker_le_comap_locMap p (oAct p σ)
      ((ker_colmezThetaInvertP (O := 𝓞_ℂ_[p]) (p := p)).le hy)
  · intro y hy
    have h := ker_le_comap_colmezLocAct p σ hy
    rw [Ideal.mem_comap, ker_colmezThetaInvertP, Ideal.mem_comap] at h
    exact h

theorem colmezBdRPlusAct_inv_apply (σ : GQp p) (x : ColmezBdRPlus 𝓞_ℂ_[p] p) :
    colmezBdRPlusAct p σ⁻¹ (colmezBdRPlusAct p σ x) = x := by
  rw [colmezBdRPlusAct, colmezBdRPlusAct, adicMap_comp]
  · exact adicMap_eq_self _ (colmezLocAct_inv_comp p σ) _ x
  · intro y hy
    have h := ker_le_comap_colmezLocAct p σ hy
    exact ker_le_comap_colmezLocAct p σ⁻¹ h

/-- The action on `B_dR^+` as a ring automorphism (inverse: the action of `σ⁻¹`). -/
noncomputable def colmezBdRPlusActEquiv (σ : GQp p) :
    ColmezBdRPlus 𝓞_ℂ_[p] p ≃+* ColmezBdRPlus 𝓞_ℂ_[p] p where
  toFun := colmezBdRPlusAct p σ
  invFun := colmezBdRPlusAct p σ⁻¹
  left_inv := colmezBdRPlusAct_inv_apply p σ
  right_inv x := by simpa using colmezBdRPlusAct_inv_apply p σ⁻¹ x
  map_add' := map_add _
  map_mul' := map_mul _

/-- **The action of `σ ∈ G_{ℚ_p}` on Colmez's `B_dR`** (the fraction field of `B_dR^+`), by the
universal property of the fraction field. -/
noncomputable def colmezBdRAct (σ : GQp p) :
    FractionRing (ColmezBdRPlus 𝓞_ℂ_[p] p) ≃+* FractionRing (ColmezBdRPlus 𝓞_ℂ_[p] p) :=
  IsFractionRing.ringEquivOfRingEquiv (colmezBdRPlusActEquiv p σ)

theorem colmezBdRAct_algebraMap (σ : GQp p) (x : ColmezBdRPlus 𝓞_ℂ_[p] p) :
    colmezBdRAct p σ (algebraMap _ _ x) = algebraMap _ _ (colmezBdRPlusAct p σ x) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap (colmezBdRPlusActEquiv p σ) x

/-- **`colmezBdREquiv` intertwines the actions on `B_dR`**: Colmez's `colmezBdRAct p σ` and the
tree's `bdrAct p σ`, on all of the fraction field. -/
theorem colmezBdREquiv_act (σ : GQp p) (y : FractionRing (ColmezBdRPlus 𝓞_ℂ_[p] p)) :
    colmezBdREquiv p (colmezBdRAct p σ y) = bdrAct p σ (colmezBdREquiv p y) := by
  have h : (colmezBdREquiv p).toRingHom.comp (colmezBdRAct p σ).toRingHom =
      (bdrAct p σ).comp (colmezBdREquiv p).toRingHom := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors (ColmezBdRPlus 𝓞_ℂ_[p] p))
    refine RingHom.ext fun x => ?_
    change colmezBdREquiv p (colmezBdRAct p σ (algebraMap _ _ x)) =
      bdrAct p σ (colmezBdREquiv p (algebraMap _ _ x))
    rw [colmezBdRAct_algebraMap, colmezBdREquiv_algebraMap, colmezBdREquiv_algebraMap,
      colmezBdRPlusEquiv_act]
    change algebraMap (BDeRhamPlus 𝓞_ℂ_[p] p) (BdR p)
        (DR.bdrPlusMap p (oAct p σ) (colmezBdRPlusEquiv x)) =
      bdrAct p σ (algebraMap (BDeRhamPlus 𝓞_ℂ_[p] p) (BdR p) (colmezBdRPlusEquiv x))
    rw [bdrAct, DR.bdrMap, IsLocalization.map_eq]
  exact congrArg (fun φ => φ y) h

end ZInQ.Contrib.ColmezTiltIso
