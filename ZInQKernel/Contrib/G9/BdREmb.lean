import ZInQKernel.Contrib.G9.KerTheta
import ZInQKernel.Contrib.G9.HenselEmb
import ZInQKernel.Contrib.G9.Local

/-!
# G9: the action of `G_{ℚ_p}` on `B_dR`, and `F' ⊆ B_dR` equivariantly

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task g9-derham, 2026-11-13).

* `bdrAct_mul`, `bdrAct_one`: pkg-I4's `bdrAct` is an action (functoriality of pkg-I4's
  `DR.bdrMap`, through the tilt, Witt vectors, `[1/p]` and the adic completion), packaged as the
  representation `bdrActHom : G_{ℚ_p} →* End_{ℚ_p}(B_dR)`.
* `thetaPlusCp_bdrPlusMap`: bdr-kertheta's residue map `θ⁺ : B_dR^+ → ℂ_p` is equivariant.
* `thetaPlusCp_qpToPlus`: `θ⁺` is `ℚ_p`-linear for pkg-I4's `ℚ_p ⊆ B_dR^+`.
* `iotaDR`, `bdrAct_iotaDR`: for a finite Galois `F/ℚ_p`, the copy `F' ⊆ ℚ̄_p` of `F` embeds in
  `B_dR` with `σ(ι x) = ι(σ x)`, by the Hensel lift (`HenselEmb.lean`) through `θ⁺`
  (`B_dR^+` is `(ξ)`-adically complete, local with maximal ideal `ker θ⁺ = (ξ)`, a domain:
  bdr-kertheta).
-/

namespace ZInQ.Contrib.G9

set_option linter.unusedSectionVars false

open PkgI4 Module Ideal

noncomputable section

namespace DRFunct

open PkgI4.DR

variable (p : ℕ) [Fact p.Prime]

section general

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]

theorem modPMap_comp (f : R →+* S) (g : S →+* T) :
    modPMap p (g.comp f) = (modPMap p g).comp (modPMap p f) :=
  Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl)

theorem modPMap_id : modPMap p (RingHom.id R) = RingHom.id _ :=
  Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl)

theorem wittMap_comp {A B C : Type*} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B)
    (g : B →+* C) :
    WittVector.map (p := p) (g.comp f) = (WittVector.map g).comp (WittVector.map f) := by
  ext x n
  simp

theorem wittMap_id {A : Type*} [CommRing A] :
    WittVector.map (p := p) (RingHom.id A) = RingHom.id _ := by
  ext x n
  simp

variable [Fact ¬IsUnit (p : R)] [Fact ¬IsUnit (p : S)] [Fact ¬IsUnit (p : T)]

theorem preTiltMap_comp (f : R →+* S) (g : S →+* T) :
    preTiltMap p (g.comp f) = (preTiltMap p g).comp (preTiltMap p f) :=
  RingHom.ext fun x => Perfection.ext fun n => by
    rw [coeff_preTiltMap, RingHom.comp_apply, coeff_preTiltMap, coeff_preTiltMap, modPMap_comp]
    rfl

theorem preTiltMap_id : preTiltMap p (RingHom.id R) = RingHom.id _ :=
  RingHom.ext fun x => Perfection.ext fun n => by
    rw [coeff_preTiltMap, modPMap_id]
    rfl

theorem locMap_comp (f : R →+* S) (g : S →+* T) :
    locMap p (g.comp f) = (locMap p g).comp (locMap p f) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (p : WittVector p (PreTilt R p)))
  ext w
  simp only [RingHom.comp_apply, locMap, Localization.awayLift, IsLocalization.Away.lift,
    IsLocalization.lift_eq]
  rw [preTiltMap_comp, wittMap_comp]
  rfl

theorem locMap_id : locMap p (RingHom.id R) = RingHom.id _ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (p : WittVector p (PreTilt R p)))
  ext w
  simp only [RingHom.comp_apply, RingHom.id_apply, locMap, Localization.awayLift,
    IsLocalization.Away.lift, IsLocalization.lift_eq]
  rw [preTiltMap_id, wittMap_id]
  rfl

end general

section adic

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]

theorem adicMap_congr (J : Ideal A) (J' : Ideal B) {g g' : A →+* B} (h : g = g')
    (hg : J ≤ J'.comap g) (hg' : J ≤ J'.comap g') : adicMap J J' g hg = adicMap J J' g' hg' := by
  subst h; rfl

theorem adicMap_comp_apply (J : Ideal A) (J' : Ideal B) (J'' : Ideal C) (g1 : A →+* B)
    (h1 : J ≤ J'.comap g1) (g2 : B →+* C) (h2 : J' ≤ J''.comap g2) (g3 : A →+* C)
    (h3 : J ≤ J''.comap g3) (hg : g3 = g2.comp g1) (x : AdicCompletion J A) :
    adicMap J J'' g3 h3 x = adicMap J' J'' g2 h2 (adicMap J J' g1 h1 x) := by
  subst hg
  refine AdicCompletion.ext_evalₐ fun n => ?_
  have hin := adicMap_evalₐ J J' g1 h1 n x
  rw [adicMap_evalₐ, adicMap_evalₐ]
  simp only [adicMapAux, RingHom.comp_apply] at hin ⊢
  erw [hin]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ J n x)
  erw [← ha]
  rfl

theorem evalOneₐ_adicMap (J : Ideal A) (J' : Ideal B) (g : A →+* B) (hg : J ≤ J'.comap g)
    (x : AdicCompletion J A) :
    AdicCompletion.evalOneₐ J' (adicMap J J' g hg x) =
      Ideal.quotientMap J' g hg (AdicCompletion.evalOneₐ J x) := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ J 1 x)
  have e1 : AdicCompletion.evalOneₐ J x =
      Ideal.Quotient.factor (show J ^ 1 ≤ J by simp) (AdicCompletion.evalₐ J 1 x) := rfl
  have e2 : AdicCompletion.evalOneₐ J' (adicMap J J' g hg x) =
      Ideal.Quotient.factor (show J' ^ 1 ≤ J' by simp)
        (AdicCompletion.evalₐ J' 1 (adicMap J J' g hg x)) := rfl
  rw [e1, e2, adicMap_evalₐ]
  simp only [adicMapAux, RingHom.comp_apply]
  erw [← ha]
  rfl

theorem adicMap_id_apply (J : Ideal A) (g : A →+* A) (h : J ≤ J.comap g)
    (hg : g = RingHom.id A) (x : AdicCompletion J A) : adicMap J J g h x = x := by
  subst hg
  refine AdicCompletion.ext_evalₐ fun n => ?_
  rw [adicMap_evalₐ]
  simp only [adicMapAux, RingHom.comp_apply]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ J n x)
  erw [← ha]
  rfl

end adic

section bdr

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
  [Fact ¬IsUnit (p : R)] [Fact ¬IsUnit (p : S)] [Fact ¬IsUnit (p : T)]
  [IsAdicComplete (span {(p : R)}) R] [IsAdicComplete (span {(p : S)}) S]
  [IsAdicComplete (span {(p : T)}) T]

theorem bdrPlusMap_comp (f : R →+* S) (g : S →+* T) :
    bdrPlusMap p (g.comp f) = (bdrPlusMap p g).comp (bdrPlusMap p f) :=
  RingHom.ext fun x => adicMap_comp_apply _ _ _ (locMap p f) (ker_le_comap_locMap p f)
    (locMap p g) (ker_le_comap_locMap p g) _ _ (locMap_comp p f g) x

theorem bdrPlusMap_id : bdrPlusMap p (RingHom.id R) = RingHom.id _ :=
  RingHom.ext fun x => adicMap_id_apply _ _ _ (locMap_id p) x

theorem bdrMap_comp (f1 : R →+* S) (g1 : S →+* R) (hgf1 : ∀ x, g1 (f1 x) = x)
    (hfg1 : ∀ y, f1 (g1 y) = y) (f2 : S →+* T) (g2 : T →+* S) (hgf2 : ∀ x, g2 (f2 x) = x)
    (hfg2 : ∀ y, f2 (g2 y) = y) (f3 : R →+* T) (g3 : T →+* R) (hgf3 : ∀ x, g3 (f3 x) = x)
    (hfg3 : ∀ y, f3 (g3 y) = y) (hf : f3 = f2.comp f1) :
    bdrMap p f3 g3 hgf3 hfg3 = (bdrMap p f2 g2 hgf2 hfg2).comp (bdrMap p f1 g1 hgf1 hfg1) := by
  apply IsLocalization.ringHom_ext (genMonoid p R)
  ext x
  simp only [RingHom.comp_apply, bdrMap, IsLocalization.map_eq]
  subst hf
  rw [bdrPlusMap_comp]
  rfl

theorem bdrMap_id (f : R →+* R) (g : R →+* R) (hgf : ∀ x, g (f x) = x)
    (hfg : ∀ y, f (g y) = y) (hf : f = RingHom.id R) :
    bdrMap p f g hgf hfg = RingHom.id _ := by
  apply IsLocalization.ringHom_ext (genMonoid p R)
  ext x
  simp only [RingHom.comp_apply, bdrMap, IsLocalization.map_eq, RingHom.id_apply]
  subst hf
  rw [bdrPlusMap_id]
  rfl

end bdr

end DRFunct

section Action

variable (p : ℕ) [Fact p.Prime]

theorem oAct_mul (σ τ : GQp p) : oAct p (σ * τ) = (oAct p σ).comp (oAct p τ) :=
  RingHom.ext fun x => Subtype.ext (cpAct_mul p σ τ x)

theorem oAct_one : oAct p 1 = RingHom.id _ :=
  RingHom.ext fun x => Subtype.ext (cpAct_one p x)

theorem bdrAct_mul (σ τ : GQp p) : bdrAct p (σ * τ) = (bdrAct p σ).comp (bdrAct p τ) :=
  DRFunct.bdrMap_comp p _ _ _ _ _ _ _ _ _ _ _ _ (oAct_mul p σ τ)

theorem bdrAct_one : bdrAct p 1 = RingHom.id _ :=
  DRFunct.bdrMap_id p _ _ _ _ (oAct_one p)

/-- `σ` acting `ℚ_p`-linearly on `B_dR`. -/
def bdrActL (σ : GQp p) : BdR p →ₗ[ℚ_[p]] BdR p where
  toFun := bdrAct p σ
  map_add' := map_add _
  map_smul' := bdrAct_smul p σ

/-- **The representation `G_{ℚ_p} → End_{ℚ_p}(B_dR)`.** -/
def bdrActHom : GQp p →* (BdR p →ₗ[ℚ_[p]] BdR p) where
  toFun := bdrActL p
  map_one' := LinearMap.ext fun x => by
    change bdrAct p 1 x = x
    rw [bdrAct_one]; rfl
  map_mul' σ τ := LinearMap.ext fun x => by
    change bdrAct p (σ * τ) x = bdrAct p σ (bdrAct p τ x)
    rw [bdrAct_mul]; rfl

theorem bdrActHom_apply (σ : GQp p) (x : BdR p) : bdrActHom p σ x = bdrAct p σ x := rfl

end Action

/-! ### `θ⁺` is equivariant and `ℚ_p`-linear -/

section Theta

variable (p : ℕ) [Fact p.Prime]

theorem thetaPlus_eq' (z : BDeRhamPlus 𝓞_ℂ_[p] p) : BdrKer.Cp.thetaPlus p z =
    (RingHom.quotientKerEquivOfSurjective (BdrKer.Cp.fontaineThetaInvertP_surjective p))
      (AdicCompletion.evalOneₐ (RingHom.ker (fontaineThetaInvertP 𝓞_ℂ_[p] p)) z) := rfl

theorem thetaPlus_mk (σ : GQp p) (x : Localization.Away (p : WittVector p (PreTilt 𝓞_ℂ_[p] p))) :
    (RingHom.quotientKerEquivOfSurjective (BdrKer.Cp.fontaineThetaInvertP_surjective p))
      (Ideal.quotientMap _ (DR.locMap p (oAct p σ)) (DR.ker_le_comap_locMap p (oAct p σ))
        (Ideal.Quotient.mk _ x)) =
    DR.locMapBase p (oAct p σ) ((RingHom.quotientKerEquivOfSurjective
      (BdrKer.Cp.fontaineThetaInvertP_surjective p)) (Ideal.Quotient.mk _ x)) := by
  rw [Ideal.quotientMap_mk, RingHom.quotientKerEquivOfSurjective_apply_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk]
  rw [← RingHom.comp_apply, DR.fontaineThetaInvertP_naturality]
  rfl

theorem thetaPlus_quot (σ : GQp p)
    (q : Localization.Away (p : WittVector p (PreTilt 𝓞_ℂ_[p] p)) ⧸
      RingHom.ker (fontaineThetaInvertP 𝓞_ℂ_[p] p)) :
    (RingHom.quotientKerEquivOfSurjective (BdrKer.Cp.fontaineThetaInvertP_surjective p))
      (Ideal.quotientMap _ (DR.locMap p (oAct p σ)) (DR.ker_le_comap_locMap p (oAct p σ)) q) =
    DR.locMapBase p (oAct p σ) ((RingHom.quotientKerEquivOfSurjective
      (BdrKer.Cp.fontaineThetaInvertP_surjective p)) q) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
  exact thetaPlus_mk p σ x

theorem thetaPlus_bdrPlusMap (σ : GQp p) (y : BDeRhamPlus 𝓞_ℂ_[p] p) :
    BdrKer.Cp.thetaPlus p (DR.bdrPlusMap p (oAct p σ) y) =
      DR.locMapBase p (oAct p σ) (BdrKer.Cp.thetaPlus p y) := by
  have h := DRFunct.evalOneₐ_adicMap (RingHom.ker (fontaineThetaInvertP 𝓞_ℂ_[p] p))
    (RingHom.ker (fontaineThetaInvertP 𝓞_ℂ_[p] p)) (DR.locMap p (oAct p σ))
    (DR.ker_le_comap_locMap p (oAct p σ)) y
  rw [thetaPlus_eq', thetaPlus_eq']
  rw [show DR.bdrPlusMap p (oAct p σ) y = DR.adicMap _ _ (DR.locMap p (oAct p σ))
    (DR.ker_le_comap_locMap p (oAct p σ)) y from rfl, h]
  exact thetaPlus_quot p σ _

theorem awayEquivCp_locMapBase (σ : GQp p) (u : Localization.Away (p : 𝓞_ℂ_[p])) :
    BdrKer.Cp.awayEquivCp p (DR.locMapBase p (oAct p σ) u) =
      cpAct p σ (BdrKer.Cp.awayEquivCp p u) := by
  have h : (BdrKer.Cp.awayEquivCp p).toRingEquiv.toRingHom.comp (DR.locMapBase p (oAct p σ)) =
      (cpAct p σ).comp (BdrKer.Cp.awayEquivCp p).toRingEquiv.toRingHom := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (p : 𝓞_ℂ_[p]))
    ext o
    simp only [RingHom.comp_apply, DR.locMapBase, Localization.awayLift,
      IsLocalization.Away.lift, IsLocalization.lift_eq]
    simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, AlgEquiv.coe_toRingEquiv,
      AlgEquiv.commutes]
    rfl
  exact congrArg (fun φ => φ u) h

/-- **`θ⁺` is `G_{ℚ_p}`-equivariant.** -/
theorem thetaPlusCp_bdrPlusMap (σ : GQp p) (y : BDeRhamPlus 𝓞_ℂ_[p] p) :
    BdrKer.Cp.thetaPlusCp p (DR.bdrPlusMap p (oAct p σ) y) =
      cpAct p σ (BdrKer.Cp.thetaPlusCp p y) := by
  change BdrKer.Cp.awayEquivCp p (BdrKer.Cp.thetaPlus p _) =
    cpAct p σ (BdrKer.Cp.awayEquivCp p (BdrKer.Cp.thetaPlus p y))
  rw [thetaPlus_bdrPlusMap, awayEquivCp_locMapBase]

/-- `ℚ_p → B_dR^+` (pkg-I4's `ofLoc ∘ qpToLoc`). -/
def qpToPlus : ℚ_[p] →+* BDeRhamPlus 𝓞_ℂ_[p] p := (ofLoc p).comp (qpToLoc p)

theorem qpToBdR_eq (c : ℚ_[p]) :
    qpToBdR p c = algebraMap (BDeRhamPlus 𝓞_ℂ_[p] p) (BdR p) (qpToPlus p c) := rfl

theorem bdrPlusMap_qpToPlus (σ : GQp p) (c : ℚ_[p]) :
    DR.bdrPlusMap p (oAct p σ) (qpToPlus p c) = qpToPlus p c := by
  have h : (DR.bdrPlusMap p (oAct p σ)).comp (qpToPlus p) = qpToPlus p := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (p : ℤ_[p]))
    ext z
    simp only [RingHom.comp_apply, qpToPlus]
    rw [qpToLoc_algebraMap, bdrPlusMap_ofLoc, locMap_algebraMap, wittMap_zpToW]
  exact congrArg (fun φ => φ c) h

theorem thetaPlusCp_zp_eq (z : ℤ_[p]) :
    BdrKer.Cp.thetaPlusCp p (qpToPlus p (algebraMap ℤ_[p] ℚ_[p] z)) =
      ((WittVector.fontaineTheta (𝓞_ℂ_[p]) p (zpToW p z) : 𝓞_ℂ_[p]) : ℂ_[p]) := by
  simp only [qpToPlus, RingHom.comp_apply, qpToLoc_algebraMap]
  have e : ofLoc p (algebraMap _ (Localization.Away (p : WittVector p (PreTilt 𝓞_ℂ_[p] p)))
      (zpToW p z)) = BdrKer.ofPlus _ p (algebraMap _ _ (zpToW p z)) := by
    rw [ofLoc]
    erw [AdicCompletion.algebraMap_apply]
    rfl
  rw [e]
  change BdrKer.Cp.awayEquivCp p (fontaineThetaInvertP _ p (algebraMap _ _ (zpToW p z))) = _
  simp only [fontaineThetaInvertP, Localization.awayLift, IsLocalization.Away.lift,
    IsLocalization.lift_eq, RingHom.comp_apply]
  rw [AlgEquiv.commutes]
  rfl

theorem norm_algebraMap_qp (c : ℚ_[p]) : ‖algebraMap ℚ_[p] ℂ_[p] c‖ = ‖c‖ := by
  rw [IsScalarTower.algebraMap_apply ℚ_[p] (PadicAlgCl p) ℂ_[p], ← PadicComplex.coe_eq,
    PadicComplex.norm_extends, PadicAlgCl.norm_extends]

theorem thetaPlusCp_zp (z : ℤ_[p]) :
    BdrKer.Cp.thetaPlusCp p (qpToPlus p (algebraMap ℤ_[p] ℚ_[p] z)) =
      algebraMap ℚ_[p] ℂ_[p] (algebraMap ℤ_[p] ℚ_[p] z) := by
  set g1 := (BdrKer.Cp.thetaPlusCp p).comp ((qpToPlus p).comp (algebraMap ℤ_[p] ℚ_[p]))
  set g2 := (algebraMap ℚ_[p] ℂ_[p]).comp (algebraMap ℤ_[p] ℚ_[p])
  change g1 z = g2 z
  have hb1 : ∀ w, ‖g1 w‖ ≤ 1 := fun w => by
    change ‖BdrKer.Cp.thetaPlusCp p (qpToPlus p (algebraMap ℤ_[p] ℚ_[p] w))‖ ≤ 1
    rw [thetaPlusCp_zp_eq]
    exact (Cp.mem_O_iff p _).mp (Subtype.prop _)
  have hb2 : ∀ w, ‖g2 w‖ ≤ 1 := fun w => by
    change ‖algebraMap ℚ_[p] ℂ_[p] (algebraMap ℤ_[p] ℚ_[p] w)‖ ≤ 1
    rw [norm_algebraMap_qp]
    exact PadicInt.norm_le_one w
  by_contra hne
  have hd : 0 < ‖g1 z - g2 z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (half_pos hd) (Cp.norm_p_lt_one p)
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp (PadicInt.appr_spec n z)
  have hz : z = (PadicInt.appr z n : ℤ_[p]) + w * (p : ℤ_[p]) ^ n := by
    rw [hw]; ring
  have hdiff : g1 z - g2 z = (g1 w - g2 w) * (p : ℂ_[p]) ^ n := by
    rw [hz, map_add, map_add, map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast,
      map_natCast, map_natCast]
    ring
  have hle : ‖g1 z - g2 z‖ ≤ 2 * ‖(p : ℂ_[p])‖ ^ n := by
    rw [hdiff, norm_mul, norm_pow]
    have : ‖g1 w - g2 w‖ ≤ 2 := by
      calc ‖g1 w - g2 w‖ ≤ ‖g1 w‖ + ‖g2 w‖ := norm_sub_le _ _
        _ ≤ 1 + 1 := add_le_add (hb1 w) (hb2 w)
        _ = 2 := by norm_num
    exact mul_le_mul_of_nonneg_right this (by positivity)
  linarith

/-- **`θ⁺` is `ℚ_p`-linear**: `θ⁺(c) = c` for `c ∈ ℚ_p ⊆ B_dR^+`. -/
theorem thetaPlusCp_qpToPlus (c : ℚ_[p]) :
    BdrKer.Cp.thetaPlusCp p (qpToPlus p c) = algebraMap ℚ_[p] ℂ_[p] c := by
  have hext : (BdrKer.Cp.thetaPlusCp p).comp (qpToPlus p) = algebraMap ℚ_[p] ℂ_[p] := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (p : ℤ_[p]))
    ext z
    simp only [RingHom.comp_apply]
    exact thetaPlusCp_zp p z
  exact congrArg (fun φ => φ c) hext

end Theta

end

end ZInQ.Contrib.G9
