/-
Copyright (c) 2026 H5/NOS Round-2 lane4 contributors.
Released under Apache 2.0 license as described in the project LICENSE.

H5 closed-section GM11 sub-gap (G4) `FramesNearOfPullback`, PROVED. SOURCE ONLY, UNCOMPILED.
Native HELD. No kernel/ABI/admission grade.

Generation descends along pullback at points, for a NATIVE invertible module (local triviality
from W07 `SheafOfModules.IsInvertible.exists_isoUnit`, Modules/Invertible.lean).

ADAPTED (namespaces, P2M macros removed, FLT `Scheme.Modules.IsInvertible` replaced by the native
W07 local trivialization, FLT callees replaced by the adapted copies here/in `PresentationBasics`)
from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0:
* `P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_exists_frame_of_frame_pullback.lean` (`FrameSpecSol`;
  upstream sha256 ad1f80539221eb468e6b9a59368c0abfa2119c9c1082455d59c4be9dd1866c82);
* `P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_bijective_unit_app_of_le_opensRange.lean`
  (upstream sha256 ad7fc4d88ee9e0e039543b0e36fd0719c5e005684e019d25cc3be9a46b2b22d8);
* `P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_unit_app_comp_pullbackComp_inv.lean`
  (upstream sha256 862309369a45fe3a4369d2a8c4bad43c0d7048aff3972b9c413c8aa7a53cf0b4).
No upstream option overrides were present; only `autoImplicit false` here.
No wholesale port; default limits.
-/
import ZInQKernel.Contrib.CloudR2NOS.ClosedSection.PresentationBasics
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.Invertible

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace ZInQ.Contrib.CloudR2NOS.ClosedSection.FramesDescend

/-- The adjunction unit along an open immersion is bijective on opens inside its range
(adapted FLT `bijective_unit_app_of_le_opensRange`). -/
theorem bijective_unit_app_of_le_opensRange {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (N : X.Modules) (V : X.Opens) (hV : V ≤ j.opensRange) :
    Function.Bijective (((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app N).app V) := by
  have hfac := Adjunction.unit_leftAdjointUniq_hom_app (Scheme.Modules.restrictAdjunction j)
    (Scheme.Modules.pullbackPushforwardAdjunction j) N
  have hfac' := congrArg (fun t => Scheme.Modules.Hom.app t V) hfac.symm
  have heq : j ''ᵁ j ⁻¹ᵁ V = V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right.mpr hV]
  have h2 : (homOfLE (j.image_preimage_le V)).op = eqToHom (congrArg op heq.symm) :=
    Subsingleton.elim _ _
  have hiso1 : IsIso (N.presheaf.map (homOfLE (j.image_preimage_le V)).op) := by
    rw [h2]
    exact ⟨N.presheaf.map (eqToHom (congrArg op heq)), by simp [eqToHom_map], by simp [eqToHom_map]⟩
  have hiso2 : IsIso ((((Scheme.Modules.restrictAdjunction j).leftAdjointUniq
      (Scheme.Modules.pullbackPushforwardAdjunction j)).hom.app N).app (j ⁻¹ᵁ V)) := inferInstance
  have hiso := @IsIso.comp_isIso _ _ _ _ _ _ _ hiso1 hiso2
  rw [← ConcreteCategory.isIso_iff_bijective]
  revert hiso
  refine fun hiso => ?_
  rw [hfac']
  exact hiso

/-- Units of composite pullbacks (adapted FLT `unit_app_comp_pullbackComp_inv`). -/
theorem unit_app_comp_pullbackComp_inv {X Y Z : Scheme.{u}} (g : Z ⟶ Y) (f : Y ⟶ X)
    (M : X.Modules) (U : X.Opens) :
    ((Scheme.Modules.pullbackPushforwardAdjunction (g ≫ f)).unit.app M).app U ≫
        ((Scheme.Modules.pullbackComp g f).inv.app M).app ((g ≫ f) ⁻¹ᵁ U) =
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app U ≫
        ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
          ((Scheme.Modules.pullback f).obj M)).app (f ⁻¹ᵁ U) := by
  have h := unit_conjugateEquiv ((Scheme.Modules.pullbackPushforwardAdjunction f).comp
      (Scheme.Modules.pullbackPushforwardAdjunction g))
    (Scheme.Modules.pullbackPushforwardAdjunction (g ≫ f)) (Scheme.Modules.pullbackComp g f).inv M
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv] at h
  have h' := congrArg (fun t => Scheme.Modules.Hom.app t U) h
  simp only [Scheme.Modules.Hom.comp_app, Adjunction.comp_unit_app,
    Scheme.Modules.pushforward_map_app, Scheme.Modules.pushforwardComp_hom_app_app,
    Functor.comp_obj] at h'
  erw [Category.comp_id] at h'
  exact h'.symm

namespace FrameSpec

variable {X : Scheme.{u}}

/-- Restriction of a global section. -/
noncomputable abbrev resT (M : X.Modules) (m : Γ(M, ⊤)) (W : X.Opens) : Γ(M, W) :=
  M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op m

/-- `m` freely generates `M` on every open inside `U`. -/
def IsFrame (M : X.Modules) (m : Γ(M, ⊤)) (U : X.Opens) : Prop :=
  ∀ W : X.Opens, W ≤ U → Function.Bijective fun g : Γ(X, W) => g • resT M m W

theorem res_map (M : X.Modules) (m : Γ(M, ⊤)) {W W' : X.Opens} (i : W' ⟶ W) :
    M.presheaf.map i.op (resT M m W) = resT M m W' := by
  simp only [resT, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  rfl

theorem res_smul (M : X.Modules) (H : Γ(X, ⊤)) (m : Γ(M, ⊤)) (W : X.Opens) :
    resT M (H • m) W = X.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op H • resT M m W := by
  rw [resT, Scheme.Modules.map_smul]

theorem app_res {M N : X.Modules} (φ : M ⟶ N) (m : Γ(M, ⊤)) (W : X.Opens) :
    φ.app W (resT M m W) = resT N (φ.app ⊤ m) W := by
  have := ((PresheafOfModules.toPresheaf _).map φ.val).naturality (homOfLE (le_top : W ≤ ⊤)).op
  exact (ConcreteCategory.congr_hom this m)

theorem IsFrame.of_iso {M N : X.Modules} (e : M ≅ N) {m : Γ(M, ⊤)} {U : X.Opens}
    (hm : IsFrame M m U) : IsFrame N (e.hom.app ⊤ m) U := by
  intro W hW
  have key : (fun g : Γ(X, W) => g • resT N (e.hom.app ⊤ m) W) =
      (e.hom.app W) ∘ (fun g : Γ(X, W) => g • resT M m W) := by
    funext g
    simp only [Function.comp_apply, Scheme.Modules.Hom.app_smul, app_res]
  rw [key]
  exact (ConcreteCategory.bijective_of_isIso (e.hom.app W)).comp (hm W hW)

theorem isFrame_of_iso_unit {M : X.Modules} (e : M ≅ SheafOfModules.unit X.ringCatSheaf) :
    IsFrame M (e.inv.app ⊤
      (show Γ((SheafOfModules.unit X.ringCatSheaf : X.Modules), ⊤) from (1 : Γ(X, ⊤)))) ⊤ := by
  have h1 : IsFrame (SheafOfModules.unit X.ringCatSheaf : X.Modules)
      (show Γ((SheafOfModules.unit X.ringCatSheaf : X.Modules), ⊤) from (1 : Γ(X, ⊤))) ⊤ := by
    intro W _
    have hres : resT (SheafOfModules.unit X.ringCatSheaf : X.Modules)
        (show Γ((SheafOfModules.unit X.ringCatSheaf : X.Modules), ⊤) from (1 : Γ(X, ⊤))) W =
        (show Γ((SheafOfModules.unit X.ringCatSheaf : X.Modules), W) from (1 : Γ(X, W))) := by
      change ((X.ringCatSheaf.obj.map (homOfLE (le_top : W ≤ ⊤)).op).hom 1) = 1
      exact map_one _
    rw [hres]
    change Function.Bijective fun g : Γ(X, W) => g * 1
    simp only [mul_one]
    exact Function.bijective_id
  simpa using h1.of_iso e.symm

theorem isUnit_germ_of_isFrame_smul {M : X.Modules} {T : Γ(M, ⊤)} {U : X.Opens}
    (hT : IsFrame M T U) (H : Γ(X, ⊤)) {z : X} {V : X.Opens} (hzV : z ∈ V) (hVU : V ≤ U)
    (hHT : IsFrame M (H • T) V) :
    IsUnit (X.presheaf.germ V z hzV (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op H)) := by
  have hb := hHT V le_rfl
  have hbT := hT V hVU
  have key : (fun g : Γ(X, V) => g • resT M (H • T) V) =
      (fun g : Γ(X, V) => g • resT M T V) ∘
        (fun g => g * X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op H) := by
    funext g
    simp only [Function.comp_apply, res_smul, mul_smul]
  rw [key] at hb
  have hmul : Function.Bijective
      (fun g : Γ(X, V) => g * X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op H) :=
    (Function.Bijective.of_comp_iff' hbT _).1 hb
  obtain ⟨g, hg⟩ := hmul.2 1
  have hu : IsUnit (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op H) :=
    isUnit_iff_exists_inv'.2 ⟨g, hg⟩
  exact hu.map _

theorem exists_isFrame_smul_of_isUnit_germ {M : X.Modules} {T : Γ(M, ⊤)} {U : X.Opens}
    (hT : IsFrame M T U) (H : Γ(X, ⊤)) {z : X} (hzU : z ∈ U)
    (hu : IsUnit (X.presheaf.germ U z hzU (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op H))) :
    ∃ V : X.Opens, z ∈ V ∧ IsFrame M (H • T) V := by
  refine ⟨X.basicOpen (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op H),
    (X.mem_basicOpen _ z hzU).2 hu, fun V hV => ?_⟩
  have hVU : V ≤ U := hV.trans (X.basicOpen_le _)
  have huV : IsUnit (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op H) := by
    have h0 := RingedSpace.isUnit_res_basicOpen (X := X.toLocallyRingedSpace.toSheafedSpace)
      (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op H)
    have hcomp : X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op H =
        X.presheaf.map (homOfLE hV).op (X.presheaf.map (homOfLE (X.basicOpen_le _)).op
          (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op H)) := by
      simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
      rfl
    rw [hcomp]
    exact h0.map (CommRingCat.Hom.hom (X.presheaf.map (homOfLE hV).op))
  have key : (fun g : Γ(X, V) => g • resT M (H • T) V) =
      (fun g : Γ(X, V) => g • resT M T V) ∘
        (fun g => g * X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op H) := by
    funext g
    simp only [Function.comp_apply, res_smul, mul_smul]
  rw [key]
  obtain ⟨u', hu'⟩ := huV
  refine (hT V hVU).comp ?_
  rw [← hu']
  exact (Units.mulRight u').bijective

theorem res_top (M : X.Modules) (m : Γ(M, ⊤)) : resT M m ⊤ = m := by
  have : (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)) = 𝟙 _ := rfl
  simp [resT]

theorem IsFrame.of_openImmersion {Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (M : X.Modules) (m : Γ(M, ⊤)) {U' : Y.Opens}
    (hfr : IsFrame ((Scheme.Modules.pullback j).obj M)
      (show Γ((Scheme.Modules.pullback j).obj M, ⊤) from
        (((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app M).app ⊤) m) U') :
    IsFrame M m (j ''ᵁ U') := by
  intro V hV
  have hVr : V ≤ j.opensRange := hV.trans (j.image_le_opensRange U')
  haveI : IsIso (j.app V) := j.isIso_app V hVr
  have ha : Function.Bijective (j.app V) := ConcreteCategory.bijective_of_isIso (j.app V)
  have hb : Function.Bijective
      (((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app M).app V) :=
    bijective_unit_app_of_le_opensRange j M V hVr
  have hW' : j ⁻¹ᵁ V ≤ U' :=
    (show j ⁻¹ᵁ V ≤ j ⁻¹ᵁ (j ''ᵁ U') from fun x hx => hV hx).trans_eq (j.preimage_image_eq U')
  have hψ := hfr (j ⁻¹ᵁ V) hW'
  have key : (((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app M).app V) ∘
      (fun g : Γ(X, V) => g • resT M m V) =
      (fun g : Γ(Y, j ⁻¹ᵁ V) => g • resT ((Scheme.Modules.pullback j).obj M)
        (show Γ((Scheme.Modules.pullback j).obj M, ⊤) from
          (((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app M).app ⊤) m) (j ⁻¹ᵁ V)) ∘
        (j.app V) := by
    funext g
    simp only [Function.comp_apply]
    erw [Scheme.Modules.Hom.app_smul, app_res]
    rfl
  have hcomp : Function.Bijective
      ((((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app M).app V) ∘
        (fun g : Γ(X, V) => g • resT M m V)) := by
    rw [key]
    exact hψ.comp ha
  exact (Function.Bijective.of_comp_iff' hb _).1 hcomp

theorem exists_iso_forall_unit_eq {X Y Z : Scheme.{u}} (g : Z ⟶ Y) (f : Y ⟶ X) (h : Z ⟶ X)
    (hh : g ≫ f = h) (M : X.Modules) :
    ∃ e : (Scheme.Modules.pullback h).obj M ≅
        (Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback f).obj M),
      ∀ s : Γ(M, ⊤),
        (e.hom.app ⊤) ((((Scheme.Modules.pullbackPushforwardAdjunction h).unit.app M).app ⊤) s) =
          (show Γ((Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback f).obj M), ⊤) from
            (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
                ((Scheme.Modules.pullback f).obj M)).app ⊤)
              (show Γ((Scheme.Modules.pullback f).obj M, ⊤) from
                (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app ⊤) s)) := by
  subst hh
  refine ⟨((Scheme.Modules.pullbackComp g f).app M).symm, fun s => ?_⟩
  exact CategoryTheory.ConcreteCategory.congr_hom (unit_app_comp_pullbackComp_inv g f M ⊤) s

/-- The literal pulled-back global section. -/
noncomputable abbrev pb {X' : Scheme.{u}} (p : X' ⟶ X) (M : X.Modules) (m : Γ(M, ⊤)) :
    Γ((Scheme.Modules.pullback p).obj M, ⊤) :=
  show Γ((Scheme.Modules.pullback p).obj M, ⊤) from
    (((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M).app ⊤) m

theorem pb_smul {X' : Scheme.{u}} (p : X' ⟶ X) (M : X.Modules) (r : Γ(X, ⊤)) (m : Γ(M, ⊤)) :
    pb p M (r • m) = p.appTop r • pb p M m := by
  dsimp only [pb]
  erw [Scheme.Modules.Hom.app_smul]
  rfl

/-- **Generation descends** (FLT `FrameSpecSol.main`, native invertibility). -/
theorem main {X' : Scheme.{u}} (p : X' ⟶ X) (M : X.Modules) [M.IsInvertible]
    (m : Γ(M, ⊤)) (z : X')
    (h : ∃ U' : X'.Opens, z ∈ U' ∧ IsFrame ((Scheme.Modules.pullback p).obj M) (pb p M m) U') :
    ∃ U : X.Opens, p z ∈ U ∧ IsFrame M m U := by
  classical
  obtain ⟨U, hyU, ⟨eU⟩⟩ :=
    SheafOfModules.IsInvertible.exists_isoUnit (inferInstance : M.IsInvertible) (p z)
  obtain ⟨U', hzU', hU'⟩ := h
  let j : (↑U : Scheme.{u}) ⟶ X := U.ι
  let j' : (↑(p ⁻¹ᵁ U) : Scheme.{u}) ⟶ X' := (p ⁻¹ᵁ U).ι
  let pU : (↑(p ⁻¹ᵁ U) : Scheme.{u}) ⟶ ↑U := p ∣_ U
  have hcomm : pU ≫ j = j' ≫ p := morphismRestrict_ι p U
  let z' : ↑(p ⁻¹ᵁ U) := ⟨z, hyU⟩
  let MU : (↑U : Scheme.{u}).Modules := (Scheme.Modules.pullback j).obj M
  let τ : Γ(MU, ⊤) := eU.inv.app ⊤ (show Γ((SheafOfModules.unit (↑U : Scheme.{u}).ringCatSheaf :
    (↑U : Scheme.{u}).Modules), ⊤) from (1 : Γ(↑U, ⊤)))
  have hτ : IsFrame MU τ ⊤ := isFrame_of_iso_unit eU
  obtain ⟨hf, hhf⟩ := (hτ ⊤ le_rfl).2 (pb j M m)
  have hmU : pb j M m = hf • τ := by rw [← hhf]; simp only [res_top]
  have h3a : IsFrame ((Scheme.Modules.pullback j').obj ((Scheme.Modules.pullback p).obj M))
      (pb j' _ (pb p M m)) (j' ⁻¹ᵁ U') := fun W hW =>
    PresentationBasics.FramePullback.main j' _ (pb p M m) hU' W hW
  obtain ⟨e₁, he₁⟩ := exists_iso_forall_unit_eq j' p (j' ≫ p) rfl M
  obtain ⟨e₂, he₂⟩ := exists_iso_forall_unit_eq pU j (j' ≫ p) hcomm M
  have he : ((e₁.symm ≪≫ e₂).hom.app ⊤) (pb j' _ (pb p M m)) = pb pU MU (pb j M m) := by
    have h1 : (e₁.inv.app ⊤) (pb j' _ (pb p M m)) = pb (j' ≫ p) M m := by
      have h2 := congrArg (e₁.inv.app ⊤) (he₁ m)
      rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, Iso.hom_inv_id,
        Scheme.Modules.Hom.id_app, ConcreteCategory.id_apply] at h2
      exact h2.symm
    rw [Iso.trans_hom, Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, Iso.symm_hom, h1]
    exact he₂ m
  have h3 : IsFrame ((Scheme.Modules.pullback pU).obj MU) (pb pU MU (pb j M m)) (j' ⁻¹ᵁ U') := by
    rw [← he]
    exact h3a.of_iso _
  have hT : IsFrame ((Scheme.Modules.pullback pU).obj MU) (pb pU MU τ) ⊤ := fun W hW =>
    PresentationBasics.FramePullback.main pU MU τ hτ W (by simp)
  rw [hmU, pb_smul] at h3
  have h5 := isUnit_germ_of_isFrame_smul hT (pU.appTop hf) (z := z') (V := j' ⁻¹ᵁ U') hzU' le_top h3
  have h6 : IsUnit ((↑U : Scheme.{u}).presheaf.germ ⊤ (pU z') trivial hf) := by
    rw [← isUnit_map_iff (CommRingCat.Hom.hom (pU.stalkMap z')), ← CommRingCat.comp_apply,
      Scheme.Hom.germ_stalkMap pU ⊤ z' trivial]
    rw [TopCat.Presheaf.germ_res_apply] at h5
    convert h5 using 1
    rfl
  obtain ⟨V, hzV, hV⟩ := exists_isFrame_smul_of_isUnit_germ hτ hf (z := pU z') (U := ⊤) trivial
    (by simp [res_top] at h6 ⊢; exact h6)
  rw [← hmU] at hV
  refine ⟨j ''ᵁ V, ?_, IsFrame.of_openImmersion j M m hV⟩
  refine ⟨pU z', hzV, ?_⟩
  show (pU ≫ j) z' = p z
  rw [hcomm]
  rfl

end FrameSpec

/-- **(G4) proved.** -/
theorem framesNearOfPullback : FramesNearOfPullback.{u} := by
  intro X Y i M _ σ y h
  exact FrameSpec.main i M σ y h

end ZInQ.Contrib.CloudR2NOS.ClosedSection.FramesDescend
