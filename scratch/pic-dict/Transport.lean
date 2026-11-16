import ZInQKernel.Contrib.OneProof.PicDictionary
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.FreeGeneratorPullback

/-! # pic-dict: transport of Mumford's formula along an automorphism (towards `WeilFormulaGalois`) -/

noncomputable section

set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite

namespace PicDict.Transport

open Scheme.Modules

universe u

variable {X Y Z : Scheme.{u}}

/-- `𝒪 → (f ≫ h)_* 𝒪` is the composite of `𝒪 → h_* 𝒪 → h_* f_* 𝒪`. -/
lemma unitToPushforward_comp (f : X ⟶ Y) (h : Y ⟶ Z) :
    SheafOfModules.unitToPushforwardObjUnit (f ≫ h).toRingCatSheafHom =
      SheafOfModules.unitToPushforwardObjUnit h.toRingCatSheafHom ≫
        (pushforward h).map (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) ≫
          (pushforwardComp f h).hom.app (unit X) := by
  ext U x
  rfl

/-- **`pullbackObjUnitIso` is compatible with `pullbackComp`.** -/
lemma pullbackObjUnitIso_comp (f : X ⟶ Y) (h : Y ⟶ Z) :
    (pullbackComp f h).inv.app _ ≫ (Scheme.Modules.pullback f).map (pullbackObjUnitIso h).hom ≫
      (pullbackObjUnitIso f).hom = (pullbackObjUnitIso (f ≫ h)).hom := by
  haveI : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    (pullbackPushforwardAdjunction f).isRightAdjoint
  haveI : (SheafOfModules.pushforward h.toRingCatSheafHom).IsRightAdjoint :=
    (pullbackPushforwardAdjunction h).isRightAdjoint
  haveI : (SheafOfModules.pushforward (f ≫ h).toRingCatSheafHom).IsRightAdjoint :=
    (pullbackPushforwardAdjunction (f ≫ h)).isRightAdjoint
  apply ((pullbackPushforwardAdjunction (f ≫ h)).homEquiv _ _).injective
  have hR : (pullbackPushforwardAdjunction (f ≫ h)).homEquiv _ _ (pullbackObjUnitIso (f ≫ h)).hom =
      SheafOfModules.unitToPushforwardObjUnit (f ≫ h).toRingCatSheafHom :=
    SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _
  have hf : (pullbackPushforwardAdjunction f).homEquiv _ _ (pullbackObjUnitIso f).hom =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom :=
    SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _
  have hh : (pullbackPushforwardAdjunction h).homEquiv _ _ (pullbackObjUnitIso h).hom =
      SheafOfModules.unitToPushforwardObjUnit h.toRingCatSheafHom :=
    SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _
  rw [hR, unitToPushforward_comp]
  set adj₁ := (pullbackPushforwardAdjunction h).comp (pullbackPushforwardAdjunction f)
  set adj₂ := pullbackPushforwardAdjunction (f ≫ h)
  set Yf := (Scheme.Modules.pullback f).map (pullbackObjUnitIso h).hom ≫ (pullbackObjUnitIso f).hom
  have hc := conjugateEquiv_pullbackComp_inv f h
  have hu := unit_conjugateEquiv adj₁ adj₂ (pullbackComp f h).inv (unit Z)
  rw [hc] at hu
  have key : adj₂.homEquiv _ _ ((pullbackComp f h).inv.app _ ≫ Yf) =
      adj₁.homEquiv _ _ Yf ≫ (pushforwardComp f h).hom.app (unit X) := by
    rw [adj₂.homEquiv_unit, adj₁.homEquiv_unit, Functor.map_comp, ← Category.assoc, ← hu,
      Category.assoc, Category.assoc]
    congr 1
  rw [key, ← Category.assoc]
  refine congrArg (fun φ => φ ≫ (pushforwardComp f h).hom.app (unit X)) ?_
  rw [Adjunction.comp_homEquiv]
  show (pullbackPushforwardAdjunction h).homEquiv _ _ ((pullbackPushforwardAdjunction f).homEquiv _ _
    ((Scheme.Modules.pullback f).map (pullbackObjUnitIso h).hom ≫ (pullbackObjUnitIso f).hom)) = _
  rw [Adjunction.homEquiv_naturality_left, hf, Adjunction.homEquiv_naturality_right, hh]

end PicDict.Transport

namespace PicDict.Transport

open Scheme.Modules

universe v

variable {X Y Z W : Scheme.{v}}

lemma pullbackCongr_hom_app {f f' : X ⟶ Y} (e : f = f') (M : Y.Modules) :
    (pullbackCongr e).hom.app M = eqToHom (by rw [e]) := by
  subst e; rfl

/-- naturality of `pullbackComp` in the first variable -/
lemma eqToHom_comp_pullbackComp {f f' : X ⟶ Y} (e : f = f') (h : Y ⟶ Z) (M : Z.Modules)
    (p : (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback h).obj M) =
      (Scheme.Modules.pullback f').obj ((Scheme.Modules.pullback h).obj M)) :
    eqToHom p ≫ (pullbackComp f' h).hom.app M =
      (pullbackComp f h).hom.app M ≫ eqToHom (by rw [e]) := by
  subst e; simp

/-- naturality of `pullbackComp` in the second variable -/
lemma map_eqToHom_comp_pullbackComp (f : X ⟶ Y) {h h' : Y ⟶ Z} (e : h = h') (M : Z.Modules)
    (p : (Scheme.Modules.pullback h).obj M = (Scheme.Modules.pullback h').obj M) :
    (Scheme.Modules.pullback f).map (eqToHom p) ≫ (pullbackComp f h').hom.app M =
      (pullbackComp f h).hom.app M ≫ eqToHom (by rw [e]) := by
  subst e; simp

/-- associativity of `pullbackComp`, on objects -/
lemma pullbackComp_assoc_app (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) (M : W.Modules) :
    (Scheme.Modules.pullback f).map ((pullbackComp g h).hom.app M) ≫
        (pullbackComp f (g ≫ h)).hom.app M =
      (pullbackComp f g).hom.app ((Scheme.Modules.pullback h).obj M) ≫
        (pullbackComp (f ≫ g) h).hom.app M ≫ eqToHom (by rw [Category.assoc]) := by
  have H := congrArg (fun τ => τ.app M) (pseudofunctor_associativity f g h)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.whiskerLeft_app, Category.id_comp, eqToHom_app] at H
  have H1 := (Iso.inv_comp_eq ((pullbackComp f (g ≫ h)).app M)).mp H
  have H2 := (Iso.inv_comp_eq ((Scheme.Modules.pullback f).mapIso ((pullbackComp g h).app M))).mp H1
  simp only [Functor.mapIso_hom, Iso.app_hom] at H2
  rw [← Category.assoc ((pullbackComp f g).hom.app _), H2]
  simp

lemma pullbackCongr_inv_app {f f' : X ⟶ Y} (e : f = f') (M : Y.Modules) :
    (pullbackCongr e).inv.app M = eqToHom (by rw [e]) := by
  subst e; rfl

lemma pullbackComp_assoc_inv₁ (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) (M : W.Modules) :
    (Scheme.Modules.pullback f).map ((pullbackComp g h).inv.app M) ≫
        (pullbackComp f g).hom.app ((Scheme.Modules.pullback h).obj M) ≫
          (pullbackComp (f ≫ g) h).hom.app M =
      (pullbackComp f (g ≫ h)).hom.app M ≫ eqToHom (by rw [Category.assoc]) := by
  rw [← cancel_epi ((Scheme.Modules.pullback f).map ((pullbackComp g h).hom.app M)),
    ← Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp,
    reassoc_of% (pullbackComp_assoc_app f g h M)]
  simp

lemma pullbackComp_assoc_inv₂ (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) (M : W.Modules) :
    (pullbackComp f g).inv.app ((Scheme.Modules.pullback h).obj M) ≫
        (Scheme.Modules.pullback f).map ((pullbackComp g h).hom.app M) ≫
          (pullbackComp f (g ≫ h)).hom.app M =
      (pullbackComp (f ≫ g) h).hom.app M ≫ eqToHom (by rw [Category.assoc]) := by
  rw [pullbackComp_assoc_app, Iso.inv_hom_id_app_assoc]

/-- `g^* m^* M ≅ m^* g^* M` for `g ≫ m = m ≫ g`. -/
def Qiso (g m : X ⟶ X) (hb : g ≫ m = m ≫ g) (M : X.Modules) :
    (Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback m).obj M) ≅
      (Scheme.Modules.pullback m).obj ((Scheme.Modules.pullback g).obj M) :=
  (pullbackComp g m).app M ≪≫ (pullbackCongr hb).app M ≪≫ ((pullbackComp m g).app M).symm

/-- `t'^* g^* ≅ g^* t^*` for `t' ≫ g = g ≫ t`. -/
def Niso (t' g t : X ⟶ X) (ha : t' ≫ g = g ≫ t) :
    Scheme.Modules.pullback g ⋙ Scheme.Modules.pullback t' ≅
      Scheme.Modules.pullback t ⋙ Scheme.Modules.pullback g :=
  pullbackComp t' g ≪≫ pullbackCongr ha ≪≫ (pullbackComp g t).symm

/-- **Coherence (II).** -/
lemma coherence_II (t' g m t : X ⟶ X) (ha : t' ≫ g = g ≫ t) (hb : g ≫ m = m ≫ g)
    (h : t ≫ m = m) (h' : t' ≫ m = m) (M : X.Modules) :
    (Niso t' g t ha).inv.app ((Scheme.Modules.pullback m).obj M) ≫
        (Scheme.Modules.pullback t').map (Qiso g m hb M).hom ≫
          (pullbackComp t' m).hom.app ((Scheme.Modules.pullback g).obj M) ≫
            (pullbackCongr h').hom.app ((Scheme.Modules.pullback g).obj M) ≫ (Qiso g m hb M).inv =
      (Scheme.Modules.pullback g).map
        ((pullbackComp t m).hom.app M ≫ (pullbackCongr h).hom.app M) := by
  rw [← cancel_mono ((pullbackComp g m).hom.app M)]
  simp only [Niso, Qiso, Iso.trans_inv, Iso.trans_hom, Iso.symm_inv, Iso.symm_hom, Iso.app_hom,
    Iso.app_inv, NatTrans.comp_app, Functor.map_comp, Category.assoc, Iso.inv_hom_id_app,
    Category.comp_id, pullbackCongr_hom_app, pullbackCongr_inv_app]
  -- RHS
  rw [map_eqToHom_comp_pullbackComp g h M, reassoc_of% (pullbackComp_assoc_app g t m M)]
  -- LHS
  rw [reassoc_of% (eqToHom_comp_pullbackComp h' g M)]
  rw [reassoc_of% (pullbackComp_assoc_inv₁ t' m g M)]
  rw [reassoc_of% (map_eqToHom_comp_pullbackComp t' hb M)]
  rw [reassoc_of% (pullbackComp_assoc_inv₂ t' g m M)]
  rw [reassoc_of% (eqToHom_comp_pullbackComp ha.symm m M)]
  simp

/-- `pullbackObjUnitIso` with its type stated through `Scheme.Modules.unit`. -/
def pOU (f : X ⟶ Y) : (Scheme.Modules.pullback f).obj (unit Y) ≅ unit X := pullbackObjUnitIso f

lemma pOU_comp (f : X ⟶ Y) (h : Y ⟶ Z) :
    (pullbackComp f h).inv.app (unit Z) ≫ (Scheme.Modules.pullback f).map (pOU h).hom ≫
      (pOU f).hom = (pOU (f ≫ h)).hom :=
  pullbackObjUnitIso_comp f h

lemma pOU_conj (h : Y ⟶ X) (f : unit X ⟶ unit X) :
    ((pOU h).inv ≫ (Scheme.Modules.pullback h).map f ≫ (pOU h).hom).app ⊤ (1 : Γ(Y, ⊤)) =
      h.appTop (f.app ⊤ (1 : Γ(X, ⊤))) :=
  pullbackObjUnitIso_conj_app_top h f

lemma pOU_inv_comp (f : X ⟶ Y) (h : Y ⟶ Z) :
    (pOU (f ≫ h)).inv = (pOU f).inv ≫
      (Scheme.Modules.pullback f).map (pOU h).inv ≫ (pullbackComp f h).hom.app (unit _) := by
  refine Iso.inv_ext ?_
  rw [← pOU_comp f h]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]
  exact Iso.inv_hom_id_app _ _

lemma pOU_inv_congr {f f' : X ⟶ Y} (e : f = f') :
    (pOU f).inv ≫ (pullbackCongr e).hom.app (unit _) = (pOU f').inv := by
  subst e; simp [pullbackCongr]

set_option maxHeartbeats 1600000 in
/-- **Coherence (I).** -/
lemma coherence_I (t' g t : X ⟶ X) (ha : t' ≫ g = g ≫ t) :
    (pOU t').inv ≫ (Scheme.Modules.pullback t').map (pOU g).inv ≫
        (Niso t' g t ha).hom.app (unit _) =
      (pOU g).inv ≫ (Scheme.Modules.pullback g).map (pOU t).inv := by
  simp only [Niso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  rw [← reassoc_of% (pOU_inv_comp t' g), reassoc_of% (pOU_inv_congr ha), pOU_inv_comp g t]
  simp

/-- The generic Weil formula. -/
def wf (t m : X ⟶ X) (h : t ≫ m = m) (M : X.Modules)
    (ψ : unit X ≅ (Scheme.Modules.pullback m).obj M) : Γ(X, ⊤) :=
  unitHomAddEquiv (unit X) ((pOU t).inv ≫ (Scheme.Modules.pullback t).map ψ.hom ≫
    (pullbackComp t m).hom.app M ≫ (pullbackCongr h).hom.app M ≫ ψ.inv)

/-- The transported trivialization. -/
def transTriv (g m : X ⟶ X) (hb : g ≫ m = m ≫ g) (M : X.Modules)
    (ψ : unit X ≅ (Scheme.Modules.pullback m).obj M) :
    unit X ≅ (Scheme.Modules.pullback m).obj ((Scheme.Modules.pullback g).obj M) :=
  (pOU g).symm ≪≫ (Scheme.Modules.pullback g).mapIso ψ ≪≫ Qiso g m hb M

/-- **Transport of Mumford's formula along `g`.** -/
theorem wf_transport (t' g m t : X ⟶ X) (ha : t' ≫ g = g ≫ t) (hb : g ≫ m = m ≫ g)
    (h : t ≫ m = m) (h' : t' ≫ m = m) (M : X.Modules)
    (ψ : unit X ≅ (Scheme.Modules.pullback m).obj M) :
    wf t' m h' ((Scheme.Modules.pullback g).obj M) (transTriv g m hb M ψ) =
      g.appTop (wf t m h M ψ) := by
  simp only [wf, unitHomAddEquiv_apply]
  rw [← pOU_conj g]
  congr 2
  have nat := (Niso t' g t ha).hom.naturality ψ.hom
  have e1 : (Scheme.Modules.pullback t').map ((Scheme.Modules.pullback g).map ψ.hom) =
      (Niso t' g t ha).hom.app _ ≫ (Scheme.Modules.pullback g).map ((Scheme.Modules.pullback t).map ψ.hom) ≫
        (Niso t' g t ha).inv.app _ := by
    simp only [Functor.comp_map] at nat
    rw [← Category.assoc, ← nat]; simp
  simp only [transTriv, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Functor.mapIso_hom,
    Functor.mapIso_inv, Functor.map_comp, Category.assoc]
  rw [e1]
  simp only [Category.assoc]
  rw [reassoc_of% (coherence_I t' g t ha)]
  have h2 := coherence_II t' g m t ha hb h h' M
  simp only [Functor.map_comp] at h2
  rw [reassoc_of% h2]

/-- Invariance under isomorphisms of the module. -/
theorem wf_iso (t m : X ⟶ X) (h : t ≫ m = m) {M₁ M₂ : X.Modules} (e : M₁ ≅ M₂)
    (ψ : unit X ≅ (Scheme.Modules.pullback m).obj M₁) :
    wf t m h M₂ (ψ ≪≫ (Scheme.Modules.pullback m).mapIso e) = wf t m h M₁ ψ := by
  have n1 := (pullbackComp t m).hom.naturality e.hom
  have n2 := (pullbackCongr h).hom.naturality e.hom
  simp only [Functor.comp_map] at n1
  simp only [wf, Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom, Functor.mapIso_inv,
    Functor.map_comp, Category.assoc]
  rw [reassoc_of% n1, reassoc_of% n2]
  simp

end PicDict.Transport

namespace PicDict

open T09Pic PkgI3 PkgI3.AbVar HDec.WeilPairing CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

variable {K : Type} [Field K]

/-- `1 × Spec σ` on `A_K̄`. -/
abbrev gal (A : AbVar K) (σ : Gal K) : AK A ⟶ AK A :=
  JacobianChallenge.baseChangeMap A.X.hom (galHom σ)

lemma gal_eq (A : AbVar K) (σ : Gal K) : gal A σ = (A.X ◁ galHom σ).left := by
  apply Limits.pullback.hom_ext <;> simp [JacobianChallenge.baseChangeMap]

lemma transl_gal (A : AbVar K) (σ : Gal K) (x : A.Pt (AlgebraicClosure K)) :
    transl (galHom σ ≫ x) ≫ (A.X ◁ galHom σ) = (A.X ◁ galHom σ) ≫ transl x := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [transl, CartesianMonoidalCategory.comp_lift_assoc]
  · simp [transl]

lemma gal_transl (A : AbVar K) (σ : Gal K) (x : A.Pt (AlgebraicClosure K)) :
    trl (galHom σ ≫ x) ≫ gal A σ = gal A σ ≫ trl x := by
  rw [gal_eq, ← Over.comp_left, ← Over.comp_left, transl_gal]

lemma gal_mulN (A : AbVar K) (σ : Gal K) (n : ℕ) : gal A σ ≫ mlN A n = mlN A n ≫ gal A σ := by
  rw [gal_eq, ← Over.comp_left, ← Over.comp_left]
  congr 1
  unfold mulN
  exact whisker_exchange _ _

lemma gal_constK (A : AbVar K) (σ : Gal K) (u : AlgebraicClosure K) :
    (gal A σ).appTop (constK A u) = constK A (σ u) := by
  have hs : gal A σ ≫ Limits.pullback.snd A.X.hom (ptK K).hom =
      Limits.pullback.snd A.X.hom (ptK K).hom ≫ (galHom σ).left := Limits.pullback.lift_snd _ _ _
  simp only [constK, RingHom.comp_apply]
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hs, Scheme.Hom.comp_appTop,
    CommRingCat.comp_apply]
  congr 1
  have := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (σ : AlgebraicClosure K →+* AlgebraicClosure K))
  exact (congrArg (fun φ => φ.hom u) this).symm

lemma weilFormula_eq_wf {A : AbVar K} {n : ℕ} (x : tors A n) (c : (AK A).Pic) (ψ : Triv A n c) :
    weilFormula x c ψ = Transport.wf (trl (Additive.toMul (x : P A))) (mlN A n)
      (transl_left_comp_mulN_left x) (mod c) ψ := rfl

/-- **GLUE, proved form**: transport along `σ ∈ G_K`. -/
def WeilFormulaGaloisEx : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (n : ℕ) (σ : Gal K) (x : tors A n) (c c' : (AK A).Pic),
      c' = Scheme.Pic.map (gal A σ) c →
      ∀ (ψ : Triv A n c) (u : AlgebraicClosure K),
        weilFormula x c ψ = constK A u →
          ∃ ψ' : Triv A n c', weilFormula (galTors A n σ x) c' ψ' = constK A (σ u)

theorem weilFormulaGaloisEx : WeilFormulaGaloisEx := by
  intro K _ A n σ x c c' hc ψ u hu
  subst hc
  let e : (Scheme.Modules.pullback (gal A σ)).obj (mod c) ≅ mod (Scheme.Pic.map (gal A σ) c) :=
    (Scheme.Pic.mkIso _).symm
  refine ⟨Transport.transTriv (gal A σ) (mlN A n) (gal_mulN A σ n) (mod c) ψ ≪≫
    (Scheme.Modules.pullback (mlN A n)).mapIso e, ?_⟩
  have ha : (transl (Additive.toMul ((galTors A n σ x : tors A n) : P A))).left ≫ gal A σ =
      gal A σ ≫ trl (Additive.toMul (x : P A)) := gal_transl A σ _
  have h1 := Transport.wf_iso (transl (Additive.toMul ((galTors A n σ x : tors A n) : P A))).left (mlN A n)
    (transl_left_comp_mulN_left (galTors A n σ x)) e
    (Transport.transTriv (gal A σ) (mlN A n) (gal_mulN A σ n) (mod c) ψ)
  have h2 := Transport.wf_transport (transl (Additive.toMul ((galTors A n σ x : tors A n) : P A))).left
    (gal A σ) (mlN A n) (trl (Additive.toMul (x : P A))) ha (gal_mulN A σ n)
    (transl_left_comp_mulN_left x) (transl_left_comp_mulN_left (galTors A n σ x)) (mod c) ψ
  have h3 : weilFormula x c ψ = Transport.wf (trl (Additive.toMul (x : P A))) (mlN A n)
    (transl_left_comp_mulN_left x) (mod c) ψ := rfl
  have h4 := weilFormula_eq_wf (galTors A n σ x) (Scheme.Pic.map (gal A σ) c)
      (Transport.transTriv (gal A σ) (mlN A n) (gal_mulN A σ n) (mod c) ψ ≪≫
        (Scheme.Modules.pullback (mlN A n)).mapIso e)
  rw [h4, h1, h2, ← h3, hu]
  exact gal_constK A σ u

end PicDict
#print axioms PicDict.weilFormulaGaloisEx
