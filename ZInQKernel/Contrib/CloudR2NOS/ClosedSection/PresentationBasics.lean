/-
Copyright (c) 2026 H5/NOS Round-2 lane4 contributors.
Released under Apache 2.0 license as described in the project LICENSE.

H5 closed-section presentation primitives. SOURCE ONLY, UNCOMPILED. Native HELD.
No kernel/ABI/admission grade is claimed.

Proved here (no sub-gap):
* `presentationOfIso` — closes GM11 sub-gap (G7) `PresentationOfIso`;
* the four FBS primitives of C3 () `Step1/FBSRestrict.lean` (sha256 69f9bc78…), restated
  VERBATIM as theorems so that C3's defs follow by `exact`:
  `projPresentationPullback` (= `ProjPresentationPullback`), `fbsIsoInvariant`
  (= `FBSIsoInvariant`), `fbsNonzeroSection` (= `FBSNonzeroSection`), `fbsUnitFinite`
  (= `FBSUnitFinite`, using C3's proved `appTop_bijective_of_isAbelianVariety`, PicZeroSections
  da09e4df…).

Portions ADAPTED (namespaces, P2M macros removed, ported FLT names substituted; mathematics and
proof structure unchanged) from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2,
Apache-2.0, read-only clone of the upstream FLT repository:
* `P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_of_iso.lean` (`PresIso`;
  upstream sha256 5c1554e3d58298620b3a75b25066d5df56a99b6863b438514f217b35b935ed3d);
* `P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_bijective_smul_unit_app_of_bijective_smul.lean`
  (`FramePullback`; upstream sha256 f8811956171c97972e2492d4bcda1ca33b686b5b6c49e04d9768b6f185ac7f05);
* `P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_mem_preimage_basicOpen_iff.lean`
  (`PresChart`; upstream sha256 e79b7aabd7b44d8a6540f542197d89d97a240d6f82d56e4ec59c0779f9fda2fd).
No upstream option overrides were present; only `autoImplicit false` here.
No wholesale port, no compile of the FLT closure, default limits. FLT definitions are the
lead-bound historical port names (namespace `ZInQ.Contrib.CloudW03NeronSurj.FLT`).
EDITION 2 (2026-11-17, rqprobe7 run b64001ed, first compile of this file). Statements unchanged:
  * 465:41 parse: `𝟙_` is `scoped notation` in CategoryTheory.MonoidalCategory (Mathlib Monoidal/Category.lean l.130)
  * 214:19/215:24/225:12: `(SheafOfModules.pushforward p.toRingCatSheafHom).IsRightAdjoint` supplied from the Mathlib adjunction (local instance)
  * 307:6: `Ideal.primeCompl` needs the IsPrime instance; supplied from the ProjectiveSpectrum field `isPrime`
  * 424:9: the `change` pattern's `_` holes left the HSMul instance problem stuck; all opens/arguments are now explicit (same term: `(j ≫ T).app U = T.app U ≫ j.app (T ⁻¹ᵁ U)` by rfl)
  The 228/235 heartbeat errors in `unitIso_hom_comp_frameHom` are expected to be cascades of the
  missing adjunction instance (re-probe). Supersedes beb3097f (kept frozen).
EDITION 3 (2026-11-17, rqprobe8 run b64001ed). Statements unchanged:
  * 225/231: ed2's local IsRightAdjoint theorem (universe mismatch) removed; unitIso now follows W07's compiled pullbackObjUnitIso pattern (Final instance + universe-pinned asIso)
  * 261: `rw [unitToPushforwardObjUnit_val_app_apply]` dropped — the lemma is `rfl` (PullbackFree.lean l.68–69) and the following `change` performs the same conversion by defeq
  * 348: `mapId` (an abbrev for `map (.id _) h`, HomogeneousLocalization.lean l.694–696) is unfolded before `map_mk` (l.698–700)
  * 452: the `change` now restricts from `j ⁻¹ᵁ ⊤` exactly as `FramePullback.res_eta` states it (`j.preimage_mono h`), so `rw [hi, hk]` matches syntactically
  * 531: under `open MonObj`, bare `mul_assoc`/`mul_one` resolve to the monoid-OBJECT lemmas (`μ ▷ X ≫ μ = …`); the ring lemmas are named `_root_.`
  Supersedes be05e193 and beb3097f (both kept frozen).
-/
import ZInQKernel.Contrib.CloudR2NOS.ClosedSection.Step3Gaps
import ZInQKernel.Contrib.CloudR2NOS.Step1.PicZeroSections
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Cohomology.Basic
import ZInQKernel.HDecomp.Objects
import Mathlib

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open MonObj
open scoped CategoryTheory.MonoidalCategory

attribute [local instance] MvPolynomial.gradedAlgebra

namespace ZInQ.Contrib.CloudR2NOS.ClosedSection.PresentationBasics

local notation "Pres" => ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.ProjPresentation
local notation "FBS'" => ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.FiniteBySections
local notation "FLTratio" => ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.ProjSpace.ratio
local notation "FLTirrel" =>
  ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.ProjSpace.irrelevant_le_span_X

/-! ### Restriction helpers -/

/-- Restriction of a section of a module sheaf. -/
noncomputable abbrev res {Z : Scheme.{u}} (N : Z.Modules) {W' W : Z.Opens} (h : W' ≤ W)
    (s : Γ(N, W)) : Γ(N, W') :=
  N.presheaf.map (homOfLE h).op s

/-- Restriction of a global section. -/
noncomputable abbrev resTop {Z : Scheme.{u}} (N : Z.Modules) (W : Z.Opens) (s : Γ(N, ⊤)) :
    Γ(N, W) :=
  N.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op s

theorem res_res {Z : Scheme.{u}} (N : Z.Modules) {W₁ W₂ W₃ : Z.Opens} (h₂₁ : W₂ ≤ W₁)
    (h₃₂ : W₃ ≤ W₂) (s : Γ(N, W₁)) : res N h₃₂ (res N h₂₁ s) = res N (h₃₂.trans h₂₁) s := by
  change (N.presheaf.map (homOfLE h₂₁).op ≫ N.presheaf.map (homOfLE h₃₂).op) s = _
  rw [← CategoryTheory.Functor.map_comp]
  rfl

theorem res_resTop {Z : Scheme.{u}} (N : Z.Modules) {W W' : Z.Opens} (h : W' ≤ W)
    (s : Γ(N, ⊤)) : res N h (resTop N W s) = resTop N W' s :=
  res_res N le_top h s

/-- `res_resTop` with the literal `presheaf.map` head (as in FLT `PresChart.res_resTop`). -/
theorem map_resTop {Z : Scheme.{u}} (N : Z.Modules) {W W' : Z.Opens} (h : W' ≤ W)
    (s : Γ(N, ⊤)) : N.presheaf.map (homOfLE h).op (resTop N W s) = resTop N W' s :=
  res_resTop N h s

theorem res_eq_map {Z : Scheme.{u}} (N : Z.Modules) {W' W : Z.Opens} (f : W' ⟶ W)
    (s : Γ(N, W)) : N.presheaf.map f.op s = res N f.le s := by
  rw [Subsingleton.elim f (homOfLE f.le)]

theorem res_smul {Z : Scheme.{u}} (N : Z.Modules) {W' W : Z.Opens} (h : W' ≤ W) (r : Γ(Z, W))
    (x : Γ(N, W)) : res N h (r • x) = Z.presheaf.map (homOfLE h).op r • res N h x :=
  Scheme.Modules.map_smul N (homOfLE h) r x

theorem app_res {Z : Scheme.{u}} {N N' : Z.Modules} (φ : N ⟶ N') {W' W : Z.Opens} (h : W' ≤ W)
    (s : Γ(N, W)) : φ.app W' (res N h s) = res N' h (φ.app W s) := by
  have hnat := φ.mapPresheaf.naturality (homOfLE h).op
  have hx := ConcreteCategory.congr_hom hnat s
  simp only [ConcreteCategory.comp_apply, Scheme.Modules.mapPresheaf_app] at hx
  exact hx

/-! ### (G7) transport along a module isomorphism (adapted FLT `PresIso`) -/

theorem map_app {X : Scheme.{u}} {M M' : X.Modules} (φ : M ⟶ M') {U V : X.Opens} (i : V ⟶ U)
    (s : Γ(M, U)) : M'.presheaf.map i.op (φ.app U s) = φ.app V (M.presheaf.map i.op s) := by
  have h := φ.mapPresheaf.naturality i.op
  have := congrArg (fun f => (ConcreteCategory.hom f) s) h
  simpa using this.symm

/-- The presentation transported along a module isomorphism (same map, transported sections). -/
noncomputable def transport {R : Type u} [CommRing R] {X : Scheme.{u}}
    {f : X ⟶ Spec (CommRingCat.of R)} {M M' : X.Modules} {N : ℕ} (𝔓 : Pres M f N)
    (e : M ≅ M') : Pres M' f N where
  σ := fun i => e.hom.app ⊤ (𝔓.σ i)
  toProj := 𝔓.toProj
  toProj_π := 𝔓.toProj_π
  frame := fun i V hV => by
    have key : (fun g : Γ(X, V) =>
          g • M'.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (e.hom.app ⊤ (𝔓.σ i))) =
        (e.hom.app V) ∘
          (fun g : Γ(X, V) => g • M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (𝔓.σ i)) := by
      funext g
      simp only [Function.comp_apply, map_app, Scheme.Modules.Hom.app_smul]
    rw [key]
    exact (ConcreteCategory.bijective_of_isIso (e.hom.app V)).comp (𝔓.frame i V hV)
  app_ratio_smul := fun i j => by
    rw [map_app, map_app, ← Scheme.Modules.Hom.app_smul, 𝔓.app_ratio_smul i j]

/-- **(G7) proved.** -/
theorem presentationOfIso : PresentationOfIso.{u} := by
  intro R _ X f M M' N 𝔓 e
  exact ⟨transport 𝔓 e, rfl, fun _ => rfl⟩

/-! ### Frames pull back (adapted FLT `FramePullback`) -/

namespace FramePullback

local instance opensMap_final' {X Y : Scheme.{u}} (f : X ⟶ Y) : (Opens.map f.base).Final :=
  CategoryTheory.final_of_representablyFlat _

/-- The structure sheaf as a module. -/
noncomputable abbrev unitMod (Z : Scheme.{u}) : Z.Modules := SheafOfModules.unit Z.ringCatSheaf

/-- `𝒪_Z ⟶ N`, `g ↦ g • s`, for a global section `s`. -/
noncomputable def frameHom {Z : Scheme.{u}} (N : Z.Modules) (s : Γ(N, ⊤)) : unitMod Z ⟶ N :=
  ⟨PresheafOfModules.homMk
    { app := fun W => AddCommGrpCat.ofHom (X := Γ(Z, W.unop)) (Y := Γ(N, W.unop))
        { toFun := fun g : Γ(Z, W.unop) => g • resTop N W.unop s
          map_zero' := zero_smul _ _
          map_add' := fun g g' => add_smul g g' _ }
      naturality := fun {W W'} f => by
        have hf : f = (homOfLE f.unop.le).op := congrArg Quiver.Hom.op (Subsingleton.elim _ _)
        rw [hf]
        ext g
        change ((Z.presheaf.map (homOfLE f.unop.le).op : Γ(Z, W.unop) ⟶ Γ(Z, W'.unop)) g) •
            resTop N W'.unop s = res N f.unop.le ((show Γ(Z, W.unop) from g) • resTop N W.unop s)
        rw [res_smul, res_resTop] }
    (fun W (r : Γ(Z, W.unop)) (g : Γ(Z, W.unop)) => by
      change (r * g) • resTop N W.unop s = r • (g • resTop N W.unop s)
      exact mul_smul r g _)⟩

theorem isIso_restrict_frameHom {Z : Scheme.{u}} (N : Z.Modules) (s : Γ(N, ⊤)) {V : Z.Opens}
    (hs : ∀ W : Z.Opens, W ≤ V → Function.Bijective fun g : Γ(Z, W) => g • resTop N W s) :
    IsIso ((Scheme.Modules.restrictFunctor V.ι).map (frameHom N s)) := by
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro W
  change IsIso ((frameHom N s).app (V.ι ''ᵁ W))
  rw [ConcreteCategory.isIso_iff_bijective]
  exact hs (V.ι ''ᵁ W) (V.ι_image_le W)

theorem isIso_pullback_frameHom {Z : Scheme.{u}} (N : Z.Modules) (s : Γ(N, ⊤)) {V : Z.Opens}
    (hs : ∀ W : Z.Opens, W ≤ V → Function.Bijective fun g : Γ(Z, W) => g • resTop N W s) :
    IsIso ((Scheme.Modules.pullback V.ι).map (frameHom N s)) :=
  (NatIso.isIso_map_iff (Scheme.Modules.restrictFunctorIsoPullback V.ι) (frameHom N s)).mp
    (isIso_restrict_frameHom N s hs)

section pullback

variable {X X' : Scheme.{u}} (p : X' ⟶ X) (M : X.Modules)

/-- The pulled-back module. -/
noncomputable abbrev F : X'.Modules := (Scheme.Modules.pullback p).obj M

/-- The literal pulled-back section (adjunction unit). -/
noncomputable def eta (U : X.Opens) (m : Γ(M, U)) : Γ(F p M, p ⁻¹ᵁ U) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M).app U m

theorem eta_smul (U : X.Opens) (r : Γ(X, U)) (m : Γ(M, U)) :
    eta p M U (r • m) = p.app U r • eta p M U m :=
  Scheme.Modules.Hom.app_smul _ r m

theorem res_eta {U U' : X.Opens} (h : U' ≤ U) (m : Γ(M, U)) :
    res (F p M) (p.preimage_mono h) (eta p M U m) = eta p M U' (res M h m) := by
  have hnat := ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M).mapPresheaf.naturality
    (homOfLE h).op
  have hx := ConcreteCategory.congr_hom hnat m
  simp only [ConcreteCategory.comp_apply, Scheme.Modules.mapPresheaf_app] at hx
  exact ((res_eq_map (F p M) ((Opens.map p.base).map (homOfLE h)) _).symm).trans hx.symm

theorem isIso_pullback_pullback_frameHom (s : Γ(M, ⊤)) {V : X.Opens}
    (hs : ∀ W : X.Opens, W ≤ V → Function.Bijective fun g : Γ(X, W) => g • resTop M W s) :
    IsIso ((Scheme.Modules.pullback (p ⁻¹ᵁ V).ι).map
      ((Scheme.Modules.pullback p).map (frameHom M s))) := by
  have hfact : (p ⁻¹ᵁ V).ι ≫ p = (p ∣_ V) ≫ V.ι := (morphismRestrict_ι p V).symm
  let e : Scheme.Modules.pullback p ⋙ Scheme.Modules.pullback (p ⁻¹ᵁ V).ι ≅
      Scheme.Modules.pullback V.ι ⋙ Scheme.Modules.pullback (p ∣_ V) :=
    Scheme.Modules.pullbackComp _ _ ≪≫ Scheme.Modules.pullbackCongr hfact ≪≫
      (Scheme.Modules.pullbackComp _ _).symm
  have h1 : IsIso ((Scheme.Modules.pullback V.ι ⋙ Scheme.Modules.pullback (p ∣_ V)).map
      (frameHom M s)) := by
    change IsIso ((Scheme.Modules.pullback (p ∣_ V)).map
      ((Scheme.Modules.pullback V.ι).map (frameHom M s)))
    haveI := isIso_pullback_frameHom M s hs
    infer_instance
  exact (NatIso.isIso_map_iff e (frameHom M s)).mpr h1

/-- `p^* 𝒪_X ≅ 𝒪_{X'}` (the W07 `Scheme.Modules.pullbackObjUnitIso` pattern, W07
Jacobian/AlgebraicGeometry/Modules/Invertible.lean l.35–40: `Opens.map p.base` is final, so Mathlib's
`IsIso (pullbackObjUnitToUnit _)` instance (ModuleCat/Sheaf/PullbackFree.lean l.101) applies; the module universe is
pinned by `(C := SheafOfModules.{u} _)`). -/
noncomputable def unitIso : (Scheme.Modules.pullback p).obj (unitMod X) ≅ unitMod X' := by
  letI : (Opens.map p.base).Final := ⟨fun _ ↦ IsCofiltered.isConnected _⟩
  exact asIso (C := SheafOfModules.{u} X'.ringCatSheaf)
    (SheafOfModules.pullbackObjUnitToUnit p.toRingCatSheafHom)

theorem unitIso_hom_comp_frameHom (s : Γ(M, ⊤)) :
    (unitIso p).hom ≫ frameHom (F p M) (eta p M ⊤ s) =
      (Scheme.Modules.pullback p).map (frameHom M s) := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction p).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  have hu : (Scheme.Modules.pullbackPushforwardAdjunction p).unit.app _ ≫
      (Scheme.Modules.pushforward p).map (unitIso p).hom =
        SheafOfModules.unitToPushforwardObjUnit p.toRingCatSheafHom := by
    have := SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
      p.toRingCatSheafHom
    rw [Adjunction.homEquiv_unit] at this
    exact this
  have h' : (Scheme.Modules.pullbackPushforwardAdjunction p).unit.app _ ≫
      (Scheme.Modules.pushforward p).map ((unitIso p).hom ≫ frameHom (F p M) (eta p M ⊤ s)) =
        SheafOfModules.unitToPushforwardObjUnit p.toRingCatSheafHom ≫
          (Scheme.Modules.pushforward p).map (frameHom (F p M) (eta p M ⊤ s)) := by
    rw [← hu]
    rfl
  have hn := (Scheme.Modules.pullbackPushforwardAdjunction p).unit.naturality (frameHom M s)
  have KEY : SheafOfModules.unitToPushforwardObjUnit p.toRingCatSheafHom ≫
      (Scheme.Modules.pushforward p).map (frameHom (F p M) (eta p M ⊤ s)) =
        frameHom M s ≫ (Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M := by
    refine Scheme.Modules.hom_ext _ _ fun W => ?_
    ext g
    change (frameHom (F p M) (eta p M ⊤ s)).app (p ⁻¹ᵁ W)
        ((SheafOfModules.unitToPushforwardObjUnit p.toRingCatSheafHom).val.app (op W) g) =
      eta p M W ((frameHom M s).app W g)
    change ((p.app W : Γ(X, W) ⟶ Γ(X', p ⁻¹ᵁ W)) g) • resTop (F p M) (p ⁻¹ᵁ W) (eta p M ⊤ s) =
      eta p M W ((show Γ(X, W) from g) • resTop M W s)
    rw [eta_smul]
    congr 1
    exact res_eta p M le_top s
  exact h'.trans (KEY.trans hn)

theorem frameHom_eta_eq (s : Γ(M, ⊤)) :
    frameHom (F p M) (eta p M ⊤ s) =
      (unitIso p).inv ≫ (Scheme.Modules.pullback p).map (frameHom M s) := by
  rw [← unitIso_hom_comp_frameHom, Iso.inv_hom_id_assoc]

theorem isIso_pullback_frameHom_eta (s : Γ(M, ⊤)) {V : X.Opens}
    (hs : ∀ W : X.Opens, W ≤ V → Function.Bijective fun g : Γ(X, W) => g • resTop M W s) :
    IsIso ((Scheme.Modules.pullback (p ⁻¹ᵁ V).ι).map (frameHom (F p M) (eta p M ⊤ s))) := by
  rw [frameHom_eta_eq, CategoryTheory.Functor.map_comp]
  haveI := isIso_pullback_pullback_frameHom p M s hs
  infer_instance

omit M in
theorem image_preimage_eq {W V : X'.Opens} (hW : W ≤ V) : V.ι ''ᵁ (V.ι ⁻¹ᵁ W) = W :=
  (Scheme.Hom.image_preimage_eq_opensRange_inf V.ι W).trans
    (by rw [Scheme.Opens.opensRange_ι]; exact inf_eq_right.mpr hW)

/-- **Frames pull back along any morphism.** -/
theorem main (s : Γ(M, ⊤)) {V : X.Opens}
    (hs : ∀ W : X.Opens, W ≤ V → Function.Bijective fun g : Γ(X, W) => g • resTop M W s)
    (W' : X'.Opens) (hW' : W' ≤ p ⁻¹ᵁ V) :
    Function.Bijective fun g : Γ(X', W') => g • resTop (F p M) W' (eta p M ⊤ s) := by
  have h1 := isIso_pullback_frameHom_eta p M s hs
  have h2 : IsIso ((Scheme.Modules.restrictFunctor (p ⁻¹ᵁ V).ι).map
      (frameHom (F p M) (eta p M ⊤ s))) :=
    (NatIso.isIso_map_iff (Scheme.Modules.restrictFunctorIsoPullback (p ⁻¹ᵁ V).ι) _).mpr h1
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app] at h2
  have h3 : IsIso ((frameHom (F p M) (eta p M ⊤ s)).app
      ((p ⁻¹ᵁ V).ι ''ᵁ ((p ⁻¹ᵁ V).ι ⁻¹ᵁ W'))) :=
    h2 ((p ⁻¹ᵁ V).ι ⁻¹ᵁ W')
  rw [image_preimage_eq hW'] at h3
  exact ConcreteCategory.bijective_of_isIso ((frameHom (F p M) (eta p M ⊤ s)).app W')

end pullback

end FramePullback

/-! ### Charts of a presentation (adapted FLT `PresChart`) -/

namespace PresChart

variable (R : Type u) [CommRing R] (N : ℕ)

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R

theorem isUnit_germ_ratio_iff (i j : Fin (N + 1))
    (y : Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R))
    (hy : y ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
      (MvPolynomial.X j)) :
    IsUnit ((Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)).presheaf.germ
        (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X j)) y hy
        (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X j)
          (FLTratio R N j i))) ↔
      y ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i) := by
  haveI : y.asHomogeneousIdeal.toIdeal.IsPrime := y.isPrime
  have hle : Submonoid.powers (MvPolynomial.X j : MvPolynomial (Fin (N + 1)) R) ≤
      y.asHomogeneousIdeal.toIdeal.primeCompl :=
    Submonoid.powers_le.mpr ((Proj.mem_basicOpen _ _ y).mp hy)
  have h := ConcreteCategory.congr_hom
    (ProjectiveSpectrum.Proj.awayToSection_germ (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
      (MvPolynomial.X j) y hy) (FLTratio R N j i)
  have h' : (Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)).presheaf.germ
      (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X j)) y hy
      (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X j)
        (FLTratio R N j i)) =
      (Proj.stalkIso' (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) y).symm
        (HomogeneousLocalization.mapId (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) hle
          (FLTratio R N j i)) := h
  have e1 : IsUnit ((Proj.stalkIso' (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) y).symm
        (HomogeneousLocalization.mapId (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) hle
          (FLTratio R N j i))) ↔
      IsUnit (HomogeneousLocalization.mapId (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) hle
        (FLTratio R N j i)) :=
    ⟨fun hu => by simpa using hu.map (Proj.stalkIso' (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) y),
      fun hu => hu.map _⟩
  rw [h']
  refine e1.trans ?_
  rw [← HomogeneousLocalization.isUnit_iff_isUnit_val,
    ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.ProjSpace.ratio,
    HomogeneousLocalization.Away.mk, HomogeneousLocalization.mapId, HomogeneousLocalization.map_mk,
    HomogeneousLocalization.val_mk,
    Localization.mk_eq_mk', IsLocalization.AtPrime.isUnit_mk'_iff, Proj.mem_basicOpen]
  exact Iff.rfl

theorem exists_mem_basicOpen_X (y : Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)) :
    ∃ j : Fin (N + 1),
      y ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X j) := by
  have htop := Proj.iSup_basicOpen_eq_top (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
    (MvPolynomial.X : Fin (N + 1) → MvPolynomial (Fin (N + 1)) R) (FLTirrel R N)
  have hy : y ∈ (⊤ : (Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)).Opens) := trivial
  rw [← htop] at hy
  exact Opens.mem_iSup.mp hy

variable {R N}

/-- **Charts of a presentation**: `x` lies over `D₊(Xᵢ)` iff `σ i` generates near `x`. -/
theorem mem_preimage_basicOpen_iff {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}
    {M : X.Modules} (𝔓 : Pres M f N) (i : Fin (N + 1)) (x : X) :
    x ∈ 𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
        (MvPolynomial.X i) ↔
      ∃ U : X.Opens, x ∈ U ∧ ∀ V : X.Opens, V ≤ U →
        Function.Bijective fun g : Γ(X, V) => g • resTop M V (𝔓.σ i) := by
  constructor
  · intro hx
    exact ⟨_, hx, fun V hV => 𝔓.frame i V hV⟩
  · rintro ⟨U, hxU, hU⟩
    obtain ⟨j, hj⟩ := exists_mem_basicOpen_X R N (𝔓.toProj x)
    have hxW : x ∈ U ⊓ 𝔓.toProj ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X j) := ⟨hxU, hj⟩
    have hWU : U ⊓ 𝔓.toProj ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X j) ≤ U := inf_le_left
    have hWj : U ⊓ 𝔓.toProj ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X j) ≤
        𝔓.toProj ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X j) := inf_le_right
    have hρ : X.presheaf.map (homOfLE hWj).op
        (𝔓.toProj.app (Proj.basicOpen 𝒜 (MvPolynomial.X j))
          (Proj.awayToSection 𝒜 (MvPolynomial.X j) (FLTratio R N j i))) •
        resTop M (U ⊓ 𝔓.toProj ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X j)) (𝔓.σ j) =
        resTop M (U ⊓ 𝔓.toProj ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X j)) (𝔓.σ i) := by
      have h := congrArg (M.presheaf.map (homOfLE hWj).op) (𝔓.app_ratio_smul j i)
      rw [Scheme.Modules.map_smul, map_resTop, map_resTop] at h
      exact h
    obtain ⟨g, hg⟩ := (hU _ hWU).2
      (resTop M (U ⊓ 𝔓.toProj ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X j)) (𝔓.σ j))
    dsimp only at hg
    have h1 : (g * X.presheaf.map (homOfLE hWj).op
        (𝔓.toProj.app (Proj.basicOpen 𝒜 (MvPolynomial.X j))
          (Proj.awayToSection 𝒜 (MvPolynomial.X j) (FLTratio R N j i)))) •
        resTop M (U ⊓ 𝔓.toProj ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X j)) (𝔓.σ j) =
        (1 : Γ(X, U ⊓ 𝔓.toProj ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X j))) •
          resTop M (U ⊓ 𝔓.toProj ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X j)) (𝔓.σ j) := by
      rw [mul_smul, hρ, hg, one_smul]
    have hunit : IsUnit (X.presheaf.map (homOfLE hWj).op
        (𝔓.toProj.app (Proj.basicOpen 𝒜 (MvPolynomial.X j))
          (Proj.awayToSection 𝒜 (MvPolynomial.X j) (FLTratio R N j i)))) := by
      refine isUnit_iff_exists_inv.mpr ⟨g, ?_⟩
      rw [mul_comm]
      exact (𝔓.frame j _ hWj).1 h1
    have hgerm : IsUnit (X.presheaf.germ _ x hxW (X.presheaf.map (homOfLE hWj).op
        (𝔓.toProj.app (Proj.basicOpen 𝒜 (MvPolynomial.X j))
          (Proj.awayToSection 𝒜 (MvPolynomial.X j) (FLTratio R N j i))))) := hunit.map _
    rw [TopCat.Presheaf.germ_res_apply] at hgerm
    have hgerm' : IsUnit (X.presheaf.germ (𝔓.toProj ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X j)) x hj
        (𝔓.toProj.app (Proj.basicOpen 𝒜 (MvPolynomial.X j))
          (Proj.awayToSection 𝒜 (MvPolynomial.X j) (FLTratio R N j i)))) := hgerm
    rw [← Scheme.Hom.germ_stalkMap_apply] at hgerm'
    haveI : IsLocalHom (ConcreteCategory.hom (𝔓.toProj.stalkMap x)) :=
      inferInstanceAs (IsLocalHom (𝔓.toProj.stalkMap x).hom)
    rw [isUnit_map_iff] at hgerm'
    exact (isUnit_germ_ratio_iff R N i j _ hj).mp hgerm'

end PresChart

/-! ### C3's FBS primitives (statements verbatim from `Step1/FBSRestrict.lean` 69f9bc78) -/

/-- C3 `ProjPresentationPullback`: a presentation pulls back along ANY morphism, with
`toProj' = j ≫ toProj` and literal pulled-back sections. -/
theorem projPresentationPullback :
    ∀ {R : Type u} [CommRing R] {X Y : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (j : Y ⟶ X)
      (N : X.Modules) (n : ℕ) (𝔓 : Pres N f n),
      ∃ 𝔓' : Pres ((Scheme.Modules.pullback j).obj N) (j ≫ f) n,
        𝔓'.toProj = j ≫ 𝔓.toProj := by
  intro R _ X Y f j N n 𝔓
  refine ⟨
    { σ := fun i => show Γ((Scheme.Modules.pullback j).obj N, ⊤) from
          FramePullback.eta j N ⊤ (𝔓.σ i)
      toProj := j ≫ 𝔓.toProj
      toProj_π := by rw [Category.assoc, 𝔓.toProj_π]
      frame := fun i V hV =>
        FramePullback.main j N (𝔓.σ i) (fun W hW => 𝔓.frame i W hW) V hV
      app_ratio_smul := fun i k => ?_ }, rfl⟩
  have hi := FramePullback.res_eta j N
    (le_top : 𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      (MvPolynomial.X i) ≤ ⊤) (𝔓.σ i)
  have hk := FramePullback.res_eta j N
    (le_top : 𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      (MvPolynomial.X i) ≤ ⊤) (𝔓.σ k)
  change (j.app (𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (MvPolynomial.X i))
        (𝔓.toProj.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X i))
          (Proj.awayToSection _ (MvPolynomial.X i) (FLTratio R n i k)))) •
      res (FramePullback.F j N) (j.preimage_mono (le_top : 𝔓.toProj ⁻¹ᵁ
          Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X i) ≤ ⊤))
        (FramePullback.eta j N ⊤ (𝔓.σ i)) =
    res (FramePullback.F j N) (j.preimage_mono (le_top : 𝔓.toProj ⁻¹ᵁ
          Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X i) ≤ ⊤))
        (FramePullback.eta j N ⊤ (𝔓.σ k))
  rw [hi, hk, ← FramePullback.eta_smul]
  exact congrArg (FramePullback.eta j N _) (𝔓.app_ratio_smul i k)

/-- C3 `FBSIsoInvariant`. -/
theorem fbsIsoInvariant :
    ∀ {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K))
      (L L' : X.Modules), Nonempty (L ≅ L') → FBS' L f → FBS' L' f := by
  intro K _ X f L L' he hL
  obtain ⟨e⟩ := he
  obtain ⟨N, 𝔓, h⟩ := hL
  unfold ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.FiniteBySections
  exact ⟨N, transport 𝔓 e, h⟩

/-- A frame on an open containing a point is a nonzero section. -/
theorem ne_zero_of_frame {X : Scheme.{u}} (M : X.Modules) (σ : Γ(M, ⊤)) {U : X.Opens} {x : X}
    (hx : x ∈ U) (hU : Function.Bijective fun g : Γ(X, U) => g • resTop M U σ) : σ ≠ 0 := by
  intro hσ
  have h10 : (1 : Γ(X, U)) = 0 := hU.1 (by simp [hσ])
  have := congrArg (X.presheaf.germ U x hx).hom h10
  simp at this

/-- C3 `FBSNonzeroSection`. -/
theorem fbsNonzeroSection :
    ∀ {K : Type u} [Field K] {X : Scheme.{u}} [Nonempty X] (f : X ⟶ Spec (CommRingCat.of K))
      (L : X.Modules), FBS' L f → ¬ Subsingleton (L.H 0) := by
  intro K _ X _ f L hL hsub
  obtain ⟨N, 𝔓, -⟩ := hL
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  obtain ⟨i, hi⟩ := PresChart.exists_mem_basicOpen_X K N (𝔓.toProj x)
  have hne := ne_zero_of_frame L (𝔓.σ i) (U := 𝔓.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X i))
    hi (𝔓.frame i _ le_rfl)
  haveI := hsub
  haveI : Subsingleton (Γ(L, ⊤)) :=
    (Scheme.Modules.H.zeroLinearEquiv L).symm.injective.subsingleton
  exact hne (Subsingleton.elim _ _)

/-- C3 `FBSUnitFinite`. -/
theorem fbsUnitFinite :
    ∀ {K : Type u} [Field K] [IsAlgClosed K] (Y : Grp (Over (Spec (CommRingCat.of K))))
      [PkgI2.IsAbelianVariety Y], FBS' (𝟙_ Y.X.left.Modules) Y.X.hom → IsFinite Y.X.hom := by
  intro K _ _ Y _ hFBS
  obtain ⟨N, 𝔓, hfin⟩ := hFBS
  haveI : IsProper Y.X.hom := PkgI2.IsAbelianVariety.proper
  -- a point of `Y` (the unit section)
  let x : Y.X.left := (η[Y.X] : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ Y.X).left.base
    (default : Spec (CommRingCat.of K))
  obtain ⟨i, hi⟩ := PresChart.exists_mem_basicOpen_X K N (𝔓.toProj x)
  let Di := Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) (MvPolynomial.X i)
  -- `σ i ≠ 0`
  have hne := ne_zero_of_frame (𝟙_ Y.X.left.Modules) (𝔓.σ i) (U := 𝔓.toProj ⁻¹ᵁ Di) hi
    (𝔓.frame i _ le_rfl)
  -- `σ i` is a constant, hence a unit of `Γ(Y, ⊤)` (C3 (i): `Γ(Spec K) → Γ(Y)` bijective)
  obtain ⟨c, hc⟩ := (ZInQ.Contrib.CloudR2NOS.Step1.appTop_bijective_of_isAbelianVariety Y).2
    (show Γ(Y.X.left, ⊤) from 𝔓.σ i)
  have hc0 : (Scheme.ΓSpecIso (CommRingCat.of K)).hom c ≠ 0 := by
    intro h0
    apply hne
    have hc' : c = 0 := by
      have := congrArg (Scheme.ΓSpecIso (CommRingCat.of K)).inv h0
      simpa using this
    change (show Γ(Y.X.left, ⊤) from 𝔓.σ i) = 0
    rw [← hc, hc', map_zero]
  have hcu : IsUnit c := by
    have hk : IsUnit ((Scheme.ΓSpecIso (CommRingCat.of K)).hom c) := hc0.isUnit
    have := hk.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
    simpa using this
  have hσu : IsUnit (show Γ(Y.X.left, ⊤) from 𝔓.σ i) := by
    rw [← hc]
    exact hcu.map Y.X.hom.appTop.hom
  -- hence `σ i` generates everywhere, so `toProj` lands in the affine chart `D₊(Xᵢ)`
  have hall : ∀ y : Y.X.left, y ∈ 𝔓.toProj ⁻¹ᵁ Di := by
    intro y
    refine (PresChart.mem_preimage_basicOpen_iff 𝔓 i y).2 ⟨⊤, trivial, fun V _ => ?_⟩
    have hu : IsUnit (Y.X.left.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op
        (show Γ(Y.X.left, ⊤) from 𝔓.σ i)) := hσu.map _
    change Function.Bijective fun g : Γ(Y.X.left, V) =>
      g * Y.X.left.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (show Γ(Y.X.left, ⊤) from 𝔓.σ i)
    refine ⟨fun a b hab => hu.mul_right_cancel hab, fun z => ⟨z * ↑hu.unit⁻¹, ?_⟩⟩
    show z * ↑hu.unit⁻¹ * _ = z
    rw [_root_.mul_assoc, hu.val_inv_mul, _root_.mul_one]
  have htop : 𝔓.toProj ⁻¹ᵁ Di = ⊤ := eq_top_iff.2 fun y _ => hall y
  haveI : IsAffineHom 𝔓.toProj := inferInstance
  have haff : IsAffineOpen (𝔓.toProj ⁻¹ᵁ Di) :=
    (Proj.isAffineOpen_basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K)
      (MvPolynomial.X i)
      (ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.ProjSpace.X_mem_one K N i)
      Nat.one_pos).preimage 𝔓.toProj
  rw [htop] at haff
  haveI : IsAffine (⊤ : Y.X.left.Opens).toScheme := haff
  haveI : IsAffine Y.X.left := IsAffine.of_isIso (Y.X.left.topIso.inv)
  exact IsFinite.iff_isProper_and_isAffineHom.2 ⟨inferInstance, inferInstance⟩

end ZInQ.Contrib.CloudR2NOS.ClosedSection.PresentationBasics
