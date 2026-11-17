import ZInQKernel.Contrib.OneProof.Y3RepresentableQ

/-! # y3-audit: `Y3RepresentableQ` from the integral model at one prime (generic fibre)

Task y3-audit (2026-11-17). Report: `docs/research/y3-audit.md` §4.3.

sgr-split's leaf `SGRSplit.ShimuraIntegralModelRep` (printed form, pending reading; Kottwitz 1992 §5, whose
prime-to-`p` level `K₃` covers the level at `3 ∣ 6`) asserts at every `p > 324` that the level-3 moduli problem on
locally noetherian `ℤ_(p)`-schemes is representable by a proper smooth curve `𝒴/ℤ_(p)`. Its generic fibre represents
the problem on locally noetherian `ℚ`-schemes. This file proves that in Lean:

* `abBC 𝒜 j`: the base change of a `QMAbScheme` along any `j : T ⟶ S` (Mathlib's `Over.pullback`, monoidal, with
  the group law `Functor.grpObjObj`);
* `qmFamFibre_abBC_iff`: `𝒜'` is a pullback of `j^*𝒜` along `g` iff it is a pullback of `𝒜` along `g ≫ j`;
* `y3RepresentableQ_of_integralAt : ShimuraIntegralModelRepAt p → Y3RepresentableQ`, and
  `y3RepresentableQ_of_integral : ShimuraIntegralModelRep → Y3RepresentableQ` (at `p = 331`).

So the new statement `Y3RepresentableQ` is never stronger than the existing integral-model leaf. -/

set_option linter.all false

noncomputable section

namespace Y3Audit

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open LeafQM LeafQM.AV LeafQM.AV.R1UnivRigid
open Y3Fix SGRSplit HDec.VertWitness HDec.ModelGlue
open scoped CategoryTheory.Obj

/-! ## Generic pullback lemmas (all objects abstract, to avoid defeq-only object mismatches) -/

theorem map_left_fst' {S T : Scheme.{0}} (j : T ⟶ S) {X Z : Over S} (u : X ⟶ Z) :
    ((Over.pullback j).map u).left ≫ pullback.fst Z.hom j = pullback.fst X.hom j ≫ u.left := by
  simp [Over.pullback_map_left]

theorem lift_compat_iota {A P X Y Z : Scheme.{0}} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {j : Y ⟶ Z}
    (hP : IsPullback fst snd f j) (k : A ⟶ P) (i' : A ⟶ A) (iP : P ⟶ P) (iX : X ⟶ X) (h₀ : A ⟶ X)
    (sA : A ⟶ Y) (hk1 : k ≫ fst = h₀) (hk2 : k ≫ snd = sA) (hι : i' ≫ h₀ = h₀ ≫ iX)
    (hiP : iP ≫ fst = fst ≫ iX) (hi's : i' ≫ sA = sA) (hiPs : iP ≫ snd = snd) : i' ≫ k = k ≫ iP := by
  apply hP.hom_ext
  · rw [Category.assoc, hk1, hι, Category.assoc, hiP, ← Category.assoc, hk1]
  · rw [Category.assoc, hk2, hi's, Category.assoc, hiPs, hk2]

theorem lift_compat_eta {A P X Y Z U : Scheme.{0}} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {j : Y ⟶ Z}
    (hP : IsPullback fst snd f j) (k : A ⟶ P) (e' : U ⟶ A) (g : U ⟶ Y) (eP : Y ⟶ P) (eX : Z ⟶ X)
    (h₀ : A ⟶ X) (sA : A ⟶ U) (hk1 : k ≫ fst = h₀) (hk2 : k ≫ snd = sA ≫ g) (hη : e' ≫ h₀ = (g ≫ j) ≫ eX)
    (heP : eP ≫ fst = j ≫ eX) (he's : e' ≫ sA = 𝟙 U) (hePs : eP ≫ snd = 𝟙 Y) : e' ≫ k = g ≫ eP := by
  apply hP.hom_ext
  · rw [Category.assoc, hk1, hη, Category.assoc, Category.assoc, heP]
  · rw [Category.assoc, hk2, ← Category.assoc, he's, Category.id_comp, Category.assoc, hePs,
      Category.comp_id]

theorem sec_eq_iff {P X Y Z W : Scheme.{0}} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {j : Y ⟶ Z}
    (hP : IsPullback fst snd f j) (s : W ⟶ Y) (ea eb : Y ⟶ P) (xa xb : Z ⟶ X)
    (ha : ea ≫ fst = j ≫ xa) (hb : eb ≫ fst = j ≫ xb) (hsa : ea ≫ snd = 𝟙 Y) (hsb : eb ≫ snd = 𝟙 Y) :
    s ≫ ea = s ≫ eb ↔ (s ≫ j) ≫ xa = (s ≫ j) ≫ xb := by
  constructor
  · intro h
    have := congrArg (· ≫ fst) h
    simp only [Category.assoc] at this
    rw [ha, hb] at this
    simpa only [Category.assoc] using this
  · intro h
    apply hP.hom_ext
    · rw [Category.assoc, Category.assoc, ha, hb, ← Category.assoc, ← Category.assoc, h]
    · rw [Category.assoc, Category.assoc, hsa, hsb]

section BC

variable {S T : Scheme.{0}} (𝒜 : QMAbScheme S) (j : T ⟶ S)

/-- The unit section of the pulled-back unit. -/
abbrev epsBC : 𝟙_ (Over T) ⟶ (Over.pullback j).obj (𝟙_ (Over S)) :=
  Functor.LaxMonoidal.ε (Over.pullback j)

theorem epsBC_fst : (epsBC j).left ≫ pullback.fst (𝟙_ (Over S)).hom j = j := by
  have h1 : (epsBC j).left ≫ pullback.snd (𝟙_ (Over S)).hom j = 𝟙 T := Over.w (epsBC j)
  have h2 : pullback.fst (𝟙_ (Over S)).hom j = pullback.snd (𝟙_ (Over S)).hom j ≫ j := by
    have := pullback.condition (f := (𝟙_ (Over S)).hom) (g := j)
    exact (Category.comp_id _).symm.trans this
  rw [h2, ← Category.assoc, h1, Category.id_comp]

theorem fa_one : fa 𝒜 1 = 𝟙 _ := Over.OverMorphism.ext 𝒜.iota_one

theorem fa_mul (a b : O) : fa 𝒜 (a * b) = fa 𝒜 b ≫ fa 𝒜 a := Over.OverMorphism.ext (𝒜.iota_mul a b)

theorem sec_mul (a b : O) : sec 𝒜 (a * b) = sec 𝒜 b ≫ fa 𝒜 a :=
  Over.OverMorphism.ext (𝒜.eta_linear a b)

theorem sec_three (b : O) : sec 𝒜 (3 * b) = sec 𝒜 0 := Over.OverMorphism.ext (𝒜.eta_three b)

/-- The section `η'(a) = ε ≫ j^*η(a)` of the base change. -/
abbrev secBC (a : O) : 𝟙_ (Over T) ⟶ (Over.pullback j).obj 𝒜.F :=
  epsBC j ≫ (Over.pullback j).map (sec 𝒜 a)

theorem secBC_fst (a : O) :
    (secBC 𝒜 j a).left ≫ pullback.fst 𝒜.F.hom j = j ≫ 𝒜.eta a := by
  change (epsBC j).left ≫ ((Over.pullback j).map (sec 𝒜 a)).left ≫ pullback.fst 𝒜.F.hom j = _
  rw [map_left_fst', ← Category.assoc, epsBC_fst]
  rfl

theorem secBC_snd (a : O) : (secBC 𝒜 j a).left ≫ pullback.snd 𝒜.F.hom j = 𝟙 T :=
  Over.w (secBC 𝒜 j a)

theorem iotaBC_fst (a : O) :
    ((Over.pullback j).map (fa 𝒜 a)).left ≫ pullback.fst 𝒜.F.hom j =
      pullback.fst 𝒜.F.hom j ≫ 𝒜.iota a :=
  map_left_fst' j (fa 𝒜 a)

/-- **The base change of a `QMAbScheme`** along `j : T ⟶ S`. -/
def abBC : QMAbScheme T :=
  letI := 𝒜.grp
  have := 𝒜.proper
  have := 𝒜.smooth
  have := 𝒜.geomConn
  { F := (Over.pullback j).obj 𝒜.F
    proper := by dsimp; infer_instance
    smooth := by dsimp; infer_instance
    iota := fun a => ((Over.pullback j).map (fa 𝒜 a)).left
    iota_over := fun a => Over.w ((Over.pullback j).map (fa 𝒜 a))
    eta := fun a => (secBC 𝒜 j a).left
    eta_sec := fun a => Over.w (secBC 𝒜 j a)
    grp := inferInstance
    geomConn := by dsimp; infer_instance
    one_eq := by
      have hsec0 : sec 𝒜 0 = η[𝒜.F] := by
        apply Over.OverMorphism.ext
        change 𝒜.eta 0 = (η[𝒜.F]).left
        rw [𝒜.one_eq]
      rw [hsec0]
      rfl
    iota_hom := fun a => by
      have : IsMonHom (fa 𝒜 a) := 𝒜.iota_hom a
      have e : (Over.homMk ((Over.pullback j).map (fa 𝒜 a)).left (Over.w _) :
          (Over.pullback j).obj 𝒜.F ⟶ (Over.pullback j).obj 𝒜.F) = (Over.pullback j).map (fa 𝒜 a) :=
        Over.OverMorphism.ext rfl
      rw [e]
      infer_instance
    iota_one := by
      change ((Over.pullback j).map (fa 𝒜 1)).left = _
      rw [fa_one, CategoryTheory.Functor.map_id]
      rfl
    iota_mul := fun a b => by
      change ((Over.pullback j).map (fa 𝒜 (a * b))).left = _
      rw [fa_mul, CategoryTheory.Functor.map_comp]
      rfl
    iota_add := fun a b => by
      have e : ∀ c : O, (Over.homMk ((Over.pullback j).map (fa 𝒜 c)).left (Over.w _) :
          (Over.pullback j).obj 𝒜.F ⟶ (Over.pullback j).obj 𝒜.F) = (Over.pullback j).map (fa 𝒜 c) :=
        fun c => Over.OverMorphism.ext rfl
      rw [e, e, e]
      have h : fa 𝒜 (a + b) = fa 𝒜 a * fa 𝒜 b := 𝒜.iota_add a b
      rw [h, CategoryTheory.Functor.map_mul]
    eta_add := fun a b => by
      have e : ∀ c : O, (Over.homMk (U := 𝟙_ (Over T)) (secBC 𝒜 j c).left (Over.w _) :
          𝟙_ (Over T) ⟶ (Over.pullback j).obj 𝒜.F) = secBC 𝒜 j c :=
        fun c => Over.OverMorphism.ext rfl
      rw [e, e, e]
      have h : sec 𝒜 (a + b) = sec 𝒜 a * sec 𝒜 b := 𝒜.eta_add a b
      simp only [secBC]
      rw [h, CategoryTheory.Functor.map_mul, MonObj.comp_mul]
    eta_linear := fun a b => by
      change (epsBC j ≫ (Over.pullback j).map (sec 𝒜 (a * b))).left = _
      rw [sec_mul, CategoryTheory.Functor.map_comp, ← Category.assoc]
      rfl
    eta_three := fun b => by
      change (epsBC j ≫ (Over.pullback j).map (sec 𝒜 (3 * b))).left = _
      rw [sec_three]
    eta_ker := fun K _ s a => by
      rw [← 𝒜.eta_ker K (s ≫ j) a]
      exact sec_eq_iff (IsPullback.of_hasPullback 𝒜.F.hom j) s _ _ (𝒜.eta a) (𝒜.eta 0)
        (secBC_fst 𝒜 j a) (secBC_fst 𝒜 j 0) (secBC_snd 𝒜 j a) (secBC_snd 𝒜 j 0) }

theorem abBC_F : (abBC 𝒜 j).F = (Over.pullback j).obj 𝒜.F := rfl

theorem abBC_eta_fst (a : O) : (abBC 𝒜 j).eta a ≫ pullback.fst 𝒜.F.hom j = j ≫ 𝒜.eta a :=
  secBC_fst 𝒜 j a

theorem abBC_iota_fst (a : O) :
    (abBC 𝒜 j).iota a ≫ pullback.fst 𝒜.F.hom j = pullback.fst 𝒜.F.hom j ≫ 𝒜.iota a :=
  iotaBC_fst 𝒜 j a

/-- The pullback square of the base change, with its `ι` and `η`. -/
theorem qmFamFibre_abBC : QMFamFibre 𝒜.toQMFamily j (abBC 𝒜 j).toQMFamily :=
  ⟨pullback.fst 𝒜.F.hom j, IsPullback.of_hasPullback _ _, fun a => abBC_iota_fst 𝒜 j a,
    fun a => abBC_eta_fst 𝒜 j a⟩

/-- Pasting of `QMFamFibre`. -/
theorem qmFamFibre_trans {U : Scheme.{0}} {𝒜₁ : QMFamily S} {𝒜₂ : QMFamily T} {𝒜₃ : QMFamily U}
    {j : T ⟶ S} {g : U ⟶ T} (h₂ : QMFamFibre 𝒜₁ j 𝒜₂) (h₃ : QMFamFibre 𝒜₂ g 𝒜₃) :
    QMFamFibre 𝒜₁ (g ≫ j) 𝒜₃ := by
  obtain ⟨h, hpb, hi, he⟩ := h₂
  obtain ⟨k, hkpb, hki, hke⟩ := h₃
  refine ⟨k ≫ h, hkpb.paste_horiz hpb, fun a => ?_, fun a => ?_⟩
  · exact paste_iota _ _ _ _ _ (hki a) (hi a)
  · exact paste_eta _ _ _ _ _ _ _ (hke a) (he a)

/-- Conversely, a pullback of `𝒜` along `g ≫ j` is a pullback of `j^*𝒜` along `g`. -/
theorem qmFamFibre_abBC_of {U : Scheme.{0}} {𝒜' : QMFamily U} {g : U ⟶ T}
    (h : QMFamFibre 𝒜.toQMFamily (g ≫ j) 𝒜') : QMFamFibre (abBC 𝒜 j).toQMFamily g 𝒜' := by
  obtain ⟨h₀, hpb, hι, hη⟩ := h
  have w : h₀ ≫ 𝒜.F.hom = (𝒜'.F.hom ≫ g) ≫ j := by rw [hpb.w, Category.assoc]
  let k : 𝒜'.F.left ⟶ (pullback 𝒜.F.hom j) := pullback.lift h₀ (𝒜'.F.hom ≫ g) w
  have hk1 : k ≫ pullback.fst 𝒜.F.hom j = h₀ := pullback.lift_fst _ _ _
  have hk2 : k ≫ pullback.snd 𝒜.F.hom j = 𝒜'.F.hom ≫ g := pullback.lift_snd _ _ _
  refine ⟨k, ?_, fun a => ?_, fun a => ?_⟩
  · have hR : IsPullback (pullback.fst 𝒜.F.hom j) (pullback.snd 𝒜.F.hom j) 𝒜.F.hom j :=
      IsPullback.of_hasPullback _ _
    have hs : IsPullback (k ≫ pullback.fst 𝒜.F.hom j) 𝒜'.F.hom 𝒜.F.hom (g ≫ j) := by
      rw [hk1]; exact hpb
    exact IsPullback.of_right hs hk2 hR
  · exact lift_compat_iota (IsPullback.of_hasPullback 𝒜.F.hom j) k (𝒜'.iota a) ((abBC 𝒜 j).iota a)
      (𝒜.iota a) h₀ (𝒜'.F.hom ≫ g) hk1 hk2 (hι a) (abBC_iota_fst 𝒜 j a)
      (by rw [← Category.assoc, 𝒜'.iota_over]) ((abBC 𝒜 j).iota_over a)
  · exact lift_compat_eta (IsPullback.of_hasPullback 𝒜.F.hom j) k (𝒜'.eta a) g ((abBC 𝒜 j).eta a)
      (𝒜.eta a) h₀ 𝒜'.F.hom hk1 hk2 (hη a) (abBC_eta_fst 𝒜 j a) (𝒜'.eta_sec a) ((abBC 𝒜 j).eta_sec a)

end BC

/-! ## The generic fibre represents the problem on `ℚ`-schemes -/

/-- **`Y3RepresentableQ` from the integral model at one prime `p`** (given `TorsionStructure`, to pass to the
printed level form over `ℚ`). -/
theorem y3RepresentableQ_of_integralAt (hT : ObjBridge.TorsionStructure) (p : ℕ) [Fact p.Prime]
    (h : ShimuraIntegralModelRepAt p) : Y3RepresentableQ := by
  obtain ⟨𝒴, 𝒜, hp, hs, hU⟩ := h
  let j := pullback.fst 𝒴.hom (specRatToZloc p)
  let Y : Over (Spec (CommRingCat.of ℚ)) := genFib 𝒴
  let 𝒜Q : QMAbSchemeP Y.left := ofKer hT (S := Y) (abBC 𝒜 j)
  refine ⟨Y, 𝒜Q, genFib_isProper 𝒴 hp, genFib_smooth 𝒴 hs, fun S hN 𝒜' => ?_⟩
  -- `S` as a `ℤ_(p)`-scheme
  let Sp : Over (Spec (CommRingCat.of (Zloc p))) := Over.mk (S.hom ≫ specRatToZloc p)
  have hNp : IsLocallyNoetherian Sp.left := hN
  obtain ⟨g', hg', hgu⟩ := hU Sp hNp (toKer 𝒜')
  have w : g'.left ≫ 𝒴.hom = S.hom ≫ specRatToZloc p := Over.w g'
  let g : S ⟶ Y := Over.homMk (pullback.lift g'.left S.hom w) (pullback.lift_snd _ _ _)
  have hgj : g.left ≫ j = g'.left := pullback.lift_fst _ _ _
  refine ⟨g, ?_, fun g₂ hg₂ => ?_⟩
  · change QMFamFibre (abBC 𝒜 j).toQMFamily g.left 𝒜'.toQMFamily
    apply qmFamFibre_abBC_of
    rw [hgj]
    exact hg'
  · -- uniqueness: `g₂ ≫ j` is a pullback map over `ℤ_(p)`
    have h₂ : QMFamFibre 𝒜.toQMFamily (g₂.left ≫ j) 𝒜'.toQMFamily :=
      qmFamFibre_trans (qmFamFibre_abBC 𝒜 j) hg₂
    have w₂ : (g₂.left ≫ j) ≫ 𝒴.hom = Sp.hom := by
      change (g₂.left ≫ j) ≫ 𝒴.hom = S.hom ≫ specRatToZloc p
      rw [Category.assoc, pullback.condition, ← Category.assoc]
      have : g₂.left ≫ pullback.snd 𝒴.hom (specRatToZloc p) = S.hom := Over.w g₂
      rw [this]
    have e := hgu (Over.homMk (g₂.left ≫ j) w₂) h₂
    have e' : g₂.left ≫ j = g'.left := congrArg CommaMorphism.left e
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · rw [e', ← hgj]
    · exact (Over.w g₂).trans (Over.w g).symm

/-- **`Y3RepresentableQ` from sgr-split's integral-model leaf** (at `p = 331 > 324`; `TorsionStructure` from the
proved `mumfordTorsionAlgClosed`). -/
theorem y3RepresentableQ_of_integral (h : ShimuraIntegralModelRep) : Y3RepresentableQ := by
  haveI : Fact (Nat.Prime 331) := ⟨by norm_num⟩
  exact y3RepresentableQ_of_integralAt
    (AvSplit.torsionStructure_of_mumford ZInQ.Contrib.CloudB3W16Torsion.mumfordTorsionAlgClosed_proof) 331
    (h 331 (by norm_num))

end Y3Audit
