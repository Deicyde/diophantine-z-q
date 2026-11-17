import ZInQKernel.Contrib.OneProof.GroupLawStalks
import ZInQKernel.OneProof.H.TailZ40

/-!
# group-law: the chain's use of Mumford's group law from *GIT* Thm 6.14 over a discrete valuation ring

Task group-law (2026-11-16); report docs/research/group-law.md. The research field `mumfordGroupLaw` is
`ZInQ.Contrib.MumfordRigidity.MumfordGroupLaw` (*GIT* Thm 6.14 over every locally noetherian `S`). Its only consumer
in `frozenTarget`'s closure is `LeafQM.AV.R1UnivRigid.qmFamilyGroupLaw_of_groupLaw` (`OneProof/H/TailZ40.lean`): the
chain uses the group law only over proper smooth curves `S/ℚ` (`QMFamilyGroupLaw`).

Proved here (no `sorry`, standard axioms):

* `qmFamilyGroupLaw_of_dvr : MumfordGroupLawDVR → QMFamilyGroupLaw` — the chain's use from *GIT* Thm 6.14 over the
  spectrum of a **discrete valuation ring** (`MumfordGroupLawDVR`), through
  `mumfordGroupLawCurve_of_dvr : MumfordGroupLawDVR → MumfordGroupLawCurve` (the group law over every base smooth of
  relative dimension one over a field). At a point `s` the local ring is a field (`grpObj_of_isField`: the group
  law exists outright) or a DVR (the leaf); it spreads to a neighbourhood of `s` and the local laws glue on the
  field points of the reduced overlaps (`GroupLawStalks.grpObj_of_stalkLaws`).
* `mumfordGroupLawRed_of_local : MumfordGroupLawLocal → MumfordGroupLawRed` — the group law over every reduced
  locally noetherian base (with `F`, `F ×_S F`, `(F ×_S F) ×_S F` reduced) from *GIT* Thm 6.14 over the spectra of
  reduced noetherian local rings.
* Comparison: `MumfordGroupLaw → MumfordGroupLawLocal → MumfordGroupLawDVR` (`local_of_field`, `dvr_of_local`), so the
  new leaves are never stronger than the field.

The field itself (non-reduced bases included) is **not** proved: gluing local group laws over a non-reduced base
needs rigidity over the base, and the local case is the deformation-theoretic core of *GIT* Thm 6.14.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.haveILetI false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

namespace ZInQ.Contrib.GroupLaw

open LeafQM.AV.R1UnivRigid PkgI3

/-! ## §1 The leaves -/

/-- **LEAF (Mumford's Thm 6.14 over a discrete valuation ring).** Let `R` be a discrete valuation ring,
`F → Spec R` proper and smooth with geometrically connected fibres, `e` a section, and every field fibre of `F`
an abelian variety with origin `e(s)`. Then `F` carries a group object structure in `Over (Spec R)` with identity
`e` (it is an abelian scheme).

Source (numbers UNVERIFIED, no network): Mumford–Fogarty–Kirwan, *Geometric Invariant Theory*, 3rd ed., Ch. 6 §1,
Thm 6.14 (`S` connected and locally noetherian, `F → S` smooth and proper with a section `e`, one geometric fibre an
abelian variety: `F` is an abelian scheme with identity `e`). *Form*: the print with `S = Spec R` (connected and
noetherian), hypotheses at least as strong (every field fibre an abelian variety, geometrically connected fibres)
and the group-object part of the conclusion: a consequence of the print. Implied by the field `MumfordGroupLaw`
(`dvr_of_field`). -/
def MumfordGroupLawDVR : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (F : Over (Spec (CommRingCat.of R))) (e : Spec (CommRingCat.of R) ⟶ F.left),
    IsProper F.hom → Smooth F.hom → GeometricallyConnected F.hom → e ≫ F.hom = 𝟙 _ →
    (∀ (K : Type) [Field K] (s : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R)),
      ∃ (A : AbVar K) (g : A.X.left ⟶ F.left), IsAbVarFibre F e s A g) →
    ∃ _G : GrpObj F, η[F].left = e

/-- **LEAF (Mumford's Thm 6.14 over a reduced noetherian local base).** As `MumfordGroupLawDVR`, over the spectrum
of any reduced noetherian local ring. Source and form as for `MumfordGroupLawDVR` (`S = Spec R`, `R` local and
noetherian); implied by the field (`local_of_field`). -/
def MumfordGroupLawLocal : Prop :=
  ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [_root_.IsReduced R]
    (F : Over (Spec (CommRingCat.of R))) (e : Spec (CommRingCat.of R) ⟶ F.left),
    IsProper F.hom → Smooth F.hom → GeometricallyConnected F.hom → e ≫ F.hom = 𝟙 _ →
    (∀ (K : Type) [Field K] (s : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R)),
      ∃ (A : AbVar K) (g : A.X.left ⟶ F.left), IsAbVarFibre F e s A g) →
    ∃ _G : GrpObj F, η[F].left = e

/-- The local leaf is an instance of the field. -/
theorem local_of_field (h : ZInQ.Contrib.MumfordRigidity.MumfordGroupLaw) : MumfordGroupLawLocal :=
  fun R _ _ _ _ F e h1 h2 h3 h4 h5 => h _ F e inferInstance h1 h2 h3 h4 h5

/-- The DVR leaf is an instance of the local leaf. -/
theorem dvr_of_local (h : MumfordGroupLawLocal) : MumfordGroupLawDVR :=
  fun R _ _ _ F e h1 h2 h3 h4 h5 => h R F e h1 h2 h3 h4 h5

/-- The DVR leaf is an instance of the field. -/
theorem dvr_of_field (h : ZInQ.Contrib.MumfordRigidity.MumfordGroupLaw) : MumfordGroupLawDVR :=
  dvr_of_local (local_of_field h)

/-! ## §2 The narrowed forms of the field -/

/-- **`MumfordGroupLaw` over a base smooth of relative dimension one over a field** (the field with that
hypothesis added): the form the chain uses (`qmFamilyGroupLaw_of_curve`). -/
def MumfordGroupLawCurve : Prop :=
  ∀ (k : Type) [Field k] (S : Scheme.{0}) (p : S ⟶ Spec (CommRingCat.of k)), SmoothOfRelativeDimension 1 p →
    ∀ (F : Over S) (e : S ⟶ F.left), IsLocallyNoetherian S → IsProper F.hom → Smooth F.hom →
    GeometricallyConnected F.hom → e ≫ F.hom = 𝟙 S →
    (∀ (K : Type) [Field K] (s : Spec (CommRingCat.of K) ⟶ S),
      ∃ (A : AbVar K) (g : A.X.left ⟶ F.left), IsAbVarFibre F e s A g) →
    ∃ _G : GrpObj F, η[F].left = e

/-- **`MumfordGroupLaw` over a reduced base** (the field with four reducedness hypotheses added). -/
def MumfordGroupLawRed : Prop :=
  ∀ (S : Scheme.{0}) (F : Over S) (e : S ⟶ F.left), IsLocallyNoetherian S → IsReduced S →
    IsReduced F.left → IsReduced (F ⊗ F).left → IsReduced ((F ⊗ F) ⊗ F).left →
    IsProper F.hom → Smooth F.hom → GeometricallyConnected F.hom → e ≫ F.hom = 𝟙 S →
    (∀ (K : Type) [Field K] (s : Spec (CommRingCat.of K) ⟶ S),
      ∃ (A : AbVar K) (g : A.X.left ⟶ F.left), IsAbVarFibre F e s A g) →
    ∃ _G : GrpObj F, η[F].left = e

theorem curve_of_field (h : ZInQ.Contrib.MumfordRigidity.MumfordGroupLaw) : MumfordGroupLawCurve :=
  fun _ _ S _ _ F e h0 h1 h2 h3 h4 h5 => h S F e h0 h1 h2 h3 h4 h5

theorem red_of_field (h : ZInQ.Contrib.MumfordRigidity.MumfordGroupLaw) : MumfordGroupLawRed :=
  fun S F e h0 _ _ _ _ h1 h2 h3 h4 h5 => h S F e h0 h1 h2 h3 h4 h5

/-! ## §3 The proofs -/

/-- Smooth over a field: `F`, `F ×_S F`, `(F ×_S F) ×_S F` are reduced. -/
theorem reduced_of_smooth_base {k : Type} [Field k] {S : Scheme.{0}} (p : S ⟶ Spec (CommRingCat.of k))
    [Smooth p] (F : Over S) [Smooth F.hom] :
    IsReduced S ∧ IsReduced F.left ∧ IsReduced (F ⊗ F).left ∧ IsReduced ((F ⊗ F) ⊗ F).left := by
  have h2 : Smooth (F ⊗ F).hom := by rw [Over.tensorObj_hom]; infer_instance
  have h3 : Smooth ((F ⊗ F) ⊗ F).hom := by rw [Over.tensorObj_hom]; infer_instance
  exact ⟨isReduced_of_smooth p, isReduced_of_smooth (F.hom ≫ p), isReduced_of_smooth ((F ⊗ F).hom ≫ p),
    isReduced_of_smooth (((F ⊗ F) ⊗ F).hom ≫ p)⟩

/-- **The group law over a smooth curve from the DVR leaf.** -/
theorem mumfordGroupLawCurve_of_dvr (hD : MumfordGroupLawDVR) : MumfordGroupLawCurve := by
  intro k _ S p hp F e hN hP hSm hGC he hfib
  haveI := hP
  haveI := hSm
  haveI := hGC
  haveI : Smooth p := SmoothOfRelativeDimension.smooth 1 p
  obtain ⟨h0, h1, h2, h3⟩ := reduced_of_smooth_base p F
  refine grpObj_of_stalkLaws F e he hfib (fun V hV 𝔭 _ => ?_)
  obtain ⟨d1, d2, d3, d4⟩ := stalkData hV 𝔭 he hfib
  rcases field_or_dvr_localization p hV 𝔭 with hF | ⟨hDom, hDVR⟩
  · exact grpObj_of_isField _ hF _ _ d4
  · exact hD (Localization.AtPrime 𝔭) _ (eLoc hV 𝔭 he) d1 d2 d3 (eLoc_sec hV 𝔭 he) d4

/-- **The group law over a reduced base from the local leaf.** -/
theorem mumfordGroupLawRed_of_local (hL : MumfordGroupLawLocal) : MumfordGroupLawRed := by
  intro S F e hN hRS hRF hRFF hRFFF hP hSm hGC he hfib
  haveI := hP
  haveI := hSm
  haveI := hGC
  refine grpObj_of_stalkLaws F e he hfib (fun V hV 𝔭 _ => ?_)
  obtain ⟨d1, d2, d3, d4⟩ := stalkData hV 𝔭 he hfib
  haveI : IsNoetherianRing Γ(S, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  haveI : IsNoetherianRing (Localization.AtPrime 𝔭) :=
    IsLocalization.isNoetherianRing 𝔭.primeCompl _ inferInstance
  haveI : _root_.IsReduced (Localization.AtPrime 𝔭) :=
    isReduced_localizationPreserves 𝔭.primeCompl (Localization.AtPrime 𝔭) inferInstance
  exact hL (Localization.AtPrime 𝔭) _ (eLoc hV 𝔭 he) d1 d2 d3 (eLoc_sec hV 𝔭 he) d4

end ZInQ.Contrib.GroupLaw

namespace LeafQM

namespace AV

namespace R1UnivRigid

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI3 ZInQ.Contrib.GroupLaw

/-- rigid-prune's `exists_qmAbScheme_gl` (`OneProof/H/TailZ40.lean`), verbatim, with the group law over the base `S`
as the hypothesis `hG` in place of `MumfordGroupLaw`. -/
theorem exists_qmAbScheme_of {S : Scheme.{0}}
    [IsReduced S] [IsLocallyNoetherian S] (𝒜 : QMFamily S) [IsReduced 𝒜.F.left]
    [IsReduced (𝒜.F ⊗ 𝒜.F).left]
    (hG : ∀ (F : Over S) (e : S ⟶ F.left), IsProper F.hom → Smooth F.hom → GeometricallyConnected F.hom →
      e ≫ F.hom = 𝟙 S → (∀ (K : Type) [Field K] (s : Spec (CommRingCat.of K) ⟶ S),
        ∃ (A : AbVar K) (g : A.X.left ⟶ F.left), IsAbVarFibre F e s A g) → ∃ _G : GrpObj F, η[F].left = e)
    (hfib : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ S), ∃ P : QML3 K,
      IsFibreOf 𝒜 t P) :
    ∃ 𝒜' : QMAbScheme S, 𝒜'.toQMFamily = 𝒜 := by
  have := 𝒜.proper
  have := 𝒜.smooth
  have hsm : Smooth 𝒜.F.hom := SmoothOfRelativeDimension.smooth 2 _
  have hgc := geomConn_of_fibres 𝒜 hfib
  obtain ⟨G, hη⟩ := hG 𝒜.F (𝒜.eta 0) 𝒜.proper hsm hgc (𝒜.eta_sec 0)
    (fun K _ s => by
      obtain ⟨P, g, hpb, -, he⟩ := hfib K s
      exact ⟨P.A, g, hpb, one_left_comp he⟩)
  have hb : ∀ (K : Type) [Field K] (s : Spec (CommRingCat.of K) ⟶ S) (A : AbVar K)
      (g : A.X.left ⟶ 𝒜.F.left), IsAbVarFibre 𝒜.F (𝒜.eta 0) s A g → IsGrpFibre 𝒜.F A g :=
    fun K _ s A g h => isGrpFibre_of_rigidity 𝒜.F s A g (by rw [hη]; exact h)
  -- `η(0)` is fixed by every `ι(a)`
  have hιe : ∀ a : O, 𝒜.eta 0 ≫ 𝒜.iota a = 𝒜.eta 0 := fun a => by
    refine sec_ext 𝒜 hfib _ _ (by rw [Category.assoc, 𝒜.iota_over])
      (fun K _ t P g hpb hι he => ?_)
    have h0 : t ≫ 𝒜.eta 0 = (1 : P.A.Pt K).left ≫ g := (one_left_comp he).symm
    rw [← Category.assoc t, h0]
    erw [Category.assoc, ← hι a, ← Over.comp_left_assoc, MonObj.one_comp]
  have hone : 𝒜.iota 1 = 𝟙 _ := F_ext 𝒜 hfib _ _ (by rw [𝒜.iota_over, Category.id_comp])
    (fun K _ t P g hpb hι he => by
      rw [← hι 1, map_one, Category.comp_id]
      show (𝟙 P.A.X : P.A.X ⟶ P.A.X).left ≫ g = g
      simp)
  have hmul : ∀ a b : O, 𝒜.iota (a * b) = 𝒜.iota b ≫ 𝒜.iota a := fun a b =>
    F_ext 𝒜 hfib _ _ (by rw [𝒜.iota_over, Category.assoc, 𝒜.iota_over, 𝒜.iota_over])
      (fun K _ t P g hpb hι he => by
        rw [← Category.assoc g (𝒜.iota b), ← hι b, Category.assoc, ← hι a, ← hι (a * b), map_mul]
        show ((P.q.iota b).hom ≫ (P.q.iota a).hom).left ≫ g = _
        rw [Over.comp_left, Category.assoc])
  have hadd : ∀ a b : O, (Over.homMk (𝒜.iota (a + b)) (𝒜.iota_over _) : 𝒜.F ⟶ 𝒜.F) =
      Over.homMk (𝒜.iota a) (𝒜.iota_over a) * Over.homMk (𝒜.iota b) (𝒜.iota_over b) :=
    fun a b => by
      apply Over.OverMorphism.ext
      refine F_ext 𝒜 hfib _ _ (by rw [Over.w, Over.w])
        (fun K _ t P g hpb hι he => ?_)
      obtain ⟨φ, hφ₁, hφ₂, hφμ⟩ := hb K t P.A g ⟨hpb, one_left_comp he⟩
      change g ≫ 𝒜.iota (a + b) = _
      rw [← hι (a + b), map_add, AbVar.Hom.hom_add,
        CategoryTheory.Hom.mul_def, CategoryTheory.Hom.mul_def, Over.comp_left, Over.comp_left,
        Category.assoc, hφμ,
        reassoc_of% (lift_comp_φ _ _ (Over.homMk (𝒜.iota a) (𝒜.iota_over a) : 𝒜.F ⟶ 𝒜.F)
          (Over.homMk (𝒜.iota b) (𝒜.iota_over b)) g φ hφ₁ hφ₂ (hι a) (hι b))]
  have headd : ∀ a b : O,
      (Over.homMk (U := 𝟙_ (Over S)) (𝒜.eta (a + b)) (𝒜.eta_sec _) : 𝟙_ (Over S) ⟶ 𝒜.F) =
      Over.homMk (U := 𝟙_ (Over S)) (𝒜.eta a) (𝒜.eta_sec a) *
        Over.homMk (U := 𝟙_ (Over S)) (𝒜.eta b) (𝒜.eta_sec b) := fun a b => by
    apply Over.OverMorphism.ext
    refine sec_ext 𝒜 hfib _ _ (by rw [Over.w, Over.w])
      (fun K _ t P g hpb hι he => ?_)
    obtain ⟨φ, hφ₁, hφ₂, hφμ⟩ := hb K t P.A g ⟨hpb, one_left_comp he⟩
    change t ≫ 𝒜.eta (a + b) = _
    rw [← he (a + b), map_add, toMul_add,
      CategoryTheory.Hom.mul_def, CategoryTheory.Hom.mul_def, Over.comp_left, Over.comp_left,
      Category.assoc, hφμ,
      reassoc_of% (lift_comp_φ _ _ (Over.homMk (U := 𝟙_ (Over S)) (𝒜.eta a) (𝒜.eta_sec a))
        (Over.homMk (U := 𝟙_ (Over S)) (𝒜.eta b) (𝒜.eta_sec b)) t φ hφ₁ hφ₂ (he a) (he b))]
    rfl
  have helin : ∀ a b : O, 𝒜.eta (a * b) = 𝒜.eta b ≫ 𝒜.iota a := fun a b => by
    refine sec_ext 𝒜 hfib _ _
      (by rw [𝒜.eta_sec, Category.assoc, 𝒜.iota_over, 𝒜.eta_sec])
      (fun K _ t P g hpb hι he => ?_)
    have hl : Additive.toMul (P.e.eta (a * b)) =
        Additive.toMul (P.e.eta b) ≫ (P.q.iota a).hom := by
      rw [P.e.linear]; rfl
    rw [← he (a * b), hl, Over.comp_left, Category.assoc, hι a, reassoc_of% (he b)]
    rfl
  have hthree : ∀ b : O, 𝒜.eta (3 * b) = 𝒜.eta 0 := fun b =>
    sec_ext 𝒜 hfib _ _ (by rw [𝒜.eta_sec, 𝒜.eta_sec]) (fun K _ t P g hpb hι he => by
      rw [← he (3 * b), ← he 0, (P.e.eq_iff (3 * b) 0).2 ⟨b, by simp⟩])
  have hker : ∀ (K : Type) [Field K] (s : Spec (CommRingCat.of K) ⟶ S) (a : O),
      s ≫ 𝒜.eta a = s ≫ 𝒜.eta 0 ↔ ∃ b : O, a = 3 * b := by
    intro K _ s a
    obtain ⟨P, g, hpb, hι, he⟩ := hfib K s
    rw [← he a, ← he 0]
    constructor
    · intro h
      have h' : Additive.toMul (P.e.eta a) = Additive.toMul (P.e.eta 0) := by
        apply Over.OverMorphism.ext
        apply hpb.hom_ext h
        rw [Over.w, Over.w]
      obtain ⟨c, hc⟩ := (P.e.eq_iff a 0).1 (Additive.toMul.injective h')
      exact ⟨c, by simpa using hc⟩
    · rintro ⟨b, rfl⟩
      rw [(P.e.eq_iff (3 * b) 0).2 ⟨b, by simp⟩]
  refine ⟨{ 𝒜 with
    grp := G
    geomConn := hgc
    one_eq := hη
    iota_hom := fun a => isMonHom_of_fibres 𝒜 hη hfib a (hιe a)
    iota_one := hone
    iota_mul := hmul
    iota_add := hadd
    eta_add := headd
    eta_linear := helin
    eta_three := hthree
    eta_ker := hker }, rfl⟩

/-- **`QMFamilyGroupLaw` from the curve form** (rigid-prune's `qmFamilyGroupLaw_of_groupLaw`, verbatim, with the
curve form applied to `S → Spec ℚ`). -/
theorem qmFamilyGroupLaw_of_curve (hG : MumfordGroupLawCurve) : QMFamilyGroupLaw := by
  intro S _ hs 𝒜 hfib
  obtain ⟨h1, h2, h3⟩ := reduced_of_smooth_curve hs 𝒜
  have : Smooth S.hom := SmoothOfRelativeDimension.smooth 1 _
  have := 𝒜.smooth
  have : Smooth 𝒜.F.hom := SmoothOfRelativeDimension.smooth 2 _
  have : Smooth (𝒜.F ⊗ 𝒜.F).hom := by
    rw [Over.tensorObj_hom]
    infer_instance
  have : IsReduced (𝒜.F ⊗ 𝒜.F).left := isReduced_of_smooth ((𝒜.F ⊗ 𝒜.F).hom ≫ S.hom)
  exact exists_qmAbScheme_of 𝒜 (fun F e h1 h2 h3 h4 h5 => hG ℚ S.left S.hom hs F e inferInstance h1 h2 h3 h4 h5)
    (fun K _ t => fibre_of_fieldPt 𝒜 hfib t)

/-- **The chain's only use of the field `mumfordGroupLaw`, from *GIT* Thm 6.14 over a DVR.** -/
theorem qmFamilyGroupLaw_of_dvr (hD : MumfordGroupLawDVR) : QMFamilyGroupLaw :=
  qmFamilyGroupLaw_of_curve (mumfordGroupLawCurve_of_dvr hD)

/-- The same from the local leaf. -/
theorem qmFamilyGroupLaw_of_local (hL : MumfordGroupLawLocal) : QMFamilyGroupLaw :=
  qmFamilyGroupLaw_of_dvr (dvr_of_local hL)

end R1UnivRigid

end AV

end LeafQM
