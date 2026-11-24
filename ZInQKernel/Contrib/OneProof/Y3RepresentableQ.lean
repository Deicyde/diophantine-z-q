import ZInQKernel.Contrib.OneProof.ShimuraY3PrintedLeaves
import ZInQKernel.Contrib.OneProof.MumfordTorsionAlgClosed

/-! # y3-audit: the fine-moduli leaf of `Y₃` from representability over `ℚ`

Task y3-audit (2026-11-17). Report: `docs/research/y3-audit.md`; log: `scratch/y3-audit/log.md`.

y3-fix's leaf `Y3Fix.Y3FineModuliAbP` is a clause list on field points and on proper smooth curves over `ℚ`
(`R1fpPropsAbP`). The printed theorems it rests on state **representability** of the moduli functor. This file
states that functor and its representability over `ℚ` in the kernel's own objects. The statement is
`Y3RepresentableQ`: on locally noetherian `ℚ`-schemes `S` (universe 0), every `QMAbSchemeP S` is, with its
`𝒪`-action and level sections, the pullback of one universal `QMAbSchemeP` over a proper smooth curve `Y/ℚ` along
exactly one `ℚ`-morphism `S → Y`. It is the `ℚ`-analogue of the existing `SGRSplit.ShimuraIntegralModelRepAt`
(over `ℤ_(p)`).

The file then proves that clause list from `Y3RepresentableQ` and the textbook field `mumfordTorsionAlgClosed`
(through `TorsionStructure`): Yoneda at `Spec K` and at proper smooth curves, using sgr-split's glue
(`qmAbFieldFibre`, `qml3AsQMAb_of`, `fibreClassUnique`).

* `y3FineModuliAbP_of_rep : TorsionStructure → Y3RepresentableQ → Y3Fix.Y3FineModuliAbP`;
* `shimuraMainThmIDeligneY3AbU_of_rep : MumfordTorsionAlgClosed → Y3RepresentableQ →
  Y3Fix.DeligneCanonicalModelY3EveryH → ShimuraMainThmIDeligneY3AbU` (the discharge of the research field).

No `sorry`.
-/

set_option linter.all false

noncomputable section

namespace Y3Audit

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV LeafQM.AV.R1UnivRigid
open ShimuraCFT RayClassCFT
open Y3Fix SGRSplit

/-- **LEAF candidate `Y3RepresentableQ`: the moduli functor of abelian surfaces with QM by `𝒪` and full
`𝒪`-linear level-3 structure is representable over `ℚ` by a proper smooth curve.**

There are a `ℚ`-scheme `Y`, proper and smooth of relative dimension 1, and a universal object
`𝒜 : QMAbSchemeP Y` with the following property. Let `S` be a locally noetherian `ℚ`-scheme in universe 0 and
`𝒜'` any object over `S`, i.e. a `QMAbSchemeP S`:
* `A/S` is an abelian scheme of relative dimension 2;
* `ι : 𝒪 → End_S(A)` is a ring map, for the maximal order `𝒪` of `B = (2, −3 | ℚ)`;
* `η` is an `𝒪`-linear level-3 structure in Mumford's form (`LevelPrint`): at every geometric point, `η(a)`,
  `a ∈ 𝒪/3𝒪`, are exactly the points of `A_s[3]`.

Then `𝒜'` is the pullback of `𝒜`, together with `ι` and `η`, along exactly one `ℚ`-morphism `S → Y`
(`QMFamFibre`). No polarization is part of the datum.

*Status.* True by a STANDARD argument, but **no verified print states it at this level**:
* Buzzard (Duke 1997) needs the level to be prime to the discriminant, and `3 ∣ 6`.
* The two routes are written out in `docs/research/y3-audit.md` §4:
  * Buzzard at an auxiliary level, plus rigidity at level 3, a free quotient and descent;
  * Kottwitz (JAMS 1992) §5 at an auxiliary prime `p ∤ 6`, where `K₃` is a neat prime-to-`p` level, together with
    the PEL comparison. Unread; locators UNVERIFIED.

*Form.* It is the published shape, representability, over `ℚ` rather than `ℤ[1/6]` and restricted to locally
noetherian bases. -/
def Y3RepresentableQ : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (𝒜 : QMAbSchemeP Y.left),
    IsProper Y.hom ∧ SmoothOfRelativeDimension 1 Y.hom ∧
    ∀ (S : Over (Spec (CommRingCat.of ℚ))), IsLocallyNoetherian S.left →
      ∀ 𝒜' : QMAbSchemeP S.left, ∃! g : S ⟶ Y, QMFamFibre 𝒜.toQMFamily g.left 𝒜'.toQMFamily

/-! ## Lemmas -/

instance isLocallyNoetherian_fieldPt (K : Type) [Field K] [Algebra ℚ K] :
    IsLocallyNoetherian (fieldPt K).left := by
  dsimp [fieldPt]; infer_instance

theorem isLocallyNoetherian_of_smooth_Q (S : Over (Spec (CommRingCat.of ℚ)))
    (hsm : SmoothOfRelativeDimension 1 S.hom) : IsLocallyNoetherian S.left := by
  have : Smooth S.hom := SmoothOfRelativeDimension.smooth 1 _
  exact LocallyOfFiniteType.isLocallyNoetherian S.hom

/-- A field object as a printed-form `QMAbSchemeP` over `Spec K` with the same fibres. -/
theorem exists_schemeP (hT : ObjBridge.TorsionStructure) (K : Type) [Field K] [Algebra ℚ K] (P : QML3 K) :
    ∃ 𝒜' : QMAbSchemeP (fieldPt K).left,
      ∀ (T : Scheme.{0}) (𝒜 : QMFamily T) (y : Spec (CommRingCat.of K) ⟶ T),
        IsFibreOf 𝒜 y P ↔ QMFamFibre 𝒜 y 𝒜'.toQMFamily := by
  obtain ⟨𝒜'', h⟩ := qml3AsQMAb_of abVarSurfaceRelDim K P
  exact ⟨ofKer hT (S := fieldPt K) 𝒜'', h⟩

/-- Pasting: a fibre of `𝒜'` at `s`, with `𝒜'` the pullback of `𝒜` along `g`, is a fibre of `𝒜` at `s ≫ g`. -/
theorem isFibreOf_comp {S T : Scheme.{0}} {𝒜 : QMFamily T} {𝒜' : QMFamily S} {g : S ⟶ T}
    (hg : QMFamFibre 𝒜 g 𝒜') {K : Type} [Field K] {s : Spec (CommRingCat.of K) ⟶ S} {P : QML3 K}
    (hP : IsFibreOf 𝒜' s P) : IsFibreOf 𝒜 (s ≫ g) P := by
  obtain ⟨h, hpb, hi, he⟩ := hg
  obtain ⟨k, hkpb, hki, hke⟩ := hP
  refine ⟨k ≫ h, hkpb.paste_horiz hpb, fun a => ?_, fun a => ?_⟩
  · exact paste_iota _ _ _ _ _ (hki a) (hi a)
  · exact paste_eta _ _ _ _ _ _ _ (hke a) (he a)

/-- The identity of a field point composed with `Spec(K → K)`. -/
theorem spec_id_comp {K : Type} [Field K] {X : Scheme.{0}} (y : Spec (CommRingCat.of K) ⟶ X)
    (f : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of K))
    (hf : f = Spec.map (CommRingCat.ofHom (algebraMap K K))) : f ≫ y = y := by
  subst hf
  rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]

/-- The level-section square of a base change, with all objects abstract. -/
theorem eta_bc {SL SK AQ AP T F : Scheme.{0}} (φ : SL ⟶ SK) (y : SK ⟶ T) (g : AQ ⟶ AP) (gP : AP ⟶ F)
    (gQ : AQ ⟶ F) (pP : AP ⟶ SK) (pQ : AQ ⟶ SL) (Fh : F ⟶ T) (e : T ⟶ F)
    (hpb : IsPullback gP pP Fh y) (hg1 : g ≫ gP = gQ) (hg2 : g ≫ pP = pQ ≫ φ) (ηQ : SL ⟶ AQ)
    (ηP : SK ⟶ AP) (hQ : ηQ ≫ gQ = (φ ≫ y) ≫ e) (hP : ηP ≫ gP = y ≫ e) (hQ1 : ηQ ≫ pQ = 𝟙 SL)
    (hP1 : ηP ≫ pP = 𝟙 SK) : ηQ ≫ g = φ ≫ ηP := by
  apply hpb.hom_ext
  · rw [Category.assoc, hg1, hQ, Category.assoc, Category.assoc, hP]
  · rw [Category.assoc, hg2, ← Category.assoc, hQ1, Category.id_comp, Category.assoc, hP1,
      Category.comp_id]

/-- **Naturality from a family**: fibres at `y` and at `Spec(f) ≫ y` are base changes along `f`. -/
theorem isBaseChangeOf_of_fibres {T : Scheme.{0}} (𝒜 : QMFamily T) {K L : Type} [Field K] [Field L]
    (f : K →+* L) (y : Spec (CommRingCat.of K) ⟶ T) (P : QML3 K) (Q : QML3 L)
    (hP : IsFibreOf 𝒜 y P) (hQ : IsFibreOf 𝒜 (Spec.map (CommRingCat.ofHom f) ≫ y) Q) :
    IsBaseChangeOf f P Q := by
  obtain ⟨gP, hpbP, hιP, hηP⟩ := hP
  obtain ⟨gQ, hpbQ, hιQ, hηQ⟩ := hQ
  have w : gQ ≫ 𝒜.F.hom = (Q.A.X.hom ≫ Spec.map (CommRingCat.ofHom f)) ≫ y := by
    rw [hpbQ.w, Category.assoc]
  let g : Q.A.X.left ⟶ P.A.X.left := hpbP.lift gQ (Q.A.X.hom ≫ Spec.map (CommRingCat.ofHom f)) w
  have hg1 : g ≫ gP = gQ := hpbP.lift_fst _ _ _
  have hg2 : g ≫ P.A.X.hom = Q.A.X.hom ≫ Spec.map (CommRingCat.ofHom f) := hpbP.lift_snd _ _ _
  refine ⟨g, ?_, fun a => ?_, fun a => ?_⟩
  · have hs : IsPullback (g ≫ gP) Q.A.X.hom 𝒜.F.hom (Spec.map (CommRingCat.ofHom f) ≫ y) := by
      rw [hg1]; exact hpbQ
    exact IsPullback.of_right hs hg2 hpbP
  · apply hpbP.hom_ext
    · simp only [Category.assoc]
      rw [hg1, hιQ a, hιP a, ← Category.assoc, hg1]
    · simp only [Category.assoc]
      rw [hg2, Over.w (P.q.iota a).hom, hg2, ← Category.assoc, Over.w (Q.q.iota a).hom]
  · have hQ1 : (Additive.toMul (Q.e.eta a)).left ≫ Q.A.X.hom = 𝟙 _ := by
      rw [Over.w (Additive.toMul (Q.e.eta a))]; exact ptObj_hom_self L
    have hP1 : (Additive.toMul (P.e.eta a)).left ≫ P.A.X.hom = 𝟙 _ := by
      rw [Over.w (Additive.toMul (P.e.eta a))]; exact ptObj_hom_self K
    exact eta_bc (Spec.map (CommRingCat.ofHom f)) y g gP gQ P.A.X.hom Q.A.X.hom 𝒜.F.hom (𝒜.eta a) hpbP
      hg1 hg2 _ _ (hηQ a) (hηP a) hQ1 hP1

/-! ## The discharge -/

/-- **`Y3FineModuliAbP` from representability over `ℚ`** (given `TorsionStructure`, i.e. the textbook field
`mumfordTorsionAlgClosed`): `Φ_K` is Yoneda at `Spec K`; naturality is pasting; the universal object is the
representing one; the classifying maps of families over proper smooth curves are the representing maps. -/
theorem y3FineModuliAbP_of_rep (hT : ObjBridge.TorsionStructure) (hR : Y3RepresentableQ) :
    Y3FineModuliAbP := by
  obtain ⟨Y, 𝒜, hp, hs, hU⟩ := hR
  -- the fibre object at a field point
  have hfib : ∀ (K : Type) [Field K] [Algebra ℚ K] (y : fieldPt K ⟶ Y),
      ∃ P : QML3 K, IsFibreOf 𝒜.toQMFamily y.left P := fun K _ _ y =>
    qmAbFieldFibre _ (toKer 𝒜) K y.left
  let φ : ∀ (K : Type) [Field K] [Algebra ℚ K], (fieldPt K ⟶ Y) → M3 K :=
    fun K _ _ y => M3.mk (hfib K y).choose
  -- `φ y = [P]` iff `P` is a fibre at `y`
  have hφ : ∀ (K : Type) [Field K] [Algebra ℚ K] (y : fieldPt K ⟶ Y) (P : QML3 K),
      φ K y = M3.mk P ↔ IsFibreOf 𝒜.toQMFamily y.left P := by
    intro K _ _ y P
    constructor
    · intro h
      obtain ⟨f⟩ := Quotient.exact h
      exact isFibreOf_of_iso _ f.symm (hfib K y).choose_spec
    · intro h
      exact fibreClassUnique _ _ K y.left _ _ (hfib K y).choose_spec h
  have hbij : ∀ (K : Type) [Field K] [Algebra ℚ K], Function.Bijective (φ K) := by
    intro K _ _
    constructor
    · intro y y' hyy
      set P := (hfib K y).choose
      have hP : IsFibreOf 𝒜.toQMFamily y.left P := (hfib K y).choose_spec
      have hP' : IsFibreOf 𝒜.toQMFamily y'.left P := (hφ K y' P).mp hyy.symm
      obtain ⟨𝒜P, h𝒜P⟩ := exists_schemeP hT K P
      obtain ⟨g, -, hg⟩ := hU (fieldPt K) inferInstance 𝒜P
      exact (hg y ((h𝒜P _ _ _).mp hP)).trans (hg y' ((h𝒜P _ _ _).mp hP')).symm
    · intro c
      obtain ⟨P, rfl⟩ := Quotient.exists_rep c
      obtain ⟨𝒜P, h𝒜P⟩ := exists_schemeP hT K P
      obtain ⟨g, hg, -⟩ := hU (fieldPt K) inferInstance 𝒜P
      exact ⟨g, (hφ K g P).mpr ((h𝒜P _ _ _).mpr hg)⟩
  let Φ : PtEquiv Y := fun K _ _ => Equiv.ofBijective (φ K) (hbij K)
  have hΦ : ∀ (K : Type) [Field K] [Algebra ℚ K] (y : fieldPt K ⟶ Y) (P : QML3 K),
      Φ K y = M3.mk P ↔ IsFibreOf 𝒜.toQMFamily y.left P := hφ
  refine ⟨Y, Φ, hp, hs, ?_, ⟨𝒜, fun K _ _ y P h => (hΦ K y P).mp h⟩, ?_⟩
  · -- naturality in the field
    intro K L _ _ _ _ f y P hP
    obtain ⟨Q, hQ⟩ := hfib L (fieldMap f ≫ y)
    refine ⟨Q, (hΦ L _ Q).mpr hQ, ?_⟩
    exact isBaseChangeOf_of_fibres 𝒜.toQMFamily (f : K →+* L) y.left P Q ((hΦ K y P).mp hP) hQ
  · -- classifying maps of families over proper smooth curves
    intro S hpS hsS 𝒜' _
    obtain ⟨g, hg, -⟩ := hU S (isLocallyNoetherian_of_smooth_Q S hsS) 𝒜'
    exact ⟨g, fun K _ _ s P hP => (hΦ K (s ≫ g) P).mpr (isFibreOf_comp hg hP)⟩

/-- **The research field `ShimuraMainThmIDeligneY3AbU` from representability over `ℚ`**, y3-fix's
canonical-model leaf, and the textbook field `mumfordTorsionAlgClosed`. -/
theorem shimuraMainThmIDeligneY3AbU_of_rep (hM : AvSplit.MumfordTorsionAlgClosed) (hR : Y3RepresentableQ)
    (h2 : DeligneCanonicalModelY3EveryH) : ShimuraMainThmIDeligneY3AbU :=
  shimuraMainThmIDeligneY3AbU_of_print hM (y3FineModuliAbP_of_rep (AvSplit.torsionStructure_of_mumford hM) hR) h2

/-- **The research field from the two leaves alone**: `mumfordTorsionAlgClosed` is now a theorem
(`ZInQ.Contrib.CloudB3W16Torsion.mumfordTorsionAlgClosed_proof`). -/
theorem shimuraMainThmIDeligneY3AbU_of_rep' (hR : Y3RepresentableQ)
    (h2 : DeligneCanonicalModelY3EveryH) : ShimuraMainThmIDeligneY3AbU :=
  shimuraMainThmIDeligneY3AbU_of_rep ZInQ.Contrib.CloudB3W16Torsion.mumfordTorsionAlgClosed_proof hR h2

/-- `Y3FineModuliAbP` from representability alone. -/
theorem y3FineModuliAbP_of_rep' (hR : Y3RepresentableQ) : Y3FineModuliAbP :=
  y3FineModuliAbP_of_rep
    (AvSplit.torsionStructure_of_mumford ZInQ.Contrib.CloudB3W16Torsion.mumfordTorsionAlgClosed_proof) hR

end Y3Audit
