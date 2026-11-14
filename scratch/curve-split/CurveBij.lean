import ZInQKernel.HDecomp.QM.Pairs
import ZInQKernel.Contrib.CurvesG.CurveSplit
import ZInQKernel.Contrib.Dim.SmoothStalk

/-! # curve-split: row H-85 `ModelGlue.CurveBijIso`

`CurveBijIso` is copied verbatim (docstring and `def`) from `scratch/model-glue/ModelGlue6.lean`
(namespace `ModelGlue`, under `open LeafQM.AV`; it uses only `fieldPt` and `Qbar` from
`ZInQKernel/HDecomp/QM/Pairs.lean`).

Split:
* Part A (proved): `CurveBijIso` from its version over an algebraically closed field of
  characteristic 0 (`CurveBijIsoClosed`), by fpqc descent of isomorphisms along
  `Spec ℚ̄ → Spec ℚ` (Mathlib, `descendsAlong_isomorphisms_surjective_inf_flat_inf_quasicompact`,
  Stacks 02L4).
* Part B: `CurveBijIsoClosed` from the published leaf `BijToNormalIsIso` (a bijective morphism of
  irreducible varieties onto a normal variety in characteristic 0 is an isomorphism; Springer,
  Borel) and the reduction from proper smooth curves to integral ones.

No `sorry`, no `axiom`. -/

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

namespace ModelGlue

open LeafQM.AV

/-- **Textbook leaf: a bijection on `ℚ̄`-points between proper smooth curves over `ℚ` is an
isomorphism** (not proved here). A morphism `g : S → Y` over `ℚ` of proper smooth curves (smooth
of relative dimension 1) that induces a bijection `S(ℚ̄) → Y(ℚ̄)` is an isomorphism.
STANDARD (locators UNVERIFIED): `g` is quasi-finite (injective on `ℚ̄`-points; a positive-
dimensional fibre has infinitely many) and proper, hence finite (EGA III 4.4.2 / Hartshorne
III Ex. 11.2); in characteristic 0 it is generically étale, so the number of `ℚ̄`-points of a
general fibre over a component of `Y_ℚ̄` is the degree there (Hartshorne II.6.9, III.10.7), so
each degree is 1 and `g` is finite birational onto the normal `Y`, hence an isomorphism
(Hartshorne I.6.12 / II.6.7). -/
def CurveBijIso : Prop :=
  ∀ (S Y : Over (Spec (CommRingCat.of ℚ))), IsProper S.hom → SmoothOfRelativeDimension 1 S.hom →
    IsProper Y.hom → SmoothOfRelativeDimension 1 Y.hom → ∀ g : S ⟶ Y,
    Function.Bijective (fun s : fieldPt Qbar ⟶ S => s ≫ g) → IsIso g

end ModelGlue

namespace CurveSplit

open LeafQM.AV ModelGlue

/-- `Spec k`. -/
abbrev SpecK (k : Type) [Field k] : Scheme := Spec (CommRingCat.of k)

/-- `Spec k` over itself: morphisms `kPt k ⟶ X` in `Over (Spec k)` are the `k`-points of `X`. -/
abbrev kPt (k : Type) [Field k] : Over (SpecK k) := Over.mk (𝟙 (SpecK k))

/-- **`CurveBijIso` over an algebraically closed field of characteristic `0`** (intermediate
statement). -/
def CurveBijIsoClosed : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (T Z : Over (SpecK k)),
    IsProper T.hom → SmoothOfRelativeDimension 1 T.hom → IsProper Z.hom →
    SmoothOfRelativeDimension 1 Z.hom → ∀ h : T ⟶ Z,
      Function.Bijective (fun t : kPt k ⟶ T => t ≫ h) → IsIso h

/-! ## Part A: descent from `ℚ̄` to `ℚ` -/

section PartA

variable {S Y : Over (Spec (CommRingCat.of ℚ))} (g : S ⟶ Y)

/-- `Spec ℚ̄ → Spec ℚ`. -/
abbrev bQ : SpecK Qbar ⟶ Spec (CommRingCat.of ℚ) := (fieldPt Qbar).hom

/-- The base change `g_ℚ̄ : S_ℚ̄ → Y_ℚ̄`. -/
abbrev bcMap : pullback S.hom bQ ⟶ pullback Y.hom bQ :=
  pullback.map S.hom bQ Y.hom bQ g.left (𝟙 _) (𝟙 _) (by simp [Over.w g]) (by simp)

theorem bcMap_snd : bcMap g ≫ pullback.snd Y.hom bQ = pullback.snd S.hom bQ := by
  simp [bcMap]

theorem bcMap_fst : bcMap g ≫ pullback.fst Y.hom bQ = pullback.fst S.hom bQ ≫ g.left := by
  simp [bcMap]

/-- The square `S_ℚ̄ → Y_ℚ̄ → Y`, `S_ℚ̄ → S → Y` is a pullback. -/
theorem bcMap_isPullback :
    IsPullback (bcMap g) (pullback.fst S.hom bQ) (pullback.fst Y.hom bQ) g.left := by
  refine IsPullback.of_right ?_ (bcMap_fst g) (IsPullback.of_hasPullback Y.hom bQ).flip
  rw [bcMap_snd, Over.w g]
  exact (IsPullback.of_hasPullback S.hom bQ).flip

instance : Subsingleton (Spec (CommRingCat.of ℚ)) :=
  inferInstanceAs (Subsingleton (PrimeSpectrum ℚ))

instance : Nonempty (SpecK Qbar) := inferInstanceAs (Nonempty (PrimeSpectrum Qbar))

instance bQ_surjective : Surjective bQ :=
  ⟨fun _ => ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩⟩

instance bQ_flat : Flat bQ := by
  show Flat (Spec.map (CommRingCat.ofHom (algebraMap ℚ Qbar)))
  rw [HasRingHomProperty.Spec_iff (P := @Flat)]
  simp only [CommRingCat.hom_ofHom]
  rw [RingHom.flat_algebraMap_iff]
  infer_instance

/-- A `ℚ̄`-point of `W_ℚ̄` gives a `ℚ̄`-point of `W` over `ℚ`. -/
def toS {W : Over (Spec (CommRingCat.of ℚ))} (t : kPt Qbar ⟶ Over.mk (pullback.snd W.hom bQ)) :
    fieldPt Qbar ⟶ W :=
  Over.homMk (show (fieldPt Qbar).left ⟶ W.left from t.left ≫ pullback.fst W.hom bQ) (by
    have h1 : t.left ≫ pullback.snd W.hom bQ = 𝟙 _ := by simpa using Over.w t
    show (t.left ≫ pullback.fst W.hom bQ) ≫ W.hom = bQ
    rw [Category.assoc, pullback.condition, ← Category.assoc, h1, Category.id_comp])

theorem toS_left {W : Over (Spec (CommRingCat.of ℚ))}
    (t : kPt Qbar ⟶ Over.mk (pullback.snd W.hom bQ)) :
    (toS t).left = t.left ≫ pullback.fst W.hom bQ := rfl

theorem sec_snd {W : Over (Spec (CommRingCat.of ℚ))}
    (t : kPt Qbar ⟶ Over.mk (pullback.snd W.hom bQ)) :
    t.left ≫ pullback.snd W.hom bQ = 𝟙 _ := by simpa using Over.w t

/-- The `ℚ̄`-points correspond (compatibly with `g`). -/
theorem bij_bc (hb : Function.Bijective (fun s : fieldPt Qbar ⟶ S => s ≫ g)) :
    Function.Bijective (fun t : kPt Qbar ⟶ Over.mk (pullback.snd S.hom bQ) =>
      t ≫ (Over.homMk (bcMap g) (bcMap_snd g) :
        Over.mk (pullback.snd S.hom bQ) ⟶ Over.mk (pullback.snd Y.hom bQ))) := by
  have hcomp : ∀ t : kPt Qbar ⟶ Over.mk (pullback.snd S.hom bQ),
      toS (t ≫ (Over.homMk (bcMap g) (bcMap_snd g) :
        Over.mk (pullback.snd S.hom bQ) ⟶ Over.mk (pullback.snd Y.hom bQ))) = toS t ≫ g := by
    intro t
    ext1
    change (t.left ≫ bcMap g) ≫ pullback.fst Y.hom bQ = (t.left ≫ pullback.fst S.hom bQ) ≫ g.left
    rw [Category.assoc, bcMap_fst, Category.assoc]
  constructor
  · intro t₁ t₂ he
    have h1 : toS t₁ ≫ g = toS t₂ ≫ g := by
      rw [← hcomp, ← hcomp]
      exact congrArg toS he
    have h2 := congrArg CommaMorphism.left (hb.1 h1)
    change t₁.left ≫ pullback.fst S.hom bQ = t₂.left ≫ pullback.fst S.hom bQ at h2
    ext1
    apply pullback.hom_ext
    · exact h2
    · rw [sec_snd t₁, sec_snd t₂]
  · intro z
    obtain ⟨s, hs⟩ := hb.2 (toS z)
    have hsw : s.left ≫ S.hom = 𝟙 (SpecK Qbar) ≫ bQ := by
      rw [Category.id_comp]; exact Over.w s
    let s' : SpecK Qbar ⟶ S.left := s.left
    let l : SpecK Qbar ⟶ pullback S.hom bQ := pullback.lift s' (𝟙 (SpecK Qbar)) hsw
    have hl1 : l ≫ pullback.fst S.hom bQ = s' := pullback.lift_fst _ _ _
    have hl2 : l ≫ pullback.snd S.hom bQ = 𝟙 _ := pullback.lift_snd _ _ _
    refine ⟨Over.homMk l hl2, ?_⟩
    have h3 := congrArg CommaMorphism.left hs
    change s' ≫ g.left = z.left ≫ pullback.fst Y.hom bQ at h3
    ext1
    change l ≫ bcMap g = z.left
    apply pullback.hom_ext
    · rw [Category.assoc, bcMap_fst, ← Category.assoc, hl1]
      exact h3
    · rw [Category.assoc, bcMap_snd, hl2, sec_snd z]; rfl

/-- **Part A (proved): `CurveBijIso` from `CurveBijIsoClosed`.** -/
theorem curveBijIso_of_closed (h : CurveBijIsoClosed) : CurveBijIso := by
  intro S Y hPS hSS hPY hSY g hb
  have hiso : IsIso (Over.homMk (bcMap g) (bcMap_snd g) :
      Over.mk (pullback.snd S.hom bQ) ⟶ Over.mk (pullback.snd Y.hom bQ)) :=
    h Qbar _ _ (by show IsProper (pullback.snd S.hom bQ); infer_instance)
      (by show SmoothOfRelativeDimension 1 (pullback.snd S.hom bQ); infer_instance)
      (by show IsProper (pullback.snd Y.hom bQ); infer_instance)
      (by show SmoothOfRelativeDimension 1 (pullback.snd Y.hom bQ); infer_instance) _ (bij_bc g hb)
  have hiso' : IsIso (bcMap g) := by
    have := (Over.forget _).map_isIso (Over.homMk (bcMap g) (bcMap_snd g) :
      Over.mk (pullback.snd S.hom bQ) ⟶ Over.mk (pullback.snd Y.hom bQ))
    simpa using this
  have hQ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme)
      (pullback.fst Y.hom bQ) := ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  have : IsIso g.left :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := MorphismProperty.isomorphisms Scheme)
      (bcMap_isPullback g) hQ hiso'
  have : IsIso ((Over.forget _).map g) := this
  exact isIso_of_reflects_iso g (Over.forget _)

end PartA

end CurveSplit

#print axioms CurveSplit.curveBijIso_of_closed
