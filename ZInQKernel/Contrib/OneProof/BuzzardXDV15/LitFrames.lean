import ZInQKernel.Contrib.OneProof.BuzzardXDV15.Defs
import Mathlib

/-!
# Literal full level-5 structures (Buzzard, Def. 1.1)

Buzzard (Duke Math. J. 87 (1997), p. 3): a naive full level `M` structure on `A/S` is "an
isomorphism α : (O_D ⊗ ℤ/Mℤ)_S ≅ A[M] of schemes which preserves the left action of O_D", and
`F_{A/S,M}(T)` is the set of full level `M` structures on `A_T`, that is, isomorphisms of
`T`-schemes `(O ⊗ Z/MZ)_T ≅ A[M]_T`; `δ ∈ (O/MO)ˣ` acts by `α ↦ α ∘ r_δ`, with `r_δ` the right
multiplication by `δ`.

Here `M = 5`. The constant scheme `(O/5O)_T` is `∐_q T`, so a morphism of `T`-schemes
`(O/5O)_T ⟶ A[5]_T = A[5] ×_S T` is a family `α q` of `5`-torsion points of `A` over `T` (its
restrictions to the copies of `T`). A literal frame is such a family which is `O`-linear,
`α (a q) = ι(a) (α q)`, and whose induced morphism `∐_q T ⟶ A[5] ×_S T` is an isomorphism.

* Restriction along `T' ⟶ T` is precomposition. The isomorphism condition is stable: each
  component square is cartesian, and finite coproducts of schemes are universal.
* Evaluation at `1` is a natural isomorphism onto the generator presheaf `Frames5 A`, as soon as
  multiplication by `5` is étale. Its inverse sends `P` to `q ↦ ι(q) P`; the induced morphism is a
  surjective open immersion: its components are sections of the étale map `A[5]_T ⟶ T`, they are
  disjoint by the first clause of `IsGenAt`, and they cover by the second one.
* Evaluation at `1` sends `α ∘ r_δ` to `ι(σ δ) (α 1)`, so it identifies the `H5`-orbit spaces.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open LeafQM LeafQM.AV
open scoped CategoryTheory.Obj

namespace Y3Buzzard.XDV15

attribute [local instance] FEC.grp

/-! ## 1. `A[5]_T` and the morphism `∐_q T ⟶ A[5]_T` -/

section Comparison

variable {S : Scheme.{0}} (A : FEC S)

/-- The structure map `A[5] ⟶ S` of the `5`-torsion `A[5] = LevelM.WM 5 A`. -/
abbrev tors5 : LevelM.WM 5 A ⟶ S := LevelM.jM 5 A ≫ A.F.hom

theorem pow5_iff {T : Over S} (x : T ⟶ A.F) :
    x ^ 5 = 1 ↔ x.left ≫ A.iota ((5 : ℕ) : O) = T.hom ≫ torsZeroL A := by
  rw [← comp_iotaHom_natCast, comp_iota_eq_one_iff]

theorem jM_iota5 :
    LevelM.jM 5 A ≫ A.iota ((5 : ℕ) : O) = (LevelM.jM 5 A ≫ A.F.hom) ≫ torsZeroL A := by
  rw [pullback.condition, torsFst_hom]

/-- The `T`-point of `A[5] ×_S T` given by a `5`-torsion point `x` of `A` over `T`. -/
def torsPt {T : Over S} (x : T ⟶ A.F) (hx : x ^ 5 = 1) : T.left ⟶ pullback (tors5 A) T.hom :=
  pullback.lift (pullback.lift x.left T.hom ((pow5_iff A x).1 hx)) (𝟙 T.left) (by
    show pullback.lift x.left T.hom _ ≫ pullback.fst _ _ ≫ A.F.hom = 𝟙 T.left ≫ T.hom
    rw [pullback.lift_fst_assoc, Category.id_comp]
    exact Over.w x)

@[reassoc (attr := simp)]
theorem torsPt_snd {T : Over S} (x : T ⟶ A.F) (hx : x ^ 5 = 1) :
    torsPt A x hx ≫ pullback.snd _ _ = 𝟙 T.left :=
  pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
theorem torsPt_fst {T : Over S} (x : T ⟶ A.F) (hx : x ^ 5 = 1) :
    torsPt A x hx ≫ pullback.fst _ _ ≫ LevelM.jM 5 A = x.left := by
  rw [torsPt, pullback.lift_fst_assoc, pullback.lift_fst]

/-- The morphism of `T`-schemes `(O/5O)_T = ∐_q T ⟶ A[5]_T` with components `α q`. -/
def litMap {T : Over S} (α : Y3OrderMod.OMod 5 → (T ⟶ A.F)) (h : ∀ q, α q ^ 5 = 1) :
    ∐ (fun _ : Y3OrderMod.OMod 5 => T.left) ⟶ pullback (tors5 A) T.hom :=
  Sigma.desc fun q => torsPt A (α q) (h q)

/-- The base change morphism `A[5]_{T'} ⟶ A[5]_T` over `f : T' ⟶ T`. -/
def bc {T T' : Over S} (f : T' ⟶ T) : pullback (tors5 A) T'.hom ⟶ pullback (tors5 A) T.hom :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ f.left)
    (by rw [pullback.condition, Category.assoc, Over.w f])

/-- `A[5]_{T'}` is the base change of `A[5]_T` along `T' ⟶ T`. -/
theorem bc_isPullback {T T' : Over S} (f : T' ⟶ T) :
    IsPullback (pullback.snd (tors5 A) T'.hom) (bc A f) f.left (pullback.snd (tors5 A) T.hom) := by
  refine (IsPullback.of_right (h₁₁ := bc A f) (h₁₂ := pullback.fst (tors5 A) T.hom)
    (v₁₃ := tors5 A) (h₂₂ := T.hom) ?_ (pullback.lift_snd _ _ _)
    (IsPullback.of_hasPullback _ _)).flip
  simp only [bc, pullback.lift_fst, Over.w f]
  exact IsPullback.of_hasPullback _ _

/-- Each component square of the restriction is cartesian. -/
theorem torsPt_isPullback {T T' : Over S} (f : T' ⟶ T) (x : T ⟶ A.F) (hx : x ^ 5 = 1)
    (hx' : (f ≫ x) ^ 5 = 1) :
    IsPullback (torsPt A (f ≫ x) hx') f.left (bc A f) (torsPt A x hx) := by
  refine IsPullback.of_right (h₁₂ := pullback.snd (tors5 A) T'.hom)
    (h₂₂ := pullback.snd (tors5 A) T.hom) (v₁₃ := f.left) ?_ ?_ (bc_isPullback A f)
  · rw [torsPt_snd, torsPt_snd]
    exact IsPullback.of_id_fst
  · apply pullback.hom_ext
    · rw [← cancel_mono (LevelM.jM 5 A)]
      simp only [bc, Category.assoc, pullback.lift_fst, torsPt_fst, Over.comp_left]
    · simp only [bc, Category.assoc, pullback.lift_snd, torsPt_snd_assoc, torsPt_snd,
        Category.comp_id]

/-- The isomorphism condition is stable under base change. -/
theorem isIso_litMap_comp {T T' : Over S} (f : T' ⟶ T) (α : Y3OrderMod.OMod 5 → (T ⟶ A.F))
    (h : ∀ q, α q ^ 5 = 1) (h' : ∀ q, (f ≫ α q) ^ 5 = 1) (hiso : IsIso (litMap A α h)) :
    IsIso (litMap A (fun q => f ≫ α q) h') := by
  have hπ : IsIso (Sigma.desc fun q => pullback.fst (bc A f) (torsPt A (α q) (h q))) :=
    FinitaryPreExtensive.isIso_sigmaDesc_fst (fun q => torsPt A (α q) (h q)) (bc A f) hiso
  have e : litMap A (fun q => f ≫ α q) h' =
      Limits.Sigma.map (fun q => (torsPt_isPullback A f (α q) (h q) (h' q)).isoPullback.hom) ≫
        Sigma.desc fun q => pullback.fst (bc A f) (torsPt A (α q) (h q)) := by
    apply Sigma.hom_ext
    intro q
    simp [litMap]
  rw [e]
  infer_instance

end Comparison

/-! ## 2. Literal frames and their presheaf -/

section Presheaf

variable {S : Scheme.{0}} (A : FEC S)

/-- A literal full level-5 structure on `A_T` (Buzzard, Def. 1.1): an `O`-linear isomorphism of
`T`-schemes `(O/5O)_T ≅ A[5]_T`, recorded by its restrictions `α q` to the copies of `T`. -/
@[ext]
structure LitFrame (T : Over S) where
  /-- The restriction of `α` to the copy of `T` indexed by `q`. -/
  α : Y3OrderMod.OMod 5 → (T ⟶ A.F)
  tors : ∀ q, α q ^ 5 = 1
  lin : ∀ (a : O) (q : Y3OrderMod.OMod 5), α ((a : Y3OrderMod.OMod 5) * q) = α q ≫ iotaO A a
  iso : IsIso (litMap A α tors)

variable {A}

/-- Restriction of a literal frame along `f : T' ⟶ T`: precomposition. -/
def LitFrame.restrict {T T' : Over S} (f : T' ⟶ T) (x : LitFrame A T) : LitFrame A T' where
  α q := f ≫ x.α q
  tors q := by rw [← MonObj.comp_pow, x.tors q, MonObj.comp_one]
  lin a q := by rw [x.lin a q, Category.assoc]
  iso := isIso_litMap_comp A f x.α x.tors _ x.iso

variable (A)

/-- `T ↦ F_{A/S,5}(T)`: the presheaf of literal full level-5 structures. -/
def LitFrames5 : (Over S)ᵒᵖ ⥤ Type where
  obj T := LitFrame A T.unop
  map f := ↾fun x => x.restrict f.unop
  map_id T := by
    ext x q
    exact congrArg (fun g => g.left) (Category.id_comp (x.α q))
  map_comp f g := by
    ext x q
    exact congrArg (fun g => g.left) (Category.assoc g.unop f.unop (x.α q))

end Presheaf

/-! ## 3. Evaluation at `1` gives a frame -/

section Eval

variable {S : Scheme.{0}} {A : FEC S}

/-- `O`-linearity at `1`: `α [a] = ι(a) (α 1)`. -/
theorem LitFrame.α_coe {T : Over S} (x : LitFrame A T) (a : O) :
    x.α (a : Y3OrderMod.OMod 5) = x.α 1 ≫ iotaO A a := by
  rw [← x.lin, _root_.mul_one]

/-- Evaluation at `1` gives a generator: the induced morphism is bijective on geometric points,
and these are `q ↦ ι(q) (α 1)` on one side and the `5`-torsion points on the other. -/
theorem LitFrame.isGen {T : Over S} (x : LitFrame A T) : IsGen 5 A (x.α 1).left := by
  have hiso := x.iso
  have ht1 : (x.α 1).left ≫ A.iota ((5 : ℕ) : O) = T.hom ≫ torsZeroL A :=
    (pow5_iff A _).1 (x.tors 1)
  refine ⟨(torsPow_eq_one_iff A _ 5).2 (by rw [Over.w (x.α 1)]; exact ht1), fun k _ _ s => ?_⟩
  have hs : s ≫ (x.α 1).left ≫ A.F.hom = s ≫ T.hom := by rw [Over.w (x.α 1)]
  refine ⟨fun a => ⟨fun ha => ?_, fun ha => ?_⟩, fun y hy => ?_⟩
  · rw [comp_iota_eq_one_iff] at ha
    simp only [Over.homMk_left, Over.mk_hom] at ha
    rw [LevelM.memM_iff]
    have h0 : (x.α ((0 : O) : Y3OrderMod.OMod 5)).left = T.hom ≫ torsZeroL A := by
      rw [x.α_coe]
      exact (comp_iota_eq_one_iff A (x.α 1) 0).1 (by rw [iotaHom_zero, MonObj.comp_one])
    have hpt : s ≫ (x.α (a : Y3OrderMod.OMod 5)).left =
        s ≫ (x.α ((0 : O) : Y3OrderMod.OMod 5)).left := by
      rw [h0, x.α_coe]
      calc s ≫ (x.α 1 ≫ iotaO A a).left = (s ≫ (x.α 1).left) ≫ A.iota a := by
            rw [Over.comp_left]; exact (Category.assoc _ _ _).symm
        _ = s ≫ T.hom ≫ torsZeroL A := by rw [ha, hs, Category.assoc]
    have hpt' : s ≫ torsPt A _ (x.tors (a : Y3OrderMod.OMod 5)) =
        s ≫ torsPt A _ (x.tors ((0 : O) : Y3OrderMod.OMod 5)) := by
      apply pullback.hom_ext
      · rw [← cancel_mono (LevelM.jM 5 A)]
        simp only [Category.assoc, torsPt_fst]
        exact hpt
      · simp only [Category.assoc, torsPt_snd]
    have hι : s ≫ Sigma.ι (fun _ : Y3OrderMod.OMod 5 => T.left) (a : Y3OrderMod.OMod 5) =
        s ≫ Sigma.ι (fun _ : Y3OrderMod.OMod 5 => T.left) ((0 : O) : Y3OrderMod.OMod 5) := by
      rw [← cancel_mono (litMap A x.α x.tors)]
      simp only [Category.assoc, litMap, Sigma.ι_comp_desc]
      exact hpt'
    obtain ⟨p⟩ := spec_field_nonempty k
    have hp := congrArg (fun g => g p) hι
    simp only [Scheme.Hom.comp_apply] at hp
    exact congrArg Sigma.fst ((sigmaι_eq_iff _ _ _ _ _).1 hp)
  · obtain ⟨b, rfl⟩ := ha
    refine comp_iota_natCast_mul_eq_one A 5 _ ?_ b
    rw [comp_iota_eq_one_iff]
    simp only [Over.homMk_left, Over.mk_hom]
    rw [Category.assoc, ht1, hs, Category.assoc]
  · have hy' := (pow5_iff A y).1 hy
    simp only [Over.mk_hom] at hy'
    have hyw : y.left ≫ A.F.hom = s ≫ T.hom := (Over.w y).trans hs
    obtain ⟨z, hz1, hz2⟩ : ∃ z : Spec (CommRingCat.of k) ⟶ pullback (tors5 A) T.hom,
        z ≫ pullback.fst _ _ ≫ LevelM.jM 5 A = y.left ∧ z ≫ pullback.snd _ _ = s :=
      ⟨pullback.lift (pullback.lift y.left _ hy') s (by
        show pullback.lift y.left _ hy' ≫ pullback.fst _ _ ≫ A.F.hom = s ≫ T.hom
        rw [pullback.lift_fst_assoc]; exact hyw),
        by rw [pullback.lift_fst_assoc]; exact pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    obtain ⟨p⟩ := spec_field_nonempty k
    obtain ⟨⟨q, t⟩, hqt⟩ : ∃ u, sigmaMk (fun _ : Y3OrderMod.OMod 5 => T.left) u =
        (z ≫ inv (litMap A x.α x.tors)) p :=
      ⟨_, (sigmaMk _).apply_symm_apply _⟩
    rw [sigmaMk_mk] at hqt
    have hr : Set.range ⇑(z ≫ inv (litMap A x.α x.tors)) ⊆
        Set.range ⇑(Sigma.ι (fun _ : Y3OrderMod.OMod 5 => T.left) q) := by
      rintro _ ⟨p', rfl⟩
      exact ⟨t, by rw [hqt, Subsingleton.elim p' p]⟩
    have hw : IsOpenImmersion.lift _ _ hr ≫ torsPt A (x.α q) (x.tors q) = z := by
      rw [← Sigma.ι_comp_desc (fun q => torsPt A (x.α q) (x.tors q)) q, ← Category.assoc,
        IsOpenImmersion.lift_fac]
      show (z ≫ inv (litMap A x.α x.tors)) ≫ litMap A x.α x.tors = z
      rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    have hws : IsOpenImmersion.lift _ _ hr = s := by
      have e := congrArg (fun g => g ≫ pullback.snd _ _) hw
      simp only [Category.assoc, torsPt_snd, Category.comp_id] at e
      exact e.trans hz2
    have hyl : y.left = s ≫ (x.α q).left := by
      have e := congrArg (fun g => g ≫ pullback.fst _ _ ≫ LevelM.jM 5 A) hw
      simp only [Category.assoc, torsPt_fst, hz1, hws] at e
      exact e.symm
    obtain ⟨r, rfl⟩ : ∃ r : O, (r : Y3OrderMod.OMod 5) = q := Y3OrderMod.coe_surjective 5 q
    refine ⟨r, Over.OverMorphism.ext ?_⟩
    rw [hyl, x.α_coe]
    simp only [Over.comp_left, Over.homMk_left, Category.assoc]

end Eval

/-! ## 4. The inverse `P ↦ (q ↦ ι(q) P)`, under étaleness of multiplication by `5` -/

section Inverse

variable {S : Scheme.{0}} (A : FEC S)

/-- A section of an étale morphism is an open immersion: it is the base change of the diagonal,
which is an open immersion. -/
theorem isOpenImmersion_of_section {X Y : Scheme.{0}} (s : X ⟶ Y) (g : Y ⟶ X)
    [AlgebraicGeometry.Etale g] (hs : s ≫ g = 𝟙 X) : IsOpenImmersion s := by
  have : MorphismProperty.HasOfPostcompProperty @IsOpenImmersion @AlgebraicGeometry.Etale :=
    MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.2 fun _ _ f _ =>
      FormallyUnramified.isOpenImmersion_diagonal f
  exact MorphismProperty.of_postcomp @IsOpenImmersion (W' := @AlgebraicGeometry.Etale) s g
    inferInstance (by rw [hs]; infer_instance)

/-- For a frame `P`, the morphism `∐_q T ⟶ A[5]_T` with components `ι(q) P` is an isomorphism:
a surjective open immersion. -/
theorem isIso_litMap_of_isGen (het : AlgebraicGeometry.Etale (A.iota ((5 : ℕ) : O)))
    {T : Over S} (P : T ⟶ A.F) (hP : IsGen 5 A P.left)
    (h : ∀ q, (P ≫ iotaO A (LevelM.repO 5 q)) ^ 5 = 1) :
    IsIso (litMap A (fun q => P ≫ iotaO A (LevelM.repO 5 q)) h) := by
  have h5 : AlgebraicGeometry.Etale (tors5 A) := torsFst_hom_etale A 5 het
  have : AlgebraicGeometry.Etale (pullback.snd (tors5 A) T.hom) :=
    MorphismProperty.of_isPullback (P := @AlgebraicGeometry.Etale)
      (IsPullback.of_hasPullback (tors5 A) T.hom) h5
  have hO : ∀ q, IsOpenImmersion (torsPt A (P ≫ iotaO A (LevelM.repO 5 q)) (h q)) := fun q =>
    isOpenImmersion_of_section _ (pullback.snd (tors5 A) T.hom) (torsPt_snd _ _ _)
  refine (isIso_iff_isOpenImmersion_and_surjective _).2
    ⟨isOpenImmersion_sigmaDesc _ _ ?_, ⟨fun y => ?_⟩⟩
  · intro q q' hqq'
    rw [Function.onFun, Set.disjoint_left]
    rintro _ ⟨t₁, rfl⟩ ⟨t₂, ht₂⟩
    obtain ⟨w, -, -⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := torsPt A _ (h q)) (g := torsPt A _ (h q')) t₁ t₂ ht₂.symm
    apply hqq'
    have hc := pullback.condition (f := torsPt A _ (h q)) (g := torsPt A _ (h q'))
    have h2 : pullback.fst (torsPt A _ (h q)) (torsPt A _ (h q')) =
        pullback.snd (torsPt A _ (h q)) (torsPt A _ (h q')) := by
      have e := congrArg (fun g => g ≫ pullback.snd (tors5 A) T.hom) hc
      simpa only [Category.assoc, torsPt_snd, Category.comp_id] using e
    have h1 := congrArg (fun g => g ≫ pullback.fst (tors5 A) T.hom ≫ LevelM.jM 5 A) hc
    simp only [Category.assoc, torsPt_fst, ← h2, Over.comp_left, iotaO, Over.homMk_left] at h1
    have hgen := hP.2 (geomK w) (geomPt w ≫ pullback.fst (torsPt A _ (h q)) (torsPt A _ (h q')))
    have hxy : (Over.homMk (U := Over.mk ((geomPt w ≫
          pullback.fst (torsPt A _ (h q)) (torsPt A _ (h q'))) ≫ P.left ≫ A.F.hom))
          ((geomPt w ≫ pullback.fst (torsPt A _ (h q)) (torsPt A _ (h q'))) ≫ P.left)
          (Category.assoc _ _ _) : _ ⟶ A.F) ≫ iotaO A (LevelM.repO 5 q) =
        Over.homMk ((geomPt w ≫ pullback.fst (torsPt A _ (h q)) (torsPt A _ (h q'))) ≫ P.left)
          (Category.assoc _ _ _) ≫ iotaO A (LevelM.repO 5 q') := by
      apply Over.OverMorphism.ext
      simp only [Over.comp_left, Over.homMk_left, iotaO, Category.assoc]
      rw [h1]
    obtain ⟨b, hb⟩ := (hgen.1 _).1 (FrameTorsor.comp_iota_sub_eq_one A _ hxy)
    have e := (Y3OrderMod.coe_eq_coe_iff (M := 5)).2 ⟨b, hb⟩
    rwa [LevelM.repO_spec, LevelM.repO_spec] at e
  · obtain ⟨p⟩ := spec_field_nonempty (geomK y)
    have hgen := hP.2 (geomK y) (geomPt y ≫ pullback.snd (tors5 A) T.hom)
    have hv : (geomPt y ≫ pullback.fst (tors5 A) T.hom ≫ LevelM.jM 5 A) ≫ A.F.hom =
        (geomPt y ≫ pullback.snd (tors5 A) T.hom) ≫ P.left ≫ A.F.hom := by
      rw [Over.w P]
      simp only [Category.assoc]
      rw [← pullback.condition]
    have hV : (Over.homMk (U := Over.mk ((geomPt y ≫ pullback.snd (tors5 A) T.hom) ≫ P.left ≫
        A.F.hom)) (geomPt y ≫ pullback.fst (tors5 A) T.hom ≫ LevelM.jM 5 A) hv : _ ⟶ A.F) ^ 5 =
          1 := by
      rw [pow5_iff]
      simp only [Over.homMk_left, Over.mk_hom]
      rw [← hv]
      simp only [Category.assoc, jM_iota5]
    obtain ⟨a, ha⟩ := hgen.2 _ hV
    have ha' := congrArg (fun g => g.left) ha
    simp only [Over.comp_left, Over.homMk_left, Category.assoc] at ha'
    have hfac : (geomPt y ≫ pullback.snd (tors5 A) T.hom) ≫
        Sigma.ι (fun _ : Y3OrderMod.OMod 5 => T.left) (a : Y3OrderMod.OMod 5) ≫
          litMap A (fun q => P ≫ iotaO A (LevelM.repO 5 q)) h = geomPt y := by
      rw [litMap, Sigma.ι_comp_desc]
      apply pullback.hom_ext
      · rw [← cancel_mono (LevelM.jM 5 A)]
        simp only [Category.assoc, torsPt_fst, Over.comp_left, iotaO, Over.homMk_left]
        rw [FrameTorsor.tors_iota_congr A P.left hP.1 (LevelM.repO_spec 5 (a : Y3OrderMod.OMod 5)),
          ha']
      · simp only [Category.assoc, torsPt_snd, Category.comp_id]
    refine ⟨((geomPt y ≫ pullback.snd (tors5 A) T.hom) ≫
      Sigma.ι (fun _ : Y3OrderMod.OMod 5 => T.left) (a : Y3OrderMod.OMod 5)) p, ?_⟩
    rw [← Scheme.Hom.comp_apply, Category.assoc, hfac, geomPt_apply]

/-- The literal frame of a frame `P`: `q ↦ ι(q) P`. -/
def litOfFrame (het : AlgebraicGeometry.Etale (A.iota ((5 : ℕ) : O))) {T : Over S}
    (P : T ⟶ A.F) (hP : IsGen 5 A P.left) : LitFrame A T where
  α q := P ≫ iotaO A (LevelM.repO 5 q)
  tors q := (GF5.fecAct A T).act_tors (frame_pow5 A P hP) _
  lin a q := by
    have hP5 : P ≫ iotaO A ((5 : ℕ) : O) = 1 :=
      (comp_iotaHom_natCast A P 5).trans (frame_pow5 A P hP)
    refine (FrameTorsor.comp_iota_congr A P hP5 ?_).trans (comp_iota_comp_iota A P _ _).symm
    rw [LevelM.repO_spec, RingCon.coe_mul, LevelM.repO_spec]
  iso := isIso_litMap_of_isGen A het P hP _

/-- Evaluation at `1`, a bijection from literal frames to frames over each `T`. -/
def evalEquiv (het : AlgebraicGeometry.Etale (A.iota ((5 : ℕ) : O))) (T : (Over S)ᵒᵖ) :
    LitFrame A T.unop ≃ (Frames5 A).obj T where
  toFun x := ⟨x.α 1, x.isGen⟩
  invFun P := litOfFrame A het P.1 P.2
  left_inv x := LitFrame.ext (funext fun q => by
    show x.α 1 ≫ iotaO A (LevelM.repO 5 q) = x.α q
    rw [← x.α_coe, LevelM.repO_spec])
  right_inv P := Subtype.ext (by
    show P.1 ≫ iotaO A (LevelM.repO 5 1) = P.1
    have hP5 : P.1 ≫ iotaO A ((5 : ℕ) : O) = 1 :=
      (comp_iotaHom_natCast A P.1 5).trans (frame_pow5 A P.1 P.2)
    refine (FrameTorsor.comp_iota_congr A P.1 hP5 (b := 1) ?_).trans ?_
    · rw [LevelM.repO_spec]; rfl
    · rw [iotaHom_one, Category.comp_id])

/-- Literal full level-5 structures are frames: evaluation at `1` is a natural isomorphism
`LitFrames5 A ≅ Frames5 A`, with inverse `P ↦ (q ↦ ι(q) P)`. -/
def litFramesIso (het : AlgebraicGeometry.Etale (A.iota ((5 : ℕ) : O))) :
    LitFrames5 A ≅ Frames5 A :=
  NatIso.ofComponents (fun T => (evalEquiv A het T).toIso) (fun f => by ext x; rfl)

theorem litFramesIso_hom_app (het : AlgebraicGeometry.Etale (A.iota ((5 : ℕ) : O)))
    (T : (Over S)ᵒᵖ) (x : (LitFrames5 A).obj T) :
    ((litFramesIso A het).hom.app T x).1 = x.α 1 := rfl

theorem litFramesIso_inv_app (het : AlgebraicGeometry.Etale (A.iota ((5 : ℕ) : O)))
    (T : (Over S)ᵒᵖ) (P : (Frames5 A).obj T) (q : Y3OrderMod.OMod 5) :
    ((litFramesIso A het).inv.app T P).α q = P.1 ≫ iotaO A (LevelM.repO 5 q) := rfl

end Inverse

/-! ## 5. The action `α ↦ α ∘ r_δ` and the orbit presheaves -/

section Action

variable {S : Scheme.{0}} {A : FEC S}

/-- Right multiplication `r_δ : q ↦ q δ` on the constant scheme `(O/5O)_X = ∐_q X`. -/
def rmul (X : Scheme.{0}) (δ : Y3OrderMod.G 5) :
    ∐ (fun _ : Y3OrderMod.OMod 5 => X) ⟶ ∐ (fun _ : Y3OrderMod.OMod 5 => X) :=
  Sigma.desc fun q => Sigma.ι (fun _ : Y3OrderMod.OMod 5 => X) (q * δ)

theorem rmul_comp (X : Scheme.{0}) (δ ε : Y3OrderMod.G 5) :
    rmul X δ ≫ rmul X ε = rmul X (δ * ε) := by
  apply Sigma.hom_ext
  intro q
  simp [rmul, _root_.mul_assoc]

theorem rmul_one (X : Scheme.{0}) : rmul X 1 = 𝟙 _ := by
  apply Sigma.hom_ext
  intro q
  simp [rmul]

instance (X : Scheme.{0}) (δ : Y3OrderMod.G 5) : IsIso (rmul X δ) :=
  ⟨⟨rmul X δ⁻¹, by rw [rmul_comp, mul_inv_cancel, rmul_one],
    by rw [rmul_comp, inv_mul_cancel, rmul_one]⟩⟩

/-- Buzzard's action `α ↦ α ∘ r_δ` of `δ ∈ (O/5O)ˣ` on literal frames: `q ↦ α (q δ)`. -/
def LitFrame.act {T : Over S} (x : LitFrame A T) (δ : Y3OrderMod.G 5) : LitFrame A T where
  α q := x.α (q * δ)
  tors q := x.tors _
  lin a q := by rw [← x.lin, _root_.mul_assoc]
  iso := by
    have e : litMap A (fun q => x.α (q * δ)) (fun q => x.tors _) =
        rmul T.left δ ≫ litMap A x.α x.tors := by
      apply Sigma.hom_ext
      intro q
      simp [litMap, rmul]
    have := x.iso
    rw [e]
    infer_instance

theorem LitFrame.act_one {T : Over S} (x : LitFrame A T) : x.act 1 = x :=
  LitFrame.ext (funext fun q => by simp [LitFrame.act])

theorem LitFrame.act_act {T : Over S} (x : LitFrame A T) (δ ε : Y3OrderMod.G 5) :
    (x.act δ).act ε = x.act (ε * δ) :=
  LitFrame.ext (funext fun q => by simp [LitFrame.act, _root_.mul_assoc])

/-- Compatibility with evaluation at `1`: `(α ∘ r_δ)(1) = ι(σ δ) (α 1)`. -/
theorem LitFrame.act_α_one {T : Over S} (x : LitFrame A T) (δ : Y3OrderMod.G 5) :
    (x.act δ).α 1 = x.α 1 ≫ iotaO A (Y3OrderMod.σ δ) := by
  show x.α (1 * (δ : Y3OrderMod.OMod 5)) = _
  rw [← x.α_coe, Y3OrderMod.σ_spec, _root_.one_mul]

variable (A)

/-- The action of `δ` as an endomorphism of the presheaf `LitFrames5 A`. -/
def litAct (δ : Y3OrderMod.G 5) : LitFrames5 A ⟶ LitFrames5 A where
  app T := ↾fun x => LitFrame.act x δ
  naturality T T' f := by
    ext x
    rfl

/-- Two literal frames are related when they lie in one `H5`-orbit. -/
def LitOrbRel (T : (Over S)ᵒᵖ) (x x' : LitFrame A T.unop) : Prop :=
  ∃ δ ∈ H5, x' = x.act δ

/-- `T ↦ H\F_{A/S,5}(T)` for literal frames. -/
def LitOrbits5 : (Over S)ᵒᵖ ⥤ Type where
  obj T := Quot (LitOrbRel A T)
  map {T T'} f := ↾(Quot.map (fun x : LitFrame A T.unop => x.restrict f.unop) (by
    rintro x _ ⟨δ, hδ, rfl⟩
    exact ⟨δ, hδ, LitFrame.ext rfl⟩))
  map_id T := by
    ext q
    induction q using Quot.ind with
    | mk x => exact congrArg (Quot.mk _) (LitFrame.ext (funext fun q => Category.id_comp (x.α q)))
  map_comp f g := by
    ext q
    induction q using Quot.ind with
    | mk x =>
      exact congrArg (Quot.mk _) (LitFrame.ext (funext fun q => Category.assoc g.unop f.unop _))

/-- Evaluation at `1` carries the `H5`-orbit relation of literal frames to `OrbRel`. -/
theorem litOrbRel_iff (het : AlgebraicGeometry.Etale (A.iota ((5 : ℕ) : O))) (T : (Over S)ᵒᵖ)
    (x x' : LitFrame A T.unop) :
    LitOrbRel A T x x' ↔ OrbRel A T (evalEquiv A het T x) (evalEquiv A het T x') := by
  constructor
  · rintro ⟨δ, hδ, rfl⟩
    exact ⟨δ, hδ, x.act_α_one δ⟩
  · rintro ⟨δ, hδ, h⟩
    exact ⟨δ, hδ, (evalEquiv A het T).injective (Subtype.ext (h.trans (x.act_α_one δ).symm))⟩

/-- The orbit presheaves agree: `LitOrbits5 A ≅ Orbits5 A`, induced by evaluation at `1`. -/
def litOrbitsIso (het : AlgebraicGeometry.Etale (A.iota ((5 : ℕ) : O))) :
    LitOrbits5 A ≅ Orbits5 A :=
  NatIso.ofComponents (fun T => (Quot.congr (evalEquiv A het T) (litOrbRel_iff A het T)).toIso)
    (fun f => by
      ext q
      induction q using Quot.ind
      rfl)

theorem litOrbitsIso_hom_mk (het : AlgebraicGeometry.Etale (A.iota ((5 : ℕ) : O)))
    (T : (Over S)ᵒᵖ) (x : LitFrame A T.unop) :
    (litOrbitsIso A het).hom.app T (Quot.mk (LitOrbRel A T) x) =
      Quot.mk (OrbRel A T) ((litFramesIso A het).hom.app T x) := rfl

end Action

/-! ## 6. Under Milne, Prop. 20.7 at `n = 5` -/

section Milne

variable {S : Over Z30Base} (A : FEC S.left)

/-- Under `MilneProp207 5`, literal full level-5 structures are the frames of `Defs`. -/
def litFramesIsoMilne (hM : MilneProp207 5) : LitFrames5 A ≅ Frames5 A :=
  litFramesIso A (hM S A).2

/-- Under `MilneProp207 5`, the literal orbit presheaf is `Orbits5 A`. -/
def litOrbitsIsoMilne (hM : MilneProp207 5) : LitOrbits5 A ≅ Orbits5 A :=
  litOrbitsIso A (hM S A).2

end Milne

end Y3Buzzard.XDV15
