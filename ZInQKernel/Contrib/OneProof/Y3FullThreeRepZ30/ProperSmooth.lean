import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.Quotients
import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.SourceDescent
import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.SmoothDescent
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open LeafQM LeafQM.AV
open scoped CategoryTheory.Obj
namespace Y3Buzzard

/-!
# The quotient `Y` is proper and smooth of relative dimension 1 over `Z[1/30]` (draft)

1. A new leaf: the `M`-torsion of a false elliptic curve is represented by a closed subscheme,
   finite and etale over the base.
2. The level-5 locus `X5` is open in the frame scheme, so `X5 -> X1` is finite and etale, and the
   level-(5,3) base `X35` is proper and smooth of relative dimension 1 over the base.
3. The quotient `Y` is proper: universally closed and locally of finite type by descent along the
   quotient map, separated by descending the diagonal.
4. `Y` is smooth of relative dimension 1 by descent along the quotient map, assumed etale.

All leaves enter as hypotheses.
-/

attribute [local instance] FEC.grp

/-! ## 1. The torsion leaf -/

/-- Torsion leaf. For a false elliptic curve `A` over a `Z[1/30]`-scheme `S` and `M` invertible on
`S`, the `M`-torsion `A[M]` is represented by a closed subscheme of `A`, finite and etale over `S`:
a `T`-point `P` of `A` factors through it exactly when `P` is killed by `M`.
Source: J. S. Milne, *Abelian Varieties*, in G. Cornell and J. H. Silverman (eds.), *Arithmetic
Geometry*, Springer (1986), Section 20, Prop. 20.7: multiplication by `n` is finite and flat,
`A_n` is a finite flat group scheme of order `n^{2g}` over `S`, and it is etale if and only if
`n` is invertible on `S`. Here `g = 2` and `M = 5` is invertible on `Z[1/30]`; `A_n` is the
kernel of `n_A`, a closed subscheme because `A` is separated over `S`. -/
def TorsionRep (M : ℕ) : Prop :=
  ∀ (S : Over Z30Base) (A : FEC S.left),
    ∃ (W : Scheme.{0}) (j : W ⟶ A.F.left), IsClosedImmersion j ∧
      AlgebraicGeometry.IsFinite (j ≫ A.F.hom) ∧ AlgebraicGeometry.Etale (j ≫ A.F.hom) ∧
      ∀ (T : Scheme.{0}) (P : T ⟶ A.F.left),
        (∃ f : T ⟶ W, f ≫ j = P) ↔
          (letI := A.grp
           (Over.homMk (U := Over.mk (P ≫ A.F.hom)) P rfl : Over.mk (P ≫ A.F.hom) ⟶ A.F) ^ M = 1)

/-- Proper monomorphisms are closed immersions.
Source: The Stacks Project, Etale Morphisms of Schemes, Lemma 41.7.2, tag 04XV. -/
def ProperMonoIsClosedImmersion : Prop :=
  ∀ (X Y : Scheme.{0}) (f : X ⟶ Y), IsProper f → Mono f → IsClosedImmersion f

/-- The leaf above holds: it is Mathlib's `IsClosedImmersion.iff_isProper_and_mono`
(Stacks, tag 04XV). -/
theorem properMonoIsClosedImmersion : ProperMonoIsClosedImmersion :=
  fun _ _ f hp hm => (IsClosedImmersion.iff_isProper_and_mono f).2 ⟨hp, hm⟩

/-- The data of the torsion leaf at `(S, A)`. -/
structure TorsionData (M : ℕ) {S : Scheme.{0}} (A : FEC S) where
  W : Scheme.{0}
  j : W ⟶ A.F.left
  closed : IsClosedImmersion j
  fin : AlgebraicGeometry.IsFinite (j ≫ A.F.hom)
  etale : AlgebraicGeometry.Etale (j ≫ A.F.hom)
  char : ∀ (T : Scheme.{0}) (P : T ⟶ A.F.left), (∃ f : T ⟶ W, f ≫ j = P) ↔
    (Over.homMk (U := Over.mk (P ≫ A.F.hom)) P rfl : Over.mk (P ≫ A.F.hom) ⟶ A.F) ^ M = 1

/-- Choice of the data of the torsion leaf. -/
def TorsionData.ofLeaf {M : ℕ} (hT : TorsionRep M) (S : Over Z30Base) (A : FEC S.left) :
    TorsionData M A where
  W := Classical.choose (hT S A)
  j := Classical.choose (Classical.choose_spec (hT S A))
  closed := (Classical.choose_spec (Classical.choose_spec (hT S A))).1
  fin := (Classical.choose_spec (Classical.choose_spec (hT S A))).2.1
  etale := (Classical.choose_spec (Classical.choose_spec (hT S A))).2.2.1
  char := (Classical.choose_spec (Classical.choose_spec (hT S A))).2.2.2

/-! ## 2. Torsion is preserved by `ι a` and by pulling back a section -/

section Torsion

variable {S : Scheme.{0}} (A : FEC S)

/-- The identity of `T` between two objects of `Over S` with equal structure maps. -/
def overReindex {T : Scheme.{0}} {u v : T ⟶ S} (h : u = v) : Over.mk u ⟶ Over.mk v :=
  Over.homMk (𝟙 T) (by
    show 𝟙 T ≫ v = u
    rw [Category.id_comp]
    exact h.symm)

/-- The map `t` from an object of `Over S` with structure map equal to `t` to the unit. -/
def overToUnit {T : Scheme.{0}} (t : T ⟶ S) {u : T ⟶ S} (h : u = t) :
    Over.mk u ⟶ 𝟙_ (Over S) :=
  Over.homMk t (by
    show t ≫ 𝟙 S = u
    rw [Category.comp_id]
    exact h.symm)

theorem iota_reindex_eq {T : Scheme.{0}} (P : T ⟶ A.F.left) (a : O) :
    (P ≫ A.iota a) ≫ A.F.hom = P ≫ A.F.hom := by
  rw [Category.assoc, A.iota_over]

theorem homMk_comp_iota_eq {T : Scheme.{0}} (P : T ⟶ A.F.left) (a : O) :
    (Over.homMk (U := Over.mk ((P ≫ A.iota a) ≫ A.F.hom)) (P ≫ A.iota a) rfl :
        Over.mk ((P ≫ A.iota a) ≫ A.F.hom) ⟶ A.F) =
      overReindex (iota_reindex_eq A P a) ≫
        ((Over.homMk (U := Over.mk (P ≫ A.F.hom)) P rfl : Over.mk (P ≫ A.F.hom) ⟶ A.F) ≫
          (Over.homMk (A.iota a) (A.iota_over a) : A.F ⟶ A.F)) := by
  apply Over.OverMorphism.ext
  show P ≫ A.iota a = 𝟙 T ≫ P ≫ A.iota a
  rw [Category.id_comp]

/-- If `P` is killed by `n`, so is `ι(a) P`: `ι(a)` is a homomorphism. -/
theorem torsion_comp_iota_pt {T : Scheme.{0}} (P : T ⟶ A.F.left) (a : O) (n : ℕ)
    (hP : (Over.homMk (U := Over.mk (P ≫ A.F.hom)) P rfl : Over.mk (P ≫ A.F.hom) ⟶ A.F) ^ n = 1) :
    (Over.homMk (U := Over.mk ((P ≫ A.iota a) ≫ A.F.hom)) (P ≫ A.iota a) rfl :
        Over.mk ((P ≫ A.iota a) ≫ A.F.hom) ⟶ A.F) ^ n = 1 := by
  have e : (P ≫ A.iota a) ≫ A.F.hom = P ≫ A.F.hom := by rw [Category.assoc, A.iota_over]
  refine (homMk_pow_eq_one_congr A e (P ≫ A.iota a) rfl e n).2 ?_
  rw [homMk_mk_comp_iota A (P ≫ A.F.hom) P rfl a e]
  exact torsion_comp_iota A n _ hP a

theorem homMk_comp_section_eq {T : Scheme.{0}} (Q : S ⟶ A.F.left) (hQ : Q ≫ A.F.hom = 𝟙 S)
    (t : T ⟶ S) (h : (t ≫ Q) ≫ A.F.hom = t) :
    (Over.homMk (U := Over.mk ((t ≫ Q) ≫ A.F.hom)) (t ≫ Q) rfl :
        Over.mk ((t ≫ Q) ≫ A.F.hom) ⟶ A.F) =
      overToUnit t h ≫ (Over.homMk (U := 𝟙_ (Over S)) Q hQ : 𝟙_ (Over S) ⟶ A.F) :=
  Over.OverMorphism.ext rfl

/-- The pullback `t ≫ Q` of an `n`-torsion section `Q` is `n`-torsion. -/
theorem torsion_of_section {T : Scheme.{0}} (Q : S ⟶ A.F.left) (hQ : Q ≫ A.F.hom = 𝟙 S) (n : ℕ)
    (hord : (Over.homMk (U := 𝟙_ (Over S)) Q hQ : 𝟙_ (Over S) ⟶ A.F) ^ n = 1)
    (t : T ⟶ S) (P : T ⟶ A.F.left) (hP : P = t ≫ Q) :
    (Over.homMk (U := Over.mk (P ≫ A.F.hom)) P rfl : Over.mk (P ≫ A.F.hom) ⟶ A.F) ^ n = 1 := by
  subst hP
  have h : (t ≫ Q) ≫ A.F.hom = t := by
    rw [Category.assoc, hQ, Category.comp_id]
  rw [homMk_comp_section_eq A Q hQ t h, ← CategoryTheory.MonObj.comp_pow, hord]
  first
    | exact CategoryTheory.MonObj.comp_one _
    | simp

end Torsion

/-! ## 3. Equalizers through an unramified closed subscheme -/

/-- If two maps `f g : Z ⟶ V` factor through a monomorphism `j : W ⟶ V` as `f'` and `g'`, and
`f'`, `g'` agree over `S`, then the equalizer of `f` and `g` is the base change of the diagonal of
`W` over `S`. -/
theorem isPullback_equalizer_diagonal_of_factor {Z V W S : Scheme.{0}} (j : W ⟶ V) [Mono j]
    (π : W ⟶ S) (f g : Z ⟶ V) (f' g' : Z ⟶ W) (hf : f' ≫ j = f) (hg : g' ≫ j = g)
    (h : f' ≫ π = g' ≫ π) :
    IsPullback (equalizer.ι f g ≫ f') (equalizer.ι f g) (pullback.diagonal π)
      (pullback.lift f' g' h) := by
  have hcancel : ∀ {T : Scheme.{0}} (k : T ⟶ Z), k ≫ f' = k ≫ g' ↔ k ≫ f = k ≫ g := by
    intro T k
    rw [← hf, ← hg, ← Category.assoc, ← Category.assoc]
    exact (cancel_mono j).symm
  have hι : equalizer.ι f g ≫ f' = equalizer.ι f g ≫ g' :=
    (hcancel (equalizer.ι f g)).2 (equalizer.condition f g)
  have hw : (equalizer.ι f g ≫ f') ≫ pullback.diagonal π =
      equalizer.ι f g ≫ pullback.lift f' g' h := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.diagonal_fst, Category.comp_id, pullback.lift_fst]
    · simp only [Category.assoc, pullback.diagonal_snd, Category.comp_id, pullback.lift_snd]
      exact hι
  have key : ∀ s : PullbackCone (pullback.diagonal π) (pullback.lift f' g' h),
      s.snd ≫ f' = s.snd ≫ g' ∧ s.fst = s.snd ≫ f' := by
    intro s
    have h1 := congrArg (fun k => k ≫ pullback.fst π π) s.condition
    have h2 := congrArg (fun k => k ≫ pullback.snd π π) s.condition
    simp only [Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd, Category.comp_id,
      pullback.lift_fst, pullback.lift_snd] at h1 h2
    exact ⟨h1.symm.trans h2, h1⟩
  have hl := PullbackCone.IsLimit.mk hw
    (fun s => equalizer.lift s.snd ((hcancel s.snd).1 (key s).1))
    (fun s => by
      show equalizer.lift s.snd ((hcancel s.snd).1 (key s).1) ≫ equalizer.ι f g ≫ f' = s.fst
      rw [← Category.assoc, equalizer.lift_ι]
      exact (key s).2.symm)
    (fun s => by
      show equalizer.lift s.snd ((hcancel s.snd).1 (key s).1) ≫ equalizer.ι f g = s.snd
      exact equalizer.lift_ι _ _)
    (fun s m _ hm2 => by
      show m = equalizer.lift s.snd ((hcancel s.snd).1 (key s).1)
      apply equalizer.hom_ext
      rw [equalizer.lift_ι]
      exact hm2)
  exact IsPullback.of_isLimit hl

/-- The level-5 locus is open in the frame scheme: both equalized maps land in the 5-torsion,
which is etale over `X1`, so its diagonal is an open immersion. -/
theorem isOpenImmersion_M5Incl {X₁ : Over Z30Base} {A₁ : FEC X₁.left} (α₁ : V15 A₁)
    {Z : Scheme.{0}} (i : Z ⟶ A₁.F.left) (hchar : FrameChar 5 A₁ i) (D : TorsionData 5 A₁) :
    IsOpenImmersion (M5Incl α₁ i) := by
  have hi : (Over.homMk (U := Over.mk (i ≫ A₁.F.hom)) i rfl :
      Over.mk (i ≫ A₁.F.hom) ⟶ A₁.F) ^ 5 = 1 := by
    obtain ⟨h1, -⟩ := (hchar Z i).1 ⟨𝟙 Z, Category.id_comp i⟩
    exact h1
  obtain ⟨f', hf'⟩ := (D.char Z (i ≫ A₁.iota (1 - e5))).2 (torsion_comp_iota_pt A₁ i (1 - e5) 5 hi)
  obtain ⟨g', hg'⟩ := (D.char Z (i ≫ A₁.F.hom ≫ α₁.Q)).2
    (torsion_of_section A₁ α₁.Q α₁.Q_sec 5 α₁.order (i ≫ A₁.F.hom) (i ≫ A₁.F.hom ≫ α₁.Q)
      (Category.assoc _ _ _).symm)
  have h : f' ≫ D.j ≫ A₁.F.hom = g' ≫ D.j ≫ A₁.F.hom := by
    rw [reassoc_of% hf', reassoc_of% hg']
    simp only [Category.assoc, A₁.iota_over, α₁.Q_sec, Category.comp_id]
  haveI := D.closed
  haveI := D.fin
  haveI := D.etale
  haveI : Mono D.j := by
    first
      | exact inferInstance
      | exact IsPreimmersion.instMonoScheme _
      | exact AlgebraicGeometry.IsPreimmersion.instMonoScheme _
  haveI hdiag : IsOpenImmersion (pullback.diagonal (D.j ≫ A₁.F.hom)) := by
    first
      | exact AlgebraicGeometry.FormallyUnramified.isOpenImmersion_diagonal (D.j ≫ A₁.F.hom)
      | infer_instance
  exact MorphismProperty.of_isPullback (P := @IsOpenImmersion)
    (isPullback_equalizer_diagonal_of_factor D.j (D.j ≫ A₁.F.hom) _ _ f' g' hf' hg' h) hdiag

/-! ## 4. The tower `X35 -> X5 -> X1 -> Spec Z[1/30]` -/

section Tower

variable {X₁ : Over Z30Base} {A₁ : FEC X₁.left} (α₁ : V15 A₁) {Z : Scheme.{0}}
  (i : Z ⟶ A₁.F.left)

theorem isFinite_M5Base (hfin : AlgebraicGeometry.IsFinite (i ≫ A₁.F.hom)) :
    AlgebraicGeometry.IsFinite (M5Base α₁ i) := by
  haveI := hfin
  haveI := isClosedImmersion_M5Incl α₁ i
  rw [M5Base_eq]
  first
    | infer_instance
    | exact MorphismProperty.comp_mem (@AlgebraicGeometry.IsFinite) _ _ inferInstance inferInstance

theorem etale_M5Base (hchar : FrameChar 5 A₁ i) (D : TorsionData 5 A₁)
    (het : AlgebraicGeometry.Etale (i ≫ A₁.F.hom)) : AlgebraicGeometry.Etale (M5Base α₁ i) := by
  haveI := het
  haveI := isOpenImmersion_M5Incl α₁ i hchar D
  rw [M5Base_eq]
  first
    | infer_instance
    | exact MorphismProperty.comp_mem (@AlgebraicGeometry.Etale) _ _ inferInstance inferInstance

end Tower

theorem b1_proper (hB1 : BuzzardThm21Cor23V15') : IsProper (leafD hB1).X.hom :=
  (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec hB1))).1

theorem b1_smooth (hB1 : BuzzardThm21Cor23V15') :
    SmoothOfRelativeDimension 1 (leafD hB1).X.hom :=
  (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec hB1))).2.1

theorem frameData_isEtale {M : ℕ} (hB2 : BuzzardFrameRepTorsor M) (S : Over Z30Base)
    (A : FEC S.left) : AlgebraicGeometry.Etale ((FrameData.ofLeaf hB2 S A).i ≫ A.F.hom) :=
  (Classical.choose_spec (Classical.choose_spec (hB2 S A))).2.2.1

theorem frameRep_isEtale {M : ℕ} (hB2 : BuzzardFrameRep M) (S : Over Z30Base)
    (A : FEC S.left) : AlgebraicGeometry.Etale ((FrameData.ofRep hB2 S A).i ≫ A.F.hom) :=
  (Classical.choose_spec (Classical.choose_spec (hB2 S A))).2.2.1

theorem frameRepNS_isEtale {M : ℕ} (hB2 : BuzzardFrameRepNS M) (S : Over Z30Base)
    (A : FEC S.left) : AlgebraicGeometry.Etale ((FrameData.ofRepNS hB2 S A).i ≫ A.F.hom) :=
  (Classical.choose_spec (Classical.choose_spec (hB2 S A))).2.2.1

section Leaves

variable (hB1 : BuzzardThm21Cor23V15') (hB25 : BuzzardFrameRepTorsor 5)
  (hB23 : BuzzardFrameRepNS 3)

theorem moduli5_X_hom : (moduli5 hB1 hB25).X.hom =
    M5Base (leafD hB1).α (leafF5 hB1 hB25).i ≫ (leafD hB1).X.hom := rfl

theorem moduli35_X_hom : (moduli35 (moduli5 hB1 hB25) hB23).X.hom =
    ((leafF3 hB1 hB25 hB23).i ≫ (moduli5 hB1 hB25).A.F.hom) ≫ (moduli5 hB1 hB25).X.hom := rfl

/-- `X5 -> X1` is finite and etale. -/
theorem moduli5_base_finite_etale (hT5 : TorsionRep 5) :
    AlgebraicGeometry.IsFinite (M5Base (leafD hB1).α (leafF5 hB1 hB25).i) ∧
      AlgebraicGeometry.Etale (M5Base (leafD hB1).α (leafF5 hB1 hB25).i) :=
  ⟨isFinite_M5Base _ _ (frameData_isFinite hB25 (leafD hB1).X (leafD hB1).A),
    etale_M5Base _ _ (leafF5 hB1 hB25).char (TorsionData.ofLeaf hT5 (leafD hB1).X (leafD hB1).A)
      (frameData_isEtale hB25 (leafD hB1).X (leafD hB1).A)⟩

/-- `X35` is proper over the base: finite over finite over the proper `X1`. -/
theorem isProper_X35 : IsProper (moduli35 (moduli5 hB1 hB25) hB23).X.hom := by
  haveI h3 : AlgebraicGeometry.IsFinite ((leafF3 hB1 hB25 hB23).i ≫ (moduli5 hB1 hB25).A.F.hom) :=
    frameRepNS_isFinite hB23 (moduli5 hB1 hB25).X (moduli5 hB1 hB25).A
  haveI h5 : AlgebraicGeometry.IsFinite (M5Base (leafD hB1).α (leafF5 hB1 hB25).i) :=
    isFinite_M5Base _ _ (frameData_isFinite hB25 (leafD hB1).X (leafD hB1).A)
  haveI h1 : IsProper (leafD hB1).X.hom := b1_proper hB1
  have p5 : IsProper (M5Base (leafD hB1).α (leafF5 hB1 hB25).i) := by
    first
      | infer_instance
      | exact (AlgebraicGeometry.IsFinite.iff_isProper_and_isAffineHom.mp h5).1
  have p3 : IsProper ((leafF3 hB1 hB25 hB23).i ≫ (moduli5 hB1 hB25).A.F.hom) := by
    first
      | infer_instance
      | exact (AlgebraicGeometry.IsFinite.iff_isProper_and_isAffineHom.mp h3).1
  have h51 : IsProper (M5Base (leafD hB1).α (leafF5 hB1 hB25).i ≫ (leafD hB1).X.hom) :=
    MorphismProperty.comp_mem (@IsProper) _ _ p5 h1
  show IsProper (((leafF3 hB1 hB25 hB23).i ≫ (moduli5 hB1 hB25).A.F.hom) ≫
    (M5Base (leafD hB1).α (leafF5 hB1 hB25).i ≫ (leafD hB1).X.hom))
  exact MorphismProperty.comp_mem (@IsProper) _ _ p3 h51

/-- `X35` is smooth of relative dimension 1 over the base: etale over etale over `X1`. -/
theorem smooth_X35 (hT5 : TorsionRep 5) :
    SmoothOfRelativeDimension 1 (moduli35 (moduli5 hB1 hB25) hB23).X.hom := by
  haveI h3 : AlgebraicGeometry.Etale ((leafF3 hB1 hB25 hB23).i ≫ (moduli5 hB1 hB25).A.F.hom) :=
    frameRepNS_isEtale hB23 (moduli5 hB1 hB25).X (moduli5 hB1 hB25).A
  haveI h5 : AlgebraicGeometry.Etale (M5Base (leafD hB1).α (leafF5 hB1 hB25).i) :=
    (moduli5_base_finite_etale hB1 hB25 hT5).2
  haveI h1 : SmoothOfRelativeDimension 1 (leafD hB1).X.hom := b1_smooth hB1
  haveI s3 : SmoothOfRelativeDimension 0
      ((leafF3 hB1 hB25 hB23).i ≫ (moduli5 hB1 hB25).A.F.hom) := by
    first
      | infer_instance
      | exact (AlgebraicGeometry.Etale.iff_smoothOfRelativeDimension_zero _).1 h3
  haveI s5 : SmoothOfRelativeDimension 0 (M5Base (leafD hB1).α (leafF5 hB1 hB25).i) := by
    first
      | infer_instance
      | exact (AlgebraicGeometry.Etale.iff_smoothOfRelativeDimension_zero _).1 h5
  have s51 : SmoothOfRelativeDimension (0 + 1)
      (M5Base (leafD hB1).α (leafF5 hB1 hB25).i ≫ (leafD hB1).X.hom) :=
    smoothOfRelativeDimension_comp (hf := s5) (hg := h1) 0 1 _ _
  have s : SmoothOfRelativeDimension (0 + (0 + 1))
      (((leafF3 hB1 hB25 hB23).i ≫ (moduli5 hB1 hB25).A.F.hom) ≫
        (M5Base (leafD hB1).α (leafF5 hB1 hB25).i ≫ (leafD hB1).X.hom)) :=
    smoothOfRelativeDimension_comp (hf := s3) (hg := s51) 0 (0 + 1) _ _
  show SmoothOfRelativeDimension 1 (((leafF3 hB1 hB25 hB23).i ≫ (moduli5 hB1 hB25).A.F.hom) ≫
    (M5Base (leafD hB1).α (leafF5 hB1 hB25).i ≫ (leafD hB1).X.hom))
  first
    | exact s
    | simpa using s

end Leaves

/-! ## 5. The quotient is proper -/

section YProper

variable {M : Moduli35} (Q : QuotientData M)

theorem universallyClosed_sY (hX : IsProper M.X.hom) : UniversallyClosed Q.sY := by
  haveI := hX
  refine descentUniversallyClosed _ _ _ Q.qX Q.sY Q.surjX ?_
  rw [Q.hsY]
  infer_instance

theorem locallyOfFiniteType_sY (hX : IsProper M.X.hom) :
    LocallyOfFiniteType Q.sY := by
  haveI := hX
  haveI hZ30 : IsNoetherianRing Y3RouteA.Z30 := by
    first
      | exact inferInstance
      | exact IsLocalization.isNoetherianRing (Submonoid.powers (30 : ℤ)) Y3RouteA.Z30
          inferInstance
  haveI hZ : IsLocallyNoetherian Z30Base := by
    first
      | exact inferInstance
      | (unfold Z30Base; infer_instance)
  refine Y3Buzzard.SourceDescent.descentLocallyOfFiniteTypeFinite _ _ _ Q.qX Q.sY hZ Q.finX
    Q.flatX Q.surjX ?_
  rw [Q.hsY]
  infer_instance

/-- Quasi-compactness of `Y`: universally closed morphisms are quasi-compact in Mathlib. -/
theorem quasiCompact_sY (hX : IsProper M.X.hom) : QuasiCompact Q.sY := by
  haveI := universallyClosed_sY Q hX
  infer_instance

/-- Surjective morphisms are stable under composition. -/
instance instIsStableUnderCompositionSurjective :
    MorphismProperty.IsStableUnderComposition @AlgebraicGeometry.Surjective := by
  first
    | infer_instance
    | exact ⟨fun f g hf hg => ⟨hg.1.comp hf.1⟩⟩

/-- The map `X ×_S X ⟶ Y ×_S Y`. -/
def gXY : pullback (Q.qX ≫ Q.sY) (Q.qX ≫ Q.sY) ⟶ pullback Q.sY Q.sY :=
  pullback.map (Q.qX ≫ Q.sY) (Q.qX ≫ Q.sY) Q.sY Q.sY Q.qX Q.qX (𝟙 _)
    (Category.comp_id _) (Category.comp_id _)

/-- The map `X ×_Y X ⟶ X ×_S X`. -/
def kpLift : pullback Q.qX Q.qX ⟶ pullback (Q.qX ≫ Q.sY) (Q.qX ≫ Q.sY) :=
  pullback.lift (pullback.fst Q.qX Q.qX) (pullback.snd Q.qX Q.qX)
    (by rw [← Category.assoc, ← Category.assoc, pullback.condition])

theorem flat_gXY : AlgebraicGeometry.Flat (gXY Q) :=
  MorphismProperty.pullbackMap (P := @AlgebraicGeometry.Flat) Q.flatX Q.flatX rfl rfl

theorem surjective_gXY : AlgebraicGeometry.Surjective (gXY Q) :=
  MorphismProperty.pullbackMap (P := @AlgebraicGeometry.Surjective) Q.surjX Q.surjX rfl rfl

theorem lfp_gXY : LocallyOfFinitePresentation (gXY Q) :=
  MorphismProperty.pullbackMap (P := @LocallyOfFinitePresentation) Q.lfpX Q.lfpX rfl rfl

theorem gXY_fst : gXY Q ≫ pullback.fst Q.sY Q.sY = pullback.fst _ _ ≫ Q.qX := by
  simp only [gXY, pullback.map, pullback.lift_fst]

theorem gXY_snd : gXY Q ≫ pullback.snd Q.sY Q.sY = pullback.snd _ _ ≫ Q.qX := by
  simp only [gXY, pullback.map, pullback.lift_snd]

theorem kpLift_fst : kpLift Q ≫ pullback.fst _ _ = pullback.fst Q.qX Q.qX :=
  pullback.lift_fst _ _ _

theorem kpLift_snd : kpLift Q ≫ pullback.snd _ _ = pullback.snd Q.qX Q.qX :=
  pullback.lift_snd _ _ _

/-- The diagonal of `Y` base-changes along `X ×_S X ⟶ Y ×_S Y` to `X ×_Y X ⟶ X ×_S X`. -/
theorem isPullback_diagonal_gXY :
    IsPullback (pullback.fst Q.qX Q.qX ≫ Q.qX) (kpLift Q) (pullback.diagonal Q.sY) (gXY Q) := by
  have hw : (pullback.fst Q.qX Q.qX ≫ Q.qX) ≫ pullback.diagonal Q.sY = kpLift Q ≫ gXY Q := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, pullback.diagonal_fst, Category.comp_id,
        Category.assoc, gXY_fst, reassoc_of% (kpLift_fst Q)]
    · rw [Category.assoc, Category.assoc, pullback.diagonal_snd, Category.comp_id,
        Category.assoc, gXY_snd, reassoc_of% (kpLift_snd Q)]
      exact pullback.condition
  have key : ∀ s : PullbackCone (pullback.diagonal Q.sY) (gXY Q),
      (s.snd ≫ pullback.fst _ _) ≫ Q.qX = s.fst ∧ (s.snd ≫ pullback.snd _ _) ≫ Q.qX = s.fst := by
    intro s
    have h1 := congrArg (fun k => k ≫ pullback.fst Q.sY Q.sY) s.condition
    have h2 := congrArg (fun k => k ≫ pullback.snd Q.sY Q.sY) s.condition
    simp only [Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd, Category.comp_id,
      gXY_fst, gXY_snd] at h1 h2
    exact ⟨by rw [Category.assoc]; exact h1.symm, by rw [Category.assoc]; exact h2.symm⟩
  have hl := PullbackCone.IsLimit.mk hw
    (fun s => pullback.lift (s.snd ≫ pullback.fst _ _) (s.snd ≫ pullback.snd _ _)
      ((key s).1.trans (key s).2.symm))
    (fun s => by
      show pullback.lift (s.snd ≫ pullback.fst _ _) (s.snd ≫ pullback.snd _ _)
          ((key s).1.trans (key s).2.symm) ≫ pullback.fst Q.qX Q.qX ≫ Q.qX = s.fst
      rw [pullback.lift_fst_assoc]
      exact (key s).1)
    (fun s => by
      show pullback.lift (s.snd ≫ pullback.fst _ _) (s.snd ≫ pullback.snd _ _)
          ((key s).1.trans (key s).2.symm) ≫ kpLift Q = s.snd
      apply pullback.hom_ext
      · rw [Category.assoc, kpLift_fst, pullback.lift_fst]
      · rw [Category.assoc, kpLift_snd, pullback.lift_snd])
    (fun s m _ hm2 => by
      show m = pullback.lift (s.snd ≫ pullback.fst _ _) (s.snd ≫ pullback.snd _ _)
          ((key s).1.trans (key s).2.symm)
      apply pullback.hom_ext
      · rw [pullback.lift_fst, ← hm2, Category.assoc, kpLift_fst]
      · rw [pullback.lift_snd, ← hm2, Category.assoc, kpLift_snd])
  exact IsPullback.of_isLimit hl

theorem mono_kpLift : Mono (kpLift Q) := by
  constructor
  intro T a b hab
  apply pullback.hom_ext
  · have := congrArg (fun k => k ≫ pullback.fst (Q.qX ≫ Q.sY) (Q.qX ≫ Q.sY)) hab
    simpa only [Category.assoc, kpLift_fst] using this
  · have := congrArg (fun k => k ≫ pullback.snd (Q.qX ≫ Q.sY) (Q.qX ≫ Q.sY)) hab
    simpa only [Category.assoc, kpLift_snd] using this

/-- `X ×_Y X ⟶ X ×_S X` is proper: its composite with the separated projection to `X` is the
base change of the finite map `qX`. -/
theorem isProper_kpLift (hX : IsProper M.X.hom) : IsProper (kpLift Q) := by
  haveI : IsProper (Q.qX ≫ Q.sY) := by
    rw [Q.hsY]
    exact hX
  haveI := Q.finX
  haveI : AlgebraicGeometry.IsSeparated (pullback.snd (Q.qX ≫ Q.sY) (Q.qX ≫ Q.sY)) :=
    MorphismProperty.of_isPullback (P := @AlgebraicGeometry.IsSeparated)
      (IsPullback.of_hasPullback (Q.qX ≫ Q.sY) (Q.qX ≫ Q.sY)) inferInstance
  haveI : AlgebraicGeometry.IsFinite (pullback.snd Q.qX Q.qX) :=
    MorphismProperty.of_isPullback (P := @AlgebraicGeometry.IsFinite)
      (IsPullback.of_hasPullback Q.qX Q.qX) Q.finX
  haveI : IsProper (kpLift Q ≫ pullback.snd (Q.qX ≫ Q.sY) (Q.qX ≫ Q.sY)) := by
    rw [kpLift_snd]
    infer_instance
  exact IsProper.of_comp (kpLift Q) (pullback.snd (Q.qX ≫ Q.sY) (Q.qX ≫ Q.sY))

theorem isSeparated_sY (hPM : ProperMonoIsClosedImmersion) (hCI : DescentClosedImmersion)
    (hX : IsProper M.X.hom) : AlgebraicGeometry.IsSeparated Q.sY := by
  have hι : IsClosedImmersion (kpLift Q) :=
    hPM _ _ (kpLift Q) (isProper_kpLift Q hX) (mono_kpLift Q)
  have hpb := isPullback_diagonal_gXY Q
  have hsnd : IsClosedImmersion (pullback.snd (pullback.diagonal Q.sY) (gXY Q)) := by
    rw [← hpb.isoPullback_inv_snd]
    haveI := hι
    first
      | infer_instance
      | exact MorphismProperty.comp_mem (@IsClosedImmersion) _ _ inferInstance hι
  have hdiag : IsClosedImmersion (pullback.diagonal Q.sY) :=
    hCI _ _ _ (pullback.diagonal Q.sY) (gXY Q) (flat_gXY Q) (surjective_gXY Q) (lfp_gXY Q) hsnd
  first
    | exact ⟨hdiag⟩
    | exact { isClosedImmersion_diagonal := hdiag }

/-- `Y` is proper over the base. -/
theorem isProper_sY (hPM : ProperMonoIsClosedImmersion)
    (hCI : DescentClosedImmersion) (hX : IsProper M.X.hom) : IsProper Q.sY :=
  (isProper_iff Q.sY).2
    ⟨isSeparated_sY Q hPM hCI hX, universallyClosed_sY Q hX, locallyOfFiniteType_sY Q hX⟩

/-! ## 6. The quotient is smooth of relative dimension 1 -/

theorem smooth_sY (hB7b : SourceDescent.DescentSmoothRelDimFiniteEtale)
    (hEt : AlgebraicGeometry.Etale Q.qX) (hXs : SmoothOfRelativeDimension 1 M.X.hom) :
    SmoothOfRelativeDimension 1 Q.sY := by
  haveI hZ30 : IsNoetherianRing Y3RouteA.Z30 := by
    first
      | exact inferInstance
      | exact IsLocalization.isNoetherianRing (Submonoid.powers (30 : ℤ)) Y3RouteA.Z30
          inferInstance
  have hZ : IsLocallyNoetherian Z30Base := by
    first
      | exact inferInstance
      | (unfold Z30Base; infer_instance)
  refine hB7b 1 _ _ _ Q.qX Q.sY hZ Q.finX hEt Q.surjX ?_
  rw [Q.hsY]
  exact hXs

/-- Proper and smooth of relative dimension 1, for any quotient datum of a proper smooth base. -/
theorem YOver_proper_smooth
    (hPM : ProperMonoIsClosedImmersion) (hCI : DescentClosedImmersion)
    (hB7b : SourceDescent.DescentSmoothRelDimFiniteEtale) (hEt : AlgebraicGeometry.Etale Q.qX)
    (hX : IsProper M.X.hom) (hXs : SmoothOfRelativeDimension 1 M.X.hom) :
    IsProper Q.YOver.hom ∧ SmoothOfRelativeDimension 1 Q.YOver.hom :=
  ⟨show IsProper Q.sY from isProper_sY Q hPM hCI hX,
    show SmoothOfRelativeDimension 1 Q.sY from smooth_sY Q hB7b hEt hXs⟩

end YProper

/-! ## 7. The goal from the leaves -/

/-- G8. The quotient `Y` of the level-(5,3) moduli scheme by `G 5` is proper and smooth of
relative dimension 1 over `Z[1/30]`, for any quotient datum. The etaleness of the quotient map
enters as the hypothesis `hEt` (finite, flat, finitely presented, and unramified since the action
is free). -/
theorem Y_proper_smooth_of (hB1 : BuzzardThm21Cor23V15') (hB25 : BuzzardFrameRepTorsor 5)
    (hB23 : BuzzardFrameRepNS 3) (hT5 : TorsionRep 5)
    (hB7b : SourceDescent.DescentSmoothRelDimFiniteEtale)
    (hCI : DescentClosedImmersion) (hPM : ProperMonoIsClosedImmersion)
    (Q : QuotientData (moduli35 (moduli5 hB1 hB25) hB23)) (hEt : AlgebraicGeometry.Etale Q.qX) :
    IsProper Q.YOver.hom ∧ SmoothOfRelativeDimension 1 Q.YOver.hom :=
  YOver_proper_smooth Q hPM hCI hB7b hEt (isProper_X35 hB1 hB25 hB23)
    (smooth_X35 hB1 hB25 hB23 hT5)

/-- G8 for the quotient datum built from the leaves. -/
theorem Y_proper_smooth (hB1 : BuzzardThm21Cor23V15') (hB25 : BuzzardFrameRepTorsor 5)
    (hB23 : BuzzardFrameRepNS 3) (hB3 : SerreRigidityLevel3') (hBC : FECGeomFibre)
    (hB6 : ProjectiveFEC) (hT5 : TorsionRep 5)
    (hB7b : SourceDescent.DescentSmoothRelDimFiniteEtale)
    (hCI : DescentClosedImmersion) (hPM : ProperMonoIsClosedImmersion)
    (hEt : AlgebraicGeometry.Etale (quotientDataOfLeaves hB1 hB25 hB23 hB3 hBC hB6).qX) :
    IsProper (quotientDataOfLeaves hB1 hB25 hB23 hB3 hBC hB6).YOver.hom ∧
      SmoothOfRelativeDimension 1 (quotientDataOfLeaves hB1 hB25 hB23 hB3 hBC hB6).YOver.hom :=
  Y_proper_smooth_of hB1 hB25 hB23 hT5 hB7b hCI hPM _ hEt

end Y3Buzzard
