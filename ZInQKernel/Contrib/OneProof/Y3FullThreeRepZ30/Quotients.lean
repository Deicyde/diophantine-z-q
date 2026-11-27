import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.FrameAction
import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.QuotientInputs
import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.QuotientDescent
import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.ProjFiniteSets
import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.IntegralTorsorPullback
noncomputable section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open LeafQM LeafQM.AV
open scoped CategoryTheory.Obj
namespace Y3Buzzard

/-!
# Quotients of the level-(5,3) moduli datum by `G 5` (draft)

1. A closed immersion into `PN N` gives `FiniteSetsInAffines`.
2. The equalizer of two maps over a separated base is a closed immersion.
3. `FiniteSetsInAffines` for the base `X35` and the total space `A35`.
4. Quotients of both by the free actions `ρ` and `ρA`.
5. The descended structure map `b` and the cartesian square `IsPullback qA p b qX`.
6. The bundle `QuotientData`, with the quotient base as an object over `Z30Base`.

All leaves enter as hypotheses. The cartesian square is obtained from the categorical
kernel-pair lemma of the torsor file, whose relation objects are arbitrary; the quotient
kernel pairs live on `∐ (_ : G), X`, and the square on the second projections is proved
from finitary extensivity.
-/

open Y3QuotientDescent (FiniteSetsInAffines)

instance instFiniteG5 : Finite (Y3OrderMod.G 5) := Y3OrderMod.finite_G 5 (by norm_num)

/-! ## 1. Projective space -/

theorem finiteSetsInAffines_PNZ (N : ℕ) : FiniteSetsInAffines (PNZ N) :=
  fun F hF => Y3ProjFiniteSets.exists_isAffineOpen_superset_of_finite (PNGradingZ N) F hF

/-- `PN N` maps affinely to `PNZ N`: the map is a base change of the morphism of affine schemes
`Spec Z[1/30] ⟶ Spec Z`. -/
instance isAffineHom_toPNZ (N : ℕ) : IsAffineHom (toPNZ N) := by
  unfold toPNZ
  first
    | infer_instance
    | exact MorphismProperty.of_isPullback (P := @IsAffineHom)
        (IsPullback.of_hasPullback _ _).flip inferInstance
    | exact MorphismProperty.pullback_fst (P := @IsAffineHom) _ _ inferInstance

theorem finiteSetsInAffines_PN (N : ℕ) : FiniteSetsInAffines (PN N) :=
  Y3QuotientDescent.finiteSetsInAffines_of_isAffineHom (toPNZ N) (finiteSetsInAffines_PNZ N)

/-- A closed immersion into `PN N` gives `FiniteSetsInAffines`: closed immersions are affine. -/
theorem finiteSetsInAffines_of_closedImmersion_PN {X : Scheme.{0}} {N : ℕ} (i : X ⟶ PN N)
    [IsClosedImmersion i] : FiniteSetsInAffines X :=
  Y3QuotientDescent.finiteSetsInAffines_of_isAffineHom i (finiteSetsInAffines_PN N)

/-! ## 2. Equalizers over a separated base -/

theorem isPullback_equalizer_diagonal {Z W S : Scheme.{0}} (π : W ⟶ S) (f g : Z ⟶ W)
    (h : f ≫ π = g ≫ π) :
    IsPullback (equalizer.ι f g ≫ f) (equalizer.ι f g) (pullback.diagonal π)
      (pullback.lift f g h) := by
  have hw : (equalizer.ι f g ≫ f) ≫ pullback.diagonal π =
      equalizer.ι f g ≫ pullback.lift f g h := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.diagonal_fst, Category.comp_id, pullback.lift_fst]
    · simp only [Category.assoc, pullback.diagonal_snd, Category.comp_id, pullback.lift_snd]
      exact equalizer.condition f g
  have key : ∀ s : PullbackCone (pullback.diagonal π) (pullback.lift f g h),
      s.snd ≫ f = s.snd ≫ g ∧ s.fst = s.snd ≫ f := by
    intro s
    have h1 := congrArg (fun k => k ≫ pullback.fst π π) s.condition
    have h2 := congrArg (fun k => k ≫ pullback.snd π π) s.condition
    simp only [Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd, Category.comp_id,
      pullback.lift_fst, pullback.lift_snd] at h1 h2
    exact ⟨h1.symm.trans h2, h1⟩
  have hl := PullbackCone.IsLimit.mk hw (fun s => equalizer.lift s.snd (key s).1)
    (fun s => by
      show equalizer.lift s.snd (key s).1 ≫ equalizer.ι f g ≫ f = s.fst
      rw [← Category.assoc, equalizer.lift_ι]
      exact (key s).2.symm)
    (fun s => by
      show equalizer.lift s.snd (key s).1 ≫ equalizer.ι f g = s.snd
      exact equalizer.lift_ι _ _)
    (fun s m _ hm2 => by
      show m = equalizer.lift s.snd (key s).1
      apply equalizer.hom_ext
      rw [equalizer.lift_ι]
      exact hm2)
  exact IsPullback.of_isLimit hl

/-- The equalizer of two maps over `S` into a scheme separated over `S` is a closed
immersion: it is the base change of the relative diagonal. -/
theorem isClosedImmersion_equalizer_ι {Z W S : Scheme.{0}} (π : W ⟶ S)
    [AlgebraicGeometry.IsSeparated π] (f g : Z ⟶ W) (h : f ≫ π = g ≫ π) :
    IsClosedImmersion (equalizer.ι f g) :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion) (isPullback_equalizer_diagonal π f g h)
    (AlgebraicGeometry.IsSeparated.isClosedImmersion_diagonal (f := π))

/-- A proper structure map is separated. -/
theorem FEC.isSeparated_hom {S : Scheme.{0}} (A : FEC S) : AlgebraicGeometry.IsSeparated A.F.hom := by
  haveI := A.proper
  infer_instance

theorem isClosedImmersion_M5Incl {X₁ : Over Z30Base} {A₁ : FEC X₁.left} (α₁ : V15 A₁)
    {Z : Scheme.{0}} (i : Z ⟶ A₁.F.left) : IsClosedImmersion (M5Incl α₁ i) := by
  haveI := FEC.isSeparated_hom A₁
  exact isClosedImmersion_equalizer_ι A₁.F.hom _ _
    (by simp only [Category.assoc, A₁.iota_over, α₁.Q_sec, Category.comp_id])

/-! ## 3. Finite sets in affines along the tower -/

theorem isAffineHom_pullbackFst {S S' : Scheme.{0}} (A : FEC S) (g : S' ⟶ S)
    [AlgebraicGeometry.IsAffineHom g] : AlgebraicGeometry.IsAffineHom (A.pullbackFst g) := by
  haveI := AlgebraicGeometry.isAffineHom_isStableUnderBaseChange
  exact MorphismProperty.of_isPullback (P := @AlgebraicGeometry.IsAffineHom)
    (A.pullback_isPullback g).flip ‹AlgebraicGeometry.IsAffineHom g›

theorem isAffineHom_M5Base {X₁ : Over Z30Base} {A₁ : FEC X₁.left} (α₁ : V15 A₁)
    {Z : Scheme.{0}} (i : Z ⟶ A₁.F.left) (hfin : AlgebraicGeometry.IsFinite (i ≫ A₁.F.hom)) :
    AlgebraicGeometry.IsAffineHom (M5Base α₁ i) := by
  haveI := hfin
  haveI := isClosedImmersion_M5Incl α₁ i
  rw [M5Base_eq]
  first
    | infer_instance
    | exact MorphismProperty.comp_mem (@AlgebraicGeometry.IsAffineHom) _ _ inferInstance
        inferInstance

/-- The level-5 base `X5 ⟶ X1` is affine (closed immersion followed by a finite map). -/
theorem fsa_moduli5Of_X (X₁ : Over Z30Base) (A₁ : FEC X₁.left) (α₁ : V15 A₁)
    (hex : B1Exists α₁) (hun : B1Unique α₁) (Z : Scheme.{0}) (i : Z ⟶ A₁.F.left)
    (hmono : Mono i) (hchar : FrameChar 5 A₁ i) (hfin : AlgebraicGeometry.IsFinite (i ≫ A₁.F.hom))
    (hX : FiniteSetsInAffines X₁.left) : FiniteSetsInAffines
    (moduli5Of X₁ A₁ α₁ hex hun Z i hmono hchar).X.left := by
  haveI := hfin
  haveI := isClosedImmersion_M5Incl α₁ i
  have h1 : FiniteSetsInAffines (M5Locus α₁ i) :=
    Y3QuotientDescent.finiteSetsInAffines_of_isAffineHom (X := M5Locus α₁ i) (M5Incl α₁ i)
      (Y3QuotientDescent.finiteSetsInAffines_of_isAffineHom (X := Z) (i ≫ A₁.F.hom) hX)
  exact h1

theorem fsa_moduli5Of_A (X₁ : Over Z30Base) (A₁ : FEC X₁.left) (α₁ : V15 A₁)
    (hex : B1Exists α₁) (hun : B1Unique α₁) (Z : Scheme.{0}) (i : Z ⟶ A₁.F.left)
    (hmono : Mono i) (hchar : FrameChar 5 A₁ i) (hfin : AlgebraicGeometry.IsFinite (i ≫ A₁.F.hom))
    (hA : FiniteSetsInAffines A₁.F.left) : FiniteSetsInAffines
    (moduli5Of X₁ A₁ α₁ hex hun Z i hmono hchar).A.F.left := by
  haveI := isAffineHom_M5Base α₁ i hfin
  haveI := isAffineHom_pullbackFst A₁ (M5Base α₁ i)
  have h1 : FiniteSetsInAffines (A₁.pullback (M5Base α₁ i)).F.left :=
    Y3QuotientDescent.finiteSetsInAffines_of_isAffineHom
      (X := (A₁.pullback (M5Base α₁ i)).F.left) (A₁.pullbackFst (M5Base α₁ i)) hA
  exact h1

theorem fsa_moduli35Of_X (M5 : Moduli5) {Z₃ : Scheme.{0}} (i₃ : Z₃ ⟶ M5.A.F.left)
    (hmono : Mono i₃) (hchar : FrameChar 3 M5.A i₃)
    (hfin : AlgebraicGeometry.IsFinite (i₃ ≫ M5.A.F.hom)) (hX : FiniteSetsInAffines M5.X.left) :
    FiniteSetsInAffines (moduli35Of M5 i₃ hmono hchar).X.left := by
  haveI := hfin
  have h1 : FiniteSetsInAffines Z₃ :=
    Y3QuotientDescent.finiteSetsInAffines_of_isAffineHom (X := Z₃) (i₃ ≫ M5.A.F.hom) hX
  exact h1

theorem fsa_moduli35Of_A (M5 : Moduli5) {Z₃ : Scheme.{0}} (i₃ : Z₃ ⟶ M5.A.F.left)
    (hmono : Mono i₃) (hchar : FrameChar 3 M5.A i₃)
    (hfin : AlgebraicGeometry.IsFinite (i₃ ≫ M5.A.F.hom)) (hA : FiniteSetsInAffines M5.A.F.left) :
    FiniteSetsInAffines (moduli35Of M5 i₃ hmono hchar).A.F.left := by
  haveI := hfin
  haveI : AlgebraicGeometry.IsAffineHom (M35Base M5 i₃) := by
    show AlgebraicGeometry.IsAffineHom (i₃ ≫ M5.A.F.hom)
    infer_instance
  haveI := isAffineHom_pullbackFst M5.A (M35Base M5 i₃)
  have h1 : FiniteSetsInAffines (M5.A.pullback (M35Base M5 i₃)).F.left :=
    Y3QuotientDescent.finiteSetsInAffines_of_isAffineHom
      (X := (M5.A.pullback (M35Base M5 i₃)).F.left) (M5.A.pullbackFst (M35Base M5 i₃)) hA
  exact h1

/-! ### The leaves, unpacked -/

theorem b1_projective (hB1 : BuzzardThm21Cor23V15') :
    ∃ (N : ℕ) (i : (B1Data.ofLeaf hB1).X.left ⟶ PN N),
      IsClosedImmersion i ∧ i ≫ toBase N = (B1Data.ofLeaf hB1).X.hom :=
  (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec hB1))).2.2.1

theorem frameData_isFinite {M : ℕ} (hB2 : BuzzardFrameRepTorsor M) (S : Over Z30Base)
    (A : FEC S.left) : AlgebraicGeometry.IsFinite ((FrameData.ofLeaf hB2 S A).i ≫ A.F.hom) :=
  (Classical.choose_spec (Classical.choose_spec (hB2 S A))).2.1

theorem frameRep_isFinite {M : ℕ} (hB2 : BuzzardFrameRep M) (S : Over Z30Base)
    (A : FEC S.left) : AlgebraicGeometry.IsFinite ((FrameData.ofRep hB2 S A).i ≫ A.F.hom) :=
  (Classical.choose_spec (Classical.choose_spec (hB2 S A))).2.1

theorem frameRepNS_isFinite {M : ℕ} (hB2 : BuzzardFrameRepNS M) (S : Over Z30Base)
    (A : FEC S.left) : AlgebraicGeometry.IsFinite ((FrameData.ofRepNS hB2 S A).i ≫ A.F.hom) :=
  (Classical.choose_spec (Classical.choose_spec (hB2 S A))).2.1

abbrev leafD (hB1 : BuzzardThm21Cor23V15') : B1Data := B1Data.ofLeaf hB1

abbrev leafF5 (hB1 : BuzzardThm21Cor23V15') (hB25 : BuzzardFrameRepTorsor 5) :
    FrameData 5 (leafD hB1).A :=
  FrameData.ofLeaf hB25 (leafD hB1).X (leafD hB1).A

abbrev leafF3 (hB1 : BuzzardThm21Cor23V15') (hB25 : BuzzardFrameRepTorsor 5)
    (hB23 : BuzzardFrameRepNS 3) : FrameData 3 (moduli5 hB1 hB25).A :=
  FrameData.ofRepNS hB23 (moduli5 hB1 hB25).X (moduli5 hB1 hB25).A

theorem fsa_X1 (hB1 : BuzzardThm21Cor23V15') : FiniteSetsInAffines (leafD hB1).X.left := by
  obtain ⟨N, j, hj, -⟩ := b1_projective hB1
  haveI := hj
  exact finiteSetsInAffines_of_closedImmersion_PN j

/-- B6 gives a closed immersion of the total space of `A1` into some `PN N'`. -/
theorem fsa_A1 (hB1 : BuzzardThm21Cor23V15') (hB6 : ProjectiveFEC) : FiniteSetsInAffines
    (leafD hB1).A.F.left := by
  obtain ⟨N, j, hj⟩ := hB6 (leafD hB1).X (b1_projective hB1) (leafD hB1).A
  haveI := hj
  exact finiteSetsInAffines_of_closedImmersion_PN j

theorem fsa_X5 (hB1 : BuzzardThm21Cor23V15') (hB25 : BuzzardFrameRepTorsor 5) :
    FiniteSetsInAffines (moduli5 hB1 hB25).X.left :=
  fsa_moduli5Of_X (leafD hB1).X (leafD hB1).A (leafD hB1).α (leafD hB1).ex (leafD hB1).uniq
    (leafF5 hB1 hB25).Z (leafF5 hB1 hB25).i (leafF5 hB1 hB25).mono (leafF5 hB1 hB25).char
    (frameData_isFinite hB25 (leafD hB1).X (leafD hB1).A) (fsa_X1 hB1)

theorem fsa_A5 (hB1 : BuzzardThm21Cor23V15') (hB25 : BuzzardFrameRepTorsor 5)
    (hB6 : ProjectiveFEC) : FiniteSetsInAffines (moduli5 hB1 hB25).A.F.left :=
  fsa_moduli5Of_A (leafD hB1).X (leafD hB1).A (leafD hB1).α (leafD hB1).ex (leafD hB1).uniq
    (leafF5 hB1 hB25).Z (leafF5 hB1 hB25).i (leafF5 hB1 hB25).mono (leafF5 hB1 hB25).char
    (frameData_isFinite hB25 (leafD hB1).X (leafD hB1).A) (fsa_A1 hB1 hB6)

theorem fsa_X35 (hB1 : BuzzardThm21Cor23V15') (hB25 : BuzzardFrameRepTorsor 5)
    (hB23 : BuzzardFrameRepNS 3) : FiniteSetsInAffines (moduli35 (moduli5 hB1 hB25) hB23).X.left :=
  fsa_moduli35Of_X (moduli5 hB1 hB25) (leafF3 hB1 hB25 hB23).i (leafF3 hB1 hB25 hB23).mono
    (leafF3 hB1 hB25 hB23).char
    (frameRepNS_isFinite hB23 (moduli5 hB1 hB25).X (moduli5 hB1 hB25).A) (fsa_X5 hB1 hB25)

theorem fsa_A35 (hB1 : BuzzardThm21Cor23V15') (hB25 : BuzzardFrameRepTorsor 5)
    (hB23 : BuzzardFrameRepNS 3) (hB6 : ProjectiveFEC) :
    FiniteSetsInAffines (moduli35 (moduli5 hB1 hB25) hB23).A.F.left :=
  fsa_moduli35Of_A (moduli5 hB1 hB25) (leafF3 hB1 hB25 hB23).i (leafF3 hB1 hB25 hB23).mono
    (leafF3 hB1 hB25 hB23).char
    (frameRepNS_isFinite hB23 (moduli5 hB1 hB25).X (moduli5 hB1 hB25).A) (fsa_A5 hB1 hB25 hB6)

/-! ## 4. Generic quotient facts -/

section Generic

variable {G : Type} [Group G]

theorem ι_actS {X : Scheme.{0}} (ρX : G →* Aut X) (g : G) :
    Sigma.ι (fun _ : G => X) g ≫ Y3QuotientDescent.actS ρX = (ρX g).asIso.hom := by
  rw [Y3QuotientDescent.actS, Sigma.ι_desc]

theorem ι_actT (X : Scheme.{0}) (g : G) :
    Sigma.ι (fun _ : G => X) g ≫ Y3QuotientDescent.actT X G = 𝟙 X := by
  rw [Y3QuotientDescent.actT, Sigma.ι_desc]

/-- A quotient map is invariant. -/
theorem act_comp_eq {X Y : Scheme.{0}} (ρX : G →* Aut X) {q : X ⟶ Y}
    (hK : IsPullback (Y3QuotientDescent.actS ρX) (Y3QuotientDescent.actT X G) q q) (g : G) :
    (ρX g).asIso.hom ≫ q = q :=
  calc (ρX g).asIso.hom ≫ q
      = (Sigma.ι (fun _ : G => X) g ≫ Y3QuotientDescent.actS ρX) ≫ q := by rw [ι_actS]
    _ = Sigma.ι (fun _ : G => X) g ≫ Y3QuotientDescent.actS ρX ≫ q := Category.assoc _ _ _
    _ = Sigma.ι (fun _ : G => X) g ≫ Y3QuotientDescent.actT X G ≫ q := by rw [hK.w]
    _ = (Sigma.ι (fun _ : G => X) g ≫ Y3QuotientDescent.actT X G) ≫ q :=
        (Category.assoc _ _ _).symm
    _ = q := by rw [ι_actT, Category.id_comp]

/-- An invariant map equalizes the action relation. -/
theorem compat_of_invariant {X Z : Scheme.{0}} (ρX : G →* Aut X) (s : X ⟶ Z)
    (hs : ∀ g, (ρX g).asIso.hom ≫ s = s) :
    Y3QuotientDescent.actS ρX ≫ s = Y3QuotientDescent.actT X G ≫ s := by
  apply Sigma.hom_ext
  intro g
  rw [← Category.assoc, ← Category.assoc, ι_actS, ι_actT, Category.id_comp, hs g]

/-- An equivariant map followed by an invariant quotient map equalizes the source relation. -/
theorem compat_of_equivariant {X A Y : Scheme.{0}} (ρX : G →* Aut X) (ρT : G →* Aut A)
    (p : A ⟶ X) (hp : ∀ g, (ρT g).asIso.hom ≫ p = p ≫ (ρX g).asIso.hom) {q : X ⟶ Y}
    (hK : IsPullback (Y3QuotientDescent.actS ρX) (Y3QuotientDescent.actT X G) q q) :
    Y3QuotientDescent.actS ρT ≫ p ≫ q = Y3QuotientDescent.actT A G ≫ p ≫ q := by
  apply Sigma.hom_ext
  intro g
  calc Sigma.ι (fun _ : G => A) g ≫ Y3QuotientDescent.actS ρT ≫ p ≫ q
      = (Sigma.ι (fun _ : G => A) g ≫ Y3QuotientDescent.actS ρT) ≫ p ≫ q :=
        (Category.assoc _ _ _).symm
    _ = (ρT g).asIso.hom ≫ p ≫ q := by rw [ι_actS]
    _ = ((ρT g).asIso.hom ≫ p) ≫ q := (Category.assoc _ _ _).symm
    _ = (p ≫ (ρX g).asIso.hom) ≫ q := by rw [hp g]
    _ = p ≫ (ρX g).asIso.hom ≫ q := Category.assoc _ _ _
    _ = p ≫ q := by rw [act_comp_eq ρX hK g]
    _ = 𝟙 A ≫ p ≫ q := (Category.id_comp _).symm
    _ = (Sigma.ι (fun _ : G => A) g ≫ Y3QuotientDescent.actT A G) ≫ p ≫ q := by rw [ι_actT]
    _ = Sigma.ι (fun _ : G => A) g ≫ Y3QuotientDescent.actT A G ≫ p ≫ q :=
        Category.assoc _ _ _

/-- The action square of the map `id × p` on the relation objects. -/
theorem sigmaDesc_actS {X A : Scheme.{0}} (ρX : G →* Aut X) (ρT : G →* Aut A) (p : A ⟶ X)
    (hp : ∀ g, (ρT g).asIso.hom ≫ p = p ≫ (ρX g).asIso.hom) :
    (Sigma.desc fun g : G => p ≫ Sigma.ι (fun _ : G => X) g) ≫ Y3QuotientDescent.actS ρX =
      Y3QuotientDescent.actS ρT ≫ p := by
  apply Sigma.hom_ext
  intro g
  rw [Sigma.ι_desc_assoc, Category.assoc, ι_actS, ← Category.assoc, ι_actS, hp g]

end Generic

section Extensive

variable {X A : Scheme.{0}} (p : A ⟶ X)

theorem pullback_fst_id_eq : pullback.fst (𝟙 X) p = pullback.snd (𝟙 X) p ≫ p := by
  have h := pullback.condition (f := 𝟙 X) (g := p)
  rw [Category.comp_id] at h
  exact h

theorem snd_lift_id :
    pullback.snd (𝟙 X) p ≫ pullback.lift p (𝟙 A) (by rw [Category.comp_id, Category.id_comp]) =
      𝟙 _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, Category.id_comp]
    exact (pullback_fst_id_eq p).symm
  · rw [Category.assoc, pullback.lift_snd, Category.comp_id, Category.id_comp]

/-- `∐ (_ : G × PUnit), 𝟙 X ×_X A` is `∐ (_ : G), A`. -/
def sigmaPullbackIso (G : Type) :
    (∐ fun _ : G × PUnit.{1} => pullback (𝟙 X) p) ≅ ∐ fun _ : G => A where
  hom := Sigma.desc fun q => pullback.snd (𝟙 X) p ≫ Sigma.ι (fun _ : G => A) q.1
  inv := Sigma.desc fun g =>
    pullback.lift p (𝟙 A) (by rw [Category.comp_id, Category.id_comp]) ≫
      Sigma.ι (fun _ : G × PUnit.{1} => pullback (𝟙 X) p) (g, PUnit.unit)
  hom_inv_id := by
    apply Sigma.hom_ext
    rintro ⟨g, ⟨⟩⟩
    rw [Sigma.ι_desc_assoc, Category.assoc, Sigma.ι_desc, reassoc_of% (snd_lift_id p),
      Category.comp_id]
  inv_hom_id := by
    apply Sigma.hom_ext
    intro g
    rw [Sigma.ι_desc_assoc, Category.assoc, Sigma.ι_desc, ← Category.assoc, pullback.lift_snd,
      Category.id_comp, Category.comp_id]

theorem ι_sigmaPullbackIso_hom {G : Type} (g : G) :
    Sigma.ι (fun _ : G × PUnit.{1} => pullback (𝟙 X) p) (g, PUnit.unit) ≫
        (sigmaPullbackIso p G).hom =
      pullback.snd (𝟙 X) p ≫ Sigma.ι (fun _ : G => A) g := by
  first
    | exact Sigma.ι_desc _ _
    | simp [sigmaPullbackIso]

/-- The coproduct over a one-point type. -/
def punitSigmaIso (A : Scheme.{0}) : (∐ fun _ : PUnit.{1} => A) ≅ A where
  hom := Sigma.desc fun _ => 𝟙 A
  inv := Sigma.ι (fun _ : PUnit.{1} => A) PUnit.unit
  hom_inv_id := by
    apply Sigma.hom_ext
    rintro ⟨⟩
    rw [Sigma.ι_desc_assoc, Category.id_comp, Category.comp_id]
  inv_hom_id := by
    rw [Sigma.ι_desc]

theorem ι_punitSigmaIso_hom (A : Scheme.{0}) (b : PUnit.{1}) :
    Sigma.ι (fun _ : PUnit.{1} => A) b ≫ (punitSigmaIso A).hom = 𝟙 A := by
  first
    | exact Sigma.ι_desc _ _
    | simp [punitSigmaIso]

/-- The square on the second projections: `∐ (_ : G), A` is the pullback of
`∐ (_ : G), X ⟶ X` along `p`. -/
theorem isPullback_sigmaDesc_actT {G : Type} [Group G] [Finite G] :
    IsPullback (Sigma.desc fun g : G => p ≫ Sigma.ι (fun _ : G => X) g)
      (Y3QuotientDescent.actT A G) (Y3QuotientDescent.actT X G) p := by
  have H := FinitaryPreExtensive.isPullback_sigmaDesc (fun _ : G => 𝟙 X)
    (fun _ : PUnit.{1} => p)
  refine IsPullback.of_iso H (sigmaPullbackIso p G) (Iso.refl _) (punitSigmaIso A) (Iso.refl _)
    ?_ ?_ ?_ ?_
  · apply Sigma.hom_ext
    rintro ⟨g, ⟨⟩⟩
    rw [Iso.refl_hom, Category.comp_id, Sigma.ι_desc, reassoc_of% (ι_sigmaPullbackIso_hom p g),
      Sigma.ι_desc, pullback_fst_id_eq p, Category.assoc]
  · apply Sigma.hom_ext
    rintro ⟨g, ⟨⟩⟩
    rw [Sigma.ι_desc_assoc, Category.assoc, ι_punitSigmaIso_hom,
      reassoc_of% (ι_sigmaPullbackIso_hom p g), ι_actT]
  · rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp, Y3QuotientDescent.actT]
  · apply Sigma.hom_ext
    intro b
    rw [Iso.refl_hom, Category.comp_id, Sigma.ι_desc, reassoc_of% (ι_punitSigmaIso_hom A b)]

end Extensive

/-- The cartesian square of two quotient maps along an equivariant map. -/
theorem cart_of_quotients {X A Y B : Scheme.{0}} {G : Type} [Group G] [Finite G]
    (ρX : G →* Aut X) (ρT : G →* Aut A) (p : A ⟶ X)
    (hp : ∀ g, (ρT g).asIso.hom ≫ p = p ≫ (ρX g).asIso.hom) {qX : X ⟶ Y} {qA : A ⟶ B}
    {b : B ⟶ Y} (hX : IsPullback (Y3QuotientDescent.actS ρX) (Y3QuotientDescent.actT X G) qX qX)
    (hA : IsPullback (Y3QuotientDescent.actS ρT) (Y3QuotientDescent.actT A G) qA qA)
    (hsurj : AlgebraicGeometry.Surjective qA) (hflat : AlgebraicGeometry.Flat qA)
    (hlfp : LocallyOfFinitePresentation qA) (hb : qA ≫ b = p ≫ qX) :
    IsPullback qA p b qX := by
  haveI : (@AlgebraicGeometry.Surjective ⊓ @AlgebraicGeometry.Flat ⊓
      @LocallyOfFinitePresentation : MorphismProperty Scheme).IsStableUnderBaseChange :=
    { of_isPullback h hq :=
        ⟨⟨MorphismProperty.of_isPullback (P := @AlgebraicGeometry.Surjective) h hq.1.1,
            MorphismProperty.of_isPullback (P := @AlgebraicGeometry.Flat) h hq.1.2⟩,
          MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) h hq.2⟩ }
  exact Y3IntegralDescent.isPullback_of_equivariant_kernelPairs
    (@AlgebraicGeometry.Surjective ⊓ @AlgebraicGeometry.Flat ⊓ @LocallyOfFinitePresentation)
    ⟨⟨hsurj, hflat⟩, hlfp⟩ hA hX (isPullback_sigmaDesc_actT p) (sigmaDesc_actS ρX ρT p hp) hb

/-- The outputs of the quotient theorem, with local finite presentation kept. -/
abbrev QSpec {X Y : Scheme.{0}} {G : Type} [Group G] (ρX : G →* Aut X) (q : X ⟶ Y) : Prop :=
  IsPullback (Y3QuotientDescent.actS ρX) (Y3QuotientDescent.actT X G) q q ∧ EffectiveEpi q ∧
    AlgebraicGeometry.IsFinite q ∧ AlgebraicGeometry.Flat q ∧ LocallyOfFinitePresentation q ∧
    AlgebraicGeometry.Surjective q

theorem quotient_spec {X : Scheme.{0}} {G : Type} [Group G] [Finite G] (ρX : G →* Aut X)
    (hfr : ∀ k : G, k ≠ 1 → ∀ (T : Scheme.{0}) (z : T ⟶ X), z ≫ (ρX k).asIso.hom = z →
      IsEmpty T)
    (hX : FiniteSetsInAffines X) : ∃ (Y : Scheme.{0}) (q : X ⟶ Y), QSpec ρX q := by
  obtain ⟨Y, q, -, h₁, h₂, h₃, h₄, h₅, -⟩ :=
    Y3QuotientDescent.exists_quotient_of_free_action ρX
      (Y3QuotientDescent.hfree_of_fixedPointFree ρX fun k hk {T} z hz => hfr k hk T z hz)
      (Y3QuotientDescent.orbit_affine_of_finiteSetsInAffines ρX hX)
  haveI := h₁
  haveI := h₂
  haveI := h₃
  haveI := h₄
  exact ⟨Y, q, h₅, Y3QuotientDescent.effectiveEpi_of_isFinite q, h₁, h₂, h₃, h₄⟩

/-! ## 5. The two quotients of the level-(5,3) datum -/

section Quot

/-- Fixed-point-freeness of the base action, in the shape of `hfix`. -/
abbrev FreeX (M : Moduli35) : Prop :=
  ∀ δ : Y3OrderMod.G 5, δ ≠ 1 → ∀ (T : Scheme.{0}) (z : T ⟶ M.X.left),
    z ≫ (ρ M δ).asIso.hom = z → IsEmpty T

/-- A fixed point of `ρA δ` maps to a fixed point of `ρ δ`. -/
theorem freeA (M : Moduli35) (hfr : FreeX M) :
    ∀ δ : Y3OrderMod.G 5, δ ≠ 1 → ∀ (T : Scheme.{0}) (z : T ⟶ M.A.F.left),
      z ≫ (ρA M δ).asIso.hom = z → IsEmpty T := by
  intro δ hδ T z hz
  refine hfr δ hδ T (z ≫ M.A.F.hom) ?_
  rw [Category.assoc, ← ρA_equivariant M δ, ← Category.assoc, hz]

theorem ρ_over (M : Moduli35) (g : Y3OrderMod.G 5) :
    (ρ M g).asIso.hom ≫ M.X.hom = M.X.hom := by
  rw [ρ_hom]
  exact Over.w (actionMap M g)

variable (M : Moduli35) (hfr : FreeX M)

def quotY (hX : FiniteSetsInAffines M.X.left) : Scheme.{0} := Classical.choose
    (quotient_spec (ρ M) hfr hX)

def quotX (hX : FiniteSetsInAffines M.X.left) : M.X.left ⟶ quotY M hfr hX :=
  Classical.choose (Classical.choose_spec (quotient_spec (ρ M) hfr hX))

theorem quotX_spec (hX : FiniteSetsInAffines M.X.left) : QSpec (ρ M) (quotX M hfr hX) :=
  Classical.choose_spec (Classical.choose_spec (quotient_spec (ρ M) hfr hX))

def quotB (hA : FiniteSetsInAffines M.A.F.left) : Scheme.{0} :=
  Classical.choose (quotient_spec (ρA M) (freeA M hfr) hA)

def quotA (hA : FiniteSetsInAffines M.A.F.left) : M.A.F.left ⟶ quotB M hfr hA :=
  Classical.choose (Classical.choose_spec (quotient_spec (ρA M) (freeA M hfr) hA))

theorem quotA_spec (hA : FiniteSetsInAffines M.A.F.left) : QSpec (ρA M) (quotA M hfr hA) :=
  Classical.choose_spec (Classical.choose_spec (quotient_spec (ρA M) (freeA M hfr) hA))

/-- `b : B ⟶ Y`, descended from `p ≫ qX` along `qA`. -/
def quotb (hX : FiniteSetsInAffines M.X.left) (hA : FiniteSetsInAffines M.A.F.left)
    : quotB M hfr hA ⟶ quotY M hfr hX :=
  haveI : EffectiveEpi (quotA M hfr hA) := (quotA_spec M hfr hA).2.1
  Y3QuotientDescent.descend (quotA_spec M hfr hA).1 (M.A.F.hom ≫ quotX M hfr hX)
    (compat_of_equivariant (ρ M) (ρA M) M.A.F.hom (ρA_equivariant M) (quotX_spec M hfr hX).1)

theorem quotb_fac (hX : FiniteSetsInAffines M.X.left) (hA : FiniteSetsInAffines M.A.F.left) :
    quotA M hfr hA ≫ quotb M hfr hX hA = M.A.F.hom ≫ quotX M hfr hX := by
  haveI : EffectiveEpi (quotA M hfr hA) := (quotA_spec M hfr hA).2.1
  exact Y3QuotientDescent.descend_fac (quotA_spec M hfr hA).1 (M.A.F.hom ≫ quotX M hfr hX)
    (compat_of_equivariant (ρ M) (ρA M) M.A.F.hom (ρA_equivariant M) (quotX_spec M hfr hX).1)

/-- The structure map of the quotient base, descended from `X35.hom`. -/
def quotS (hX : FiniteSetsInAffines M.X.left) : quotY M hfr hX ⟶ Z30Base :=
  haveI : EffectiveEpi (quotX M hfr hX) := (quotX_spec M hfr hX).2.1
  Y3QuotientDescent.descend (quotX_spec M hfr hX).1 M.X.hom
    (compat_of_invariant (ρ M) M.X.hom (ρ_over M))

theorem quotS_fac (hX : FiniteSetsInAffines M.X.left)
    : quotX M hfr hX ≫ quotS M hfr hX = M.X.hom := by
  haveI : EffectiveEpi (quotX M hfr hX) := (quotX_spec M hfr hX).2.1
  exact Y3QuotientDescent.descend_fac (quotX_spec M hfr hX).1 M.X.hom
    (compat_of_invariant (ρ M) M.X.hom (ρ_over M))

end Quot

/-! ## 6. The bundle -/

/-- The quotients of the base and of the total space of a level-(5,3) datum by `G 5`. -/
structure QuotientData (M : Moduli35) where
  Y : Scheme.{0}
  B : Scheme.{0}
  qX : M.X.left ⟶ Y
  qA : M.A.F.left ⟶ B
  b : B ⟶ Y
  kpX : IsPullback (Y3QuotientDescent.actS (ρ M))
    (Y3QuotientDescent.actT M.X.left (Y3OrderMod.G 5)) qX qX
  kpA : IsPullback (Y3QuotientDescent.actS (ρA M))
    (Y3QuotientDescent.actT M.A.F.left (Y3OrderMod.G 5)) qA qA
  effX : EffectiveEpi qX
  effA : EffectiveEpi qA
  finX : AlgebraicGeometry.IsFinite qX
  finA : AlgebraicGeometry.IsFinite qA
  flatX : AlgebraicGeometry.Flat qX
  flatA : AlgebraicGeometry.Flat qA
  lfpX : LocallyOfFinitePresentation qX
  lfpA : LocallyOfFinitePresentation qA
  surjX : AlgebraicGeometry.Surjective qX
  surjA : AlgebraicGeometry.Surjective qA
  hb : qA ≫ b = M.A.F.hom ≫ qX
  cart : IsPullback qA M.A.F.hom b qX
  sY : Y ⟶ Z30Base
  hsY : qX ≫ sY = M.X.hom

/-- The quotient base as an object over `Z30Base`. -/
def QuotientData.YOver {M : Moduli35} (Q : QuotientData M) : Over Z30Base := Over.mk Q.sY

/-- The quotient map as a map over `Z30Base`. -/
def QuotientData.qXOver {M : Moduli35} (Q : QuotientData M) : M.X ⟶ Q.YOver :=
  Over.homMk Q.qX Q.hsY

def quotientData (M : Moduli35) (hfr : FreeX M) (hX : FiniteSetsInAffines M.X.left)
    (hA : FiniteSetsInAffines M.A.F.left) :
    QuotientData M where
  Y := quotY M hfr hX
  B := quotB M hfr hA
  qX := quotX M hfr hX
  qA := quotA M hfr hA
  b := quotb M hfr hX hA
  kpX := (quotX_spec M hfr hX).1
  kpA := (quotA_spec M hfr hA).1
  effX := (quotX_spec M hfr hX).2.1
  effA := (quotA_spec M hfr hA).2.1
  finX := (quotX_spec M hfr hX).2.2.1
  finA := (quotA_spec M hfr hA).2.2.1
  flatX := (quotX_spec M hfr hX).2.2.2.1
  flatA := (quotA_spec M hfr hA).2.2.2.1
  lfpX := (quotX_spec M hfr hX).2.2.2.2.1
  lfpA := (quotA_spec M hfr hA).2.2.2.2.1
  surjX := (quotX_spec M hfr hX).2.2.2.2.2
  surjA := (quotA_spec M hfr hA).2.2.2.2.2
  hb := quotb_fac M hfr hX hA
  cart := cart_of_quotients (ρ M) (ρA M) M.A.F.hom (ρA_equivariant M) (quotX_spec M hfr hX).1
    (quotA_spec M hfr hA).1 (quotA_spec M hfr hA).2.2.2.2.2 (quotA_spec M hfr hA).2.2.2.1
    (quotA_spec M hfr hA).2.2.2.2.1 (quotb_fac M hfr hX hA)
  sY := quotS M hfr hX
  hsY := quotS_fac M hfr hX

/-- The quotient data of the level-(5,3) datum built from the leaves. -/
def quotientDataOfLeaves (hB1 : BuzzardThm21Cor23V15') (hB25 : BuzzardFrameRepTorsor 5)
    (hB23 : BuzzardFrameRepNS 3) (hB3 : SerreRigidityLevel3') (hBC : FECGeomFibre)
    (hB6 : ProjectiveFEC) : QuotientData (moduli35 (moduli5 hB1 hB25) hB23) :=
  quotientData _ (hfix _ hB3 hBC) (fsa_X35 hB1 hB25 hB23) (fsa_A35 hB1 hB25 hB23 hB6)

end Y3Buzzard
