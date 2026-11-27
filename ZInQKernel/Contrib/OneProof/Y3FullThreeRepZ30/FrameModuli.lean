import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.FECPullback
import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.BuzzardLeaves2
noncomputable section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open LeafQM LeafQM.AV
open scoped CategoryTheory.Obj
namespace Y3Buzzard

/-!
# Moduli of false elliptic curves with a 5-frame, and with a (5, 3)-frame (draft)

From the moduli leaf B1' (level `V₁(5)`) and the frame leaf B2' at `M = 5` we build a scheme
`X₅` with a universal false elliptic curve and a universal generator of the full 5-torsion,
as the locus inside the frame scheme where `(1 - e5) P = Q`. From any such datum and B2' at
`M = 3` we then build the datum with both a 5-generator and a 3-generator.
All leaves enter as hypotheses.
-/

attribute [local instance] FEC.grp

/-! ## 1. Generic base change lemmas -/

section Generic

variable {S S' : Scheme.{0}}

/-- The section of `A.pullback g` induced by a point `R` of `A` lying over `g`. -/
def FEC.pointSection (A : FEC S) (g : S' ⟶ S) (R : S' ⟶ A.F.left) (hR : R ≫ A.F.hom = g) :
    S' ⟶ (A.pullback g).F.left :=
  (A.pullback_isPullback g).lift R (𝟙 S') (by rw [hR, Category.id_comp])

theorem FEC.pointSection_fst (A : FEC S) (g : S' ⟶ S) (R : S' ⟶ A.F.left)
    (hR : R ≫ A.F.hom = g) : A.pointSection g R hR ≫ A.pullbackFst g = R :=
  (A.pullback_isPullback g).lift_fst _ _ _

theorem FEC.pointSection_sec (A : FEC S) (g : S' ⟶ S) (R : S' ⟶ A.F.left)
    (hR : R ≫ A.F.hom = g) : A.pointSection g R hR ≫ (A.pullback g).F.hom = 𝟙 S' :=
  (A.pullback_isPullback g).lift_snd _ _ _

/-- An `O`-compatible cartesian square over `g ≫ b` factors through `A.pullback b`. -/
theorem up_fibre {S T B : Scheme.{0}} {A : FEC B} (b : T ⟶ B) {A' : FEC S} {g : S ⟶ T}
    {h₁ : A'.F.left ⟶ A.F.left} (hpb : IsPullback h₁ A'.F.hom A.F.hom (g ≫ b))
    (hι : ∀ a : O, A'.iota a ≫ h₁ = h₁ ≫ A.iota a) :
    ∃ h : A'.F.left ⟶ (A.pullback b).F.left, h ≫ A.pullbackFst b = h₁ ∧
      h ≫ (A.pullback b).F.hom = A'.F.hom ≫ g ∧
      IsPullback h A'.F.hom (A.pullback b).F.hom g ∧
      ∀ a : O, A'.iota a ≫ h = h ≫ (A.pullback b).iota a := by
  obtain ⟨h, hh₁, hh₂⟩ : ∃ h : A'.F.left ⟶ (A.pullback b).F.left,
      h ≫ A.pullbackFst b = h₁ ∧ h ≫ (A.pullback b).F.hom = A'.F.hom ≫ g :=
    ⟨(A.pullback_isPullback b).lift h₁ (A'.F.hom ≫ g)
        (by rw [Category.assoc]; exact hpb.w),
      (A.pullback_isPullback b).lift_fst _ _ _, (A.pullback_isPullback b).lift_snd _ _ _⟩
  refine ⟨h, hh₁, hh₂,
    IsPullback.of_right (by rw [hh₁]; exact hpb) hh₂ (A.pullback_isPullback b), fun a => ?_⟩
  refine (A.pullback_isPullback b).hom_ext ?_ ?_
  · simp only [Category.assoc]
    rw [hh₁, A.pullback_iota_fst, reassoc_of% hh₁, hι a]
  · simp only [Category.assoc]
    rw [(A.pullback b).iota_over a, hh₂, reassoc_of% (A'.iota_over a)]

/-- An `O`-compatible cartesian square into `A.pullback b` gives one into `A`. -/
theorem down_fibre {S T B : Scheme.{0}} {A : FEC B} (b : T ⟶ B) {A' : FEC S} {g : S ⟶ T}
    {h : A'.F.left ⟶ (A.pullback b).F.left}
    (hpb : IsPullback h A'.F.hom (A.pullback b).F.hom g)
    (hι : ∀ a : O, A'.iota a ≫ h = h ≫ (A.pullback b).iota a) :
    IsPullback (h ≫ A.pullbackFst b) A'.F.hom A.F.hom (g ≫ b) ∧
      ∀ a : O, A'.iota a ≫ (h ≫ A.pullbackFst b) = (h ≫ A.pullbackFst b) ≫ A.iota a :=
  ⟨hpb.paste_horiz (A.pullback_isPullback b), fun a => by
    simp only [Category.assoc]
    rw [reassoc_of% (hι a), A.pullback_iota_fst]⟩

/-- A section equation into `A.pullback b` can be checked after the first projection. -/
theorem sec_eq_of_fst {S T B : Scheme.{0}} {A : FEC B} (b : T ⟶ B) {A' : FEC S} {g : S ⟶ T}
    {h : A'.F.left ⟶ (A.pullback b).F.left} (hh₂ : h ≫ (A.pullback b).F.hom = A'.F.hom ≫ g)
    {P' : S ⟶ A'.F.left} (hP' : P' ≫ A'.F.hom = 𝟙 S) {s : T ⟶ (A.pullback b).F.left}
    (hs : s ≫ (A.pullback b).F.hom = 𝟙 T)
    (hfst : P' ≫ h ≫ A.pullbackFst b = g ≫ s ≫ A.pullbackFst b) : P' ≫ h = g ≫ s := by
  refine (A.pullback_isPullback b).hom_ext ?_ ?_
  · simp only [Category.assoc]
    exact hfst
  · simp only [Category.assoc]
    rw [hh₂, hs, reassoc_of% hP', Category.comp_id]

end Generic

/-! ## 2. The leaves, unpacked -/

/-- The existence clause of B1'. -/
abbrev B1Exists {X₁ : Over Z30Base} {A₁ : FEC X₁.left} (α₁ : V15 A₁) : Prop :=
  ∀ (S : Over Z30Base) (A' : FEC S.left) (α' : V15 A'),
    ∃! g : S ⟶ X₁, V15Fibre A₁ α₁ g.left A' α'

/-- The uniqueness clause of B1' for comparison maps. -/
abbrev B1Unique {X₁ : Over Z30Base} {A₁ : FEC X₁.left} (α₁ : V15 A₁) : Prop :=
  ∀ (S : Over Z30Base) (A' : FEC S.left) (α' : V15 A') (g : S ⟶ X₁)
    (h h' : A'.F.left ⟶ A₁.F.left),
    (IsPullback h A'.F.hom A₁.F.hom g.left ∧ (∀ a : O, A'.iota a ≫ h = h ≫ A₁.iota a) ∧
      α'.Q ≫ h = g.left ≫ α₁.Q) →
    (IsPullback h' A'.F.hom A₁.F.hom g.left ∧ (∀ a : O, A'.iota a ≫ h' = h' ≫ A₁.iota a) ∧
      α'.Q ≫ h' = g.left ≫ α₁.Q) → h = h'

/-- The characterization clause of B2'. -/
abbrev FrameChar (M : ℕ) {S : Scheme.{0}} (A : FEC S) {Z : Scheme.{0}} (i : Z ⟶ A.F.left) :
    Prop :=
  ∀ (T : Scheme.{0}) (P : T ⟶ A.F.left), (∃ f : T ⟶ Z, f ≫ i = P) ↔ IsGen M A P

/-- The data of B1' that are used below. -/
structure B1Data where
  X : Over Z30Base
  A : FEC X.left
  α : V15 A
  ex : B1Exists α
  uniq : B1Unique α

/-- Choice of the data of B1'. -/
def B1Data.ofLeaf (hB1 : BuzzardThm21Cor23V15') : B1Data where
  X := Classical.choose hB1
  A := Classical.choose (Classical.choose_spec hB1)
  α := Classical.choose (Classical.choose_spec (Classical.choose_spec hB1))
  ex := (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec hB1))).2.2.2.1
  uniq := (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec hB1))).2.2.2.2

/-- The data of B2' at `(S, A)` that are used below. -/
structure FrameData (M : ℕ) {S : Scheme.{0}} (A : FEC S) where
  Z : Scheme.{0}
  i : Z ⟶ A.F.left
  mono : Mono i
  char : FrameChar M A i

/-- Choice of the data of B2'. A closed immersion is a monomorphism. -/
def FrameData.ofLeaf {M : ℕ} (hB2 : BuzzardFrameRepTorsor M) (S : Over Z30Base)
    (A : FEC S.left) : FrameData M A where
  Z := Classical.choose (hB2 S A)
  i := Classical.choose (Classical.choose_spec (hB2 S A))
  mono := by
    haveI := (Classical.choose_spec (Classical.choose_spec (hB2 S A))).1
    first
      | exact inferInstance
      | exact IsPreimmersion.instMonoScheme _
      | exact AlgebraicGeometry.IsPreimmersion.instMonoScheme _
  char := (Classical.choose_spec (Classical.choose_spec (hB2 S A))).2.2.2.2.1

/-- Choice of the data of B2 (frame representability without the torsor clause). -/
def FrameData.ofRep {M : ℕ} (hB2 : BuzzardFrameRep M) (S : Over Z30Base)
    (A : FEC S.left) : FrameData M A where
  Z := Classical.choose (hB2 S A)
  i := Classical.choose (Classical.choose_spec (hB2 S A))
  mono := by
    haveI := (Classical.choose_spec (Classical.choose_spec (hB2 S A))).1
    first
      | exact inferInstance
      | exact IsPreimmersion.instMonoScheme _
      | exact AlgebraicGeometry.IsPreimmersion.instMonoScheme _
  char := (Classical.choose_spec (Classical.choose_spec (hB2 S A))).2.2.2.2

/-- Frame representability without the torsor clause and without surjectivity: the full
level-`M` frames are represented by a closed subscheme of `A`, finite and etale over the base. -/
def BuzzardFrameRepNS (M : ℕ) : Prop :=
  ∀ (S : Over Z30Base) (A : FEC S.left),
    ∃ (Z : Scheme.{0}) (i : Z ⟶ A.F.left), IsClosedImmersion i ∧
      AlgebraicGeometry.IsFinite (i ≫ A.F.hom) ∧ AlgebraicGeometry.Etale (i ≫ A.F.hom) ∧
      ∀ (T : Scheme.{0}) (P : T ⟶ A.F.left), (∃ f : T ⟶ Z, f ≫ i = P) ↔ IsGen M A P

theorem frameRepNS_of_rep {M : ℕ} (h : BuzzardFrameRep M) : BuzzardFrameRepNS M :=
  fun S A => by
    obtain ⟨Z, i, h1, h2, h3, -, h5⟩ := h S A
    exact ⟨Z, i, h1, h2, h3, h5⟩

/-- Choice of the data of `BuzzardFrameRepNS`. -/
def FrameData.ofRepNS {M : ℕ} (hB2 : BuzzardFrameRepNS M) (S : Over Z30Base)
    (A : FEC S.left) : FrameData M A where
  Z := Classical.choose (hB2 S A)
  i := Classical.choose (Classical.choose_spec (hB2 S A))
  mono := by
    haveI := (Classical.choose_spec (Classical.choose_spec (hB2 S A))).1
    first
      | exact inferInstance
      | exact IsPreimmersion.instMonoScheme _
      | exact AlgebraicGeometry.IsPreimmersion.instMonoScheme _
  char := (Classical.choose_spec (Classical.choose_spec (hB2 S A))).2.2.2

/-! ## 3. The level-5 frame moduli datum -/

/-- A false elliptic curve over a `Z[1/30]`-scheme with a section generating the full
5-torsion, representing that moduli problem with unique comparison maps. -/
structure Moduli5 where
  X : Over Z30Base
  A : FEC X.left
  P : X.left ⟶ A.F.left
  sec : P ≫ A.F.hom = 𝟙 X.left
  gen : IsGen 5 A P
  rep : ∀ (S : Over Z30Base) (A' : FEC S.left) (P' : S.left ⟶ A'.F.left),
    P' ≫ A'.F.hom = 𝟙 S.left → IsGen 5 A' P' →
      ∃! g : S ⟶ X, ∃ h : A'.F.left ⟶ A.F.left, IsPullback h A'.F.hom A.F.hom g.left ∧
        (∀ a : O, A'.iota a ≫ h = h ≫ A.iota a) ∧ P' ≫ h = g.left ≫ P
  huniq : ∀ (S : Over Z30Base) (A' : FEC S.left) (P' : S.left ⟶ A'.F.left),
    P' ≫ A'.F.hom = 𝟙 S.left → IsGen 5 A' P' →
      ∀ (g : S ⟶ X) (h h' : A'.F.left ⟶ A.F.left),
        (IsPullback h A'.F.hom A.F.hom g.left ∧ (∀ a : O, A'.iota a ≫ h = h ≫ A.iota a) ∧
          P' ≫ h = g.left ≫ P) →
        (IsPullback h' A'.F.hom A.F.hom g.left ∧ (∀ a : O, A'.iota a ≫ h' = h' ≫ A.iota a) ∧
          P' ≫ h' = g.left ≫ P) → h = h'

section Level5

variable {X₁ : Over Z30Base} {A₁ : FEC X₁.left} (α₁ : V15 A₁) {Z : Scheme.{0}}
  (i : Z ⟶ A₁.F.left)

/-- The locus of frame points `P` with `(1 - e5) P = Q`. -/
abbrev M5Locus : Scheme.{0} := equalizer (i ≫ A₁.iota (1 - e5)) (i ≫ A₁.F.hom ≫ α₁.Q)

/-- Its inclusion into the frame scheme. -/
abbrev M5Incl : M5Locus α₁ i ⟶ Z := equalizer.ι (i ≫ A₁.iota (1 - e5)) (i ≫ A₁.F.hom ≫ α₁.Q)

/-- Its map to `X₁`. -/
def M5Base : M5Locus α₁ i ⟶ X₁.left := M5Incl α₁ i ≫ i ≫ A₁.F.hom

theorem M5Base_eq : M5Base α₁ i = M5Incl α₁ i ≫ i ≫ A₁.F.hom := rfl

/-- The locus as an object over the base. -/
abbrev M5X : Over Z30Base := Over.mk (M5Base α₁ i ≫ X₁.hom)

/-- The universal curve on the locus. -/
abbrev M5A : FEC (M5X α₁ i).left := A₁.pullback (M5Base α₁ i)

/-- The universal 5-generator on the locus: the tautological frame point. -/
abbrev M5P : (M5X α₁ i).left ⟶ (M5A α₁ i).F.left :=
  A₁.pointSection (M5Base α₁ i) (M5Incl α₁ i ≫ i) (Category.assoc _ _ _)

theorem M5_condition :
    M5Incl α₁ i ≫ i ≫ A₁.iota (1 - e5) = M5Incl α₁ i ≫ i ≫ A₁.F.hom ≫ α₁.Q :=
  equalizer.condition _ _

theorem M5P_fst : M5P α₁ i ≫ A₁.pullbackFst (M5Base α₁ i) = M5Incl α₁ i ≫ i :=
  FEC.pointSection_fst _ _ _ _

theorem M5P_sec : M5P α₁ i ≫ (M5A α₁ i).F.hom = 𝟙 (M5X α₁ i).left :=
  FEC.pointSection_sec _ _ _ _

theorem M5P_gen (hchar : FrameChar 5 A₁ i) : IsGen 5 (M5A α₁ i) (M5P α₁ i) := by
  refine (isGen_iff_of_fibre (A₁.pullback_isPullback (M5Base α₁ i))
    (A₁.pullback_iota_fst (M5Base α₁ i))).2 ?_
  rw [M5P_fst]
  exact (hchar _ _).1 ⟨M5Incl α₁ i, rfl⟩

/-- The `Q`-equation transported down to `X₁`. -/
theorem m5_Q {S : Scheme.{0}} {A' : FEC S} {P' : S ⟶ A'.F.left} {g : S ⟶ M5Locus α₁ i}
    {h : A'.F.left ⟶ (M5A α₁ i).F.left}
    (hι : ∀ a : O, A'.iota a ≫ h = h ≫ (M5A α₁ i).iota a) (hP : P' ≫ h = g ≫ M5P α₁ i) :
    (P' ≫ A'.iota (1 - e5)) ≫ (h ≫ A₁.pullbackFst (M5Base α₁ i)) =
      (g ≫ M5Base α₁ i) ≫ α₁.Q := by
  have e : (P' ≫ A'.iota (1 - e5)) ≫ (h ≫ A₁.pullbackFst (M5Base α₁ i)) =
      g ≫ M5Incl α₁ i ≫ i ≫ A₁.F.hom ≫ α₁.Q := by
    simp only [Category.assoc]
    rw [reassoc_of% (hι (1 - e5)), A₁.pullback_iota_fst, reassoc_of% hP,
      reassoc_of% (M5P_fst α₁ i), M5_condition]
  rw [e, M5Base_eq]
  simp only [Category.assoc]

theorem m5_rep (hmono : Mono i) (hex : B1Exists α₁) (hun : B1Unique α₁)
    (hchar : FrameChar 5 A₁ i) (S : Over Z30Base) (A' : FEC S.left)
    (P' : S.left ⟶ A'.F.left) (hP' : P' ≫ A'.F.hom = 𝟙 S.left) (hg : IsGen 5 A' P') :
    ∃! g : S ⟶ M5X α₁ i, ∃ h : A'.F.left ⟶ (M5A α₁ i).F.left,
      IsPullback h A'.F.hom (M5A α₁ i).F.hom g.left ∧
      (∀ a : O, A'.iota a ≫ h = h ≫ (M5A α₁ i).iota a) ∧ P' ≫ h = g.left ≫ M5P α₁ i := by
  haveI := hmono
  obtain ⟨g₁, ⟨h₁, hpb₁, hι₁, hQ₁⟩, hg₁u⟩ := hex S A' (v15_of_isGen5 A' P' hP' hg)
  have hQ₁' : (P' ≫ A'.iota (1 - e5)) ≫ h₁ = g₁.left ≫ α₁.Q := hQ₁
  have hπ : P' ≫ h₁ ≫ A₁.F.hom = g₁.left := by
    rw [hpb₁.w, ← Category.assoc, hP', Category.id_comp]
  obtain ⟨f, hf⟩ := (hchar S.left (P' ≫ h₁)).2 (isGen_of_fibre hpb₁ hι₁ hg)
  have heq : f ≫ i ≫ A₁.iota (1 - e5) = f ≫ i ≫ A₁.F.hom ≫ α₁.Q := by
    calc f ≫ i ≫ A₁.iota (1 - e5) = (P' ≫ A'.iota (1 - e5)) ≫ h₁ := by
          rw [reassoc_of% hf, ← hι₁ (1 - e5), Category.assoc]
      _ = g₁.left ≫ α₁.Q := hQ₁'
      _ = f ≫ i ≫ A₁.F.hom ≫ α₁.Q := by
          rw [reassoc_of% hf, reassoc_of% hπ]
  obtain ⟨k, hk⟩ : ∃ k : S.left ⟶ M5Locus α₁ i, k ≫ M5Incl α₁ i = f :=
    ⟨equalizer.lift f heq, equalizer.lift_ι f heq⟩
  have hkb : k ≫ M5Base α₁ i = g₁.left := by
    rw [M5Base_eq, reassoc_of% hk, reassoc_of% hf, hπ]
  have hw : k ≫ (M5X α₁ i).hom = S.hom := by
    show k ≫ M5Base α₁ i ≫ X₁.hom = S.hom
    rw [reassoc_of% hkb, Over.w g₁]
  obtain ⟨h, hh₁, hh₂, hpb, hι⟩ :=
    up_fibre (M5Base α₁ i) (g := k) (by rw [hkb]; exact hpb₁) hι₁
  refine ⟨Over.homMk k hw, ⟨h, hpb, hι, ?_⟩, ?_⟩
  · show P' ≫ h = k ≫ M5P α₁ i
    refine sec_eq_of_fst (M5Base α₁ i) hh₂ hP' (M5P_sec α₁ i) ?_
    rw [hh₁, M5P_fst, reassoc_of% hk, hf]
  · rintro g' ⟨h', hpb', hι', hP''⟩
    obtain ⟨hpbd, hιd⟩ := down_fibre (M5Base α₁ i) hpb' hι'
    have hw' : (g'.left ≫ M5Base α₁ i) ≫ X₁.hom = S.hom := by
      rw [Category.assoc]
      exact Over.w g'
    have hb' : g'.left ≫ M5Base α₁ i = g₁.left :=
      congrArg (fun t : S ⟶ X₁ => t.left)
        (hg₁u (Over.homMk (g'.left ≫ M5Base α₁ i) hw')
          (Exists.intro (h' ≫ A₁.pullbackFst (M5Base α₁ i))
            ⟨hpbd, hιd, m5_Q α₁ i hι' hP''⟩))
    have hfst : h' ≫ A₁.pullbackFst (M5Base α₁ i) = h₁ := by
      refine hun S A' (v15_of_isGen5 A' P' hP' hg) g₁ (h' ≫ A₁.pullbackFst (M5Base α₁ i)) h₁
        ⟨?_, hιd, ?_⟩ ⟨hpb₁, hι₁, hQ₁⟩
      · rw [← hb']
        exact hpbd
      · rw [← hb']
        exact m5_Q α₁ i hι' hP''
    have hpt : g'.left ≫ M5Incl α₁ i ≫ i = k ≫ M5Incl α₁ i ≫ i := by
      calc g'.left ≫ M5Incl α₁ i ≫ i
          = g'.left ≫ M5P α₁ i ≫ A₁.pullbackFst (M5Base α₁ i) := by rw [M5P_fst]
        _ = (P' ≫ h') ≫ A₁.pullbackFst (M5Base α₁ i) := by rw [hP'', Category.assoc]
        _ = f ≫ i := by rw [Category.assoc, hfst, hf]
        _ = k ≫ M5Incl α₁ i ≫ i := by rw [reassoc_of% hk]
    apply Over.OverMorphism.ext
    show g'.left = k
    rw [← Category.assoc, ← Category.assoc] at hpt
    exact (cancel_mono (M5Incl α₁ i)).1 ((cancel_mono i).1 hpt)

theorem m5_huniq (hun : B1Unique α₁) (S : Over Z30Base) (A' : FEC S.left)
    (P' : S.left ⟶ A'.F.left) (hP' : P' ≫ A'.F.hom = 𝟙 S.left) (hg : IsGen 5 A' P')
    (g : S ⟶ M5X α₁ i) (h h' : A'.F.left ⟶ (M5A α₁ i).F.left)
    (H : IsPullback h A'.F.hom (M5A α₁ i).F.hom g.left ∧
      (∀ a : O, A'.iota a ≫ h = h ≫ (M5A α₁ i).iota a) ∧ P' ≫ h = g.left ≫ M5P α₁ i)
    (H' : IsPullback h' A'.F.hom (M5A α₁ i).F.hom g.left ∧
      (∀ a : O, A'.iota a ≫ h' = h' ≫ (M5A α₁ i).iota a) ∧ P' ≫ h' = g.left ≫ M5P α₁ i) :
    h = h' := by
  obtain ⟨hpb, hι, hP⟩ := H
  obtain ⟨hpb', hι', hP2⟩ := H'
  obtain ⟨hpbd, hιd⟩ := down_fibre (M5Base α₁ i) hpb hι
  obtain ⟨hpbd', hιd'⟩ := down_fibre (M5Base α₁ i) hpb' hι'
  have hw' : (g.left ≫ M5Base α₁ i) ≫ X₁.hom = S.hom := by
    rw [Category.assoc]
    exact Over.w g
  refine (A₁.pullback_isPullback (M5Base α₁ i)).hom_ext ?_ (hpb.w.trans hpb'.w.symm)
  exact hun S A' (v15_of_isGen5 A' P' hP' hg) (Over.homMk (g.left ≫ M5Base α₁ i) hw')
    (h ≫ A₁.pullbackFst (M5Base α₁ i)) (h' ≫ A₁.pullbackFst (M5Base α₁ i))
    ⟨hpbd, hιd, m5_Q α₁ i hι hP⟩ ⟨hpbd', hιd', m5_Q α₁ i hι' hP2⟩

end Level5

/-- The level-5 frame datum from unpacked leaves. -/
def moduli5Of (X₁ : Over Z30Base) (A₁ : FEC X₁.left) (α₁ : V15 A₁) (hex : B1Exists α₁)
    (hun : B1Unique α₁) (Z : Scheme.{0}) (i : Z ⟶ A₁.F.left) (hmono : Mono i)
    (hchar : FrameChar 5 A₁ i) : Moduli5 where
  X := M5X α₁ i
  A := M5A α₁ i
  P := M5P α₁ i
  sec := M5P_sec α₁ i
  gen := M5P_gen α₁ i hchar
  rep := m5_rep α₁ i hmono hex hun hchar
  huniq := m5_huniq α₁ i hun

/-- The level-5 frame datum from B1' and B2' at `M = 5`. -/
def moduli5 (hB1 : BuzzardThm21Cor23V15') (hB2 : BuzzardFrameRepTorsor 5) : Moduli5 :=
  let D := B1Data.ofLeaf hB1
  let F := FrameData.ofLeaf hB2 D.X D.A
  moduli5Of D.X D.A D.α D.ex D.uniq F.Z F.i F.mono F.char

/-! ## 4. Adding a 3-frame -/

/-- As `Moduli5`, with a second section generating the full 3-torsion. -/
structure Moduli35 where
  X : Over Z30Base
  A : FEC X.left
  P5 : X.left ⟶ A.F.left
  P3 : X.left ⟶ A.F.left
  sec5 : P5 ≫ A.F.hom = 𝟙 X.left
  sec3 : P3 ≫ A.F.hom = 𝟙 X.left
  gen5 : IsGen 5 A P5
  gen3 : IsGen 3 A P3
  rep : ∀ (S : Over Z30Base) (A' : FEC S.left) (P5' P3' : S.left ⟶ A'.F.left),
    P5' ≫ A'.F.hom = 𝟙 S.left → P3' ≫ A'.F.hom = 𝟙 S.left →
    IsGen 5 A' P5' → IsGen 3 A' P3' →
      ∃! g : S ⟶ X, ∃ h : A'.F.left ⟶ A.F.left, IsPullback h A'.F.hom A.F.hom g.left ∧
        (∀ a : O, A'.iota a ≫ h = h ≫ A.iota a) ∧
        P5' ≫ h = g.left ≫ P5 ∧ P3' ≫ h = g.left ≫ P3
  huniq : ∀ (S : Over Z30Base) (A' : FEC S.left) (P5' P3' : S.left ⟶ A'.F.left),
    P5' ≫ A'.F.hom = 𝟙 S.left → P3' ≫ A'.F.hom = 𝟙 S.left →
    IsGen 5 A' P5' → IsGen 3 A' P3' →
      ∀ (g : S ⟶ X) (h h' : A'.F.left ⟶ A.F.left),
        (IsPullback h A'.F.hom A.F.hom g.left ∧ (∀ a : O, A'.iota a ≫ h = h ≫ A.iota a) ∧
          P5' ≫ h = g.left ≫ P5 ∧ P3' ≫ h = g.left ≫ P3) →
        (IsPullback h' A'.F.hom A.F.hom g.left ∧ (∀ a : O, A'.iota a ≫ h' = h' ≫ A.iota a) ∧
          P5' ≫ h' = g.left ≫ P5 ∧ P3' ≫ h' = g.left ≫ P3) → h = h'

section Level35

variable (M : Moduli5) {Z₃ : Scheme.{0}} (i₃ : Z₃ ⟶ M.A.F.left)

/-- The 3-frame scheme mapped to the level-5 base. -/
def M35Base : Z₃ ⟶ M.X.left := i₃ ≫ M.A.F.hom

abbrev M35X : Over Z30Base := Over.mk (M35Base M i₃ ≫ M.X.hom)

abbrev M35A : FEC (M35X M i₃).left := M.A.pullback (M35Base M i₃)

abbrev M35P5 : (M35X M i₃).left ⟶ (M35A M i₃).F.left :=
  M.A.pullbackSection (M35Base M i₃) M.P M.sec

abbrev M35P3 : (M35X M i₃).left ⟶ (M35A M i₃).F.left :=
  M.A.pointSection (M35Base M i₃) i₃ rfl

theorem M35P5_fst : M35P5 M i₃ ≫ M.A.pullbackFst (M35Base M i₃) = M35Base M i₃ ≫ M.P :=
  M.A.pullbackSection_fst (M35Base M i₃) M.P M.sec

theorem M35P5_sec : M35P5 M i₃ ≫ (M35A M i₃).F.hom = 𝟙 (M35X M i₃).left :=
  M.A.pullbackSection_sec (M35Base M i₃) M.P M.sec

theorem M35P5_gen : IsGen 5 (M35A M i₃) (M35P5 M i₃) :=
  M.A.isGen_pullbackSection (M35Base M i₃) M.P M.sec M.gen

theorem M35P3_fst : M35P3 M i₃ ≫ M.A.pullbackFst (M35Base M i₃) = i₃ :=
  FEC.pointSection_fst _ _ _ _

theorem M35P3_sec : M35P3 M i₃ ≫ (M35A M i₃).F.hom = 𝟙 (M35X M i₃).left :=
  FEC.pointSection_sec _ _ _ _

theorem M35P3_gen (hchar : FrameChar 3 M.A i₃) : IsGen 3 (M35A M i₃) (M35P3 M i₃) := by
  refine (isGen_iff_of_fibre (M.A.pullback_isPullback (M35Base M i₃))
    (M.A.pullback_iota_fst (M35Base M i₃))).2 ?_
  rw [M35P3_fst]
  exact (hchar Z₃ i₃).1 ⟨𝟙 Z₃, Category.id_comp i₃⟩

theorem m35_P5 {S : Scheme.{0}} {A' : FEC S} {P' : S ⟶ A'.F.left} {g : S ⟶ Z₃}
    {h : A'.F.left ⟶ (M35A M i₃).F.left} (hP : P' ≫ h = g ≫ M35P5 M i₃) :
    P' ≫ (h ≫ M.A.pullbackFst (M35Base M i₃)) = (g ≫ M35Base M i₃) ≫ M.P := by
  rw [← Category.assoc, hP, Category.assoc, M35P5_fst, ← Category.assoc]

theorem m35_rep (hmono : Mono i₃) (hchar : FrameChar 3 M.A i₃) (S : Over Z30Base)
    (A' : FEC S.left) (P5' P3' : S.left ⟶ A'.F.left) (hs5 : P5' ≫ A'.F.hom = 𝟙 S.left)
    (hs3 : P3' ≫ A'.F.hom = 𝟙 S.left) (hg5 : IsGen 5 A' P5') (hg3 : IsGen 3 A' P3') :
    ∃! g : S ⟶ M35X M i₃, ∃ h : A'.F.left ⟶ (M35A M i₃).F.left,
      IsPullback h A'.F.hom (M35A M i₃).F.hom g.left ∧
      (∀ a : O, A'.iota a ≫ h = h ≫ (M35A M i₃).iota a) ∧
      P5' ≫ h = g.left ≫ M35P5 M i₃ ∧ P3' ≫ h = g.left ≫ M35P3 M i₃ := by
  haveI := hmono
  obtain ⟨g₅, ⟨h₅, hpb₅, hι₅, hP₅⟩, hg₅u⟩ := M.rep S A' P5' hs5 hg5
  have hπ : P3' ≫ h₅ ≫ M.A.F.hom = g₅.left := by
    rw [hpb₅.w, ← Category.assoc, hs3, Category.id_comp]
  obtain ⟨f, hf⟩ := (hchar S.left (P3' ≫ h₅)).2 (isGen_of_fibre hpb₅ hι₅ hg3)
  have hfb : f ≫ M35Base M i₃ = g₅.left := by
    show f ≫ i₃ ≫ M.A.F.hom = g₅.left
    rw [reassoc_of% hf, hπ]
  have hw : f ≫ (M35X M i₃).hom = S.hom := by
    show f ≫ M35Base M i₃ ≫ M.X.hom = S.hom
    rw [reassoc_of% hfb, Over.w g₅]
  obtain ⟨h, hh₁, hh₂, hpb, hι⟩ :=
    up_fibre (M35Base M i₃) (g := f) (by rw [hfb]; exact hpb₅) hι₅
  refine ⟨Over.homMk f hw, ⟨h, hpb, hι, ?_, ?_⟩, ?_⟩
  · show P5' ≫ h = f ≫ M35P5 M i₃
    refine sec_eq_of_fst (M35Base M i₃) hh₂ hs5 (M35P5_sec M i₃) ?_
    rw [hh₁, M35P5_fst, reassoc_of% hfb, hP₅]
  · show P3' ≫ h = f ≫ M35P3 M i₃
    refine sec_eq_of_fst (M35Base M i₃) hh₂ hs3 (M35P3_sec M i₃) ?_
    rw [hh₁, M35P3_fst, hf]
  · rintro g' ⟨h', hpb', hι', hP5b, hP3b⟩
    obtain ⟨hpbd, hιd⟩ := down_fibre (M35Base M i₃) hpb' hι'
    have hw' : (g'.left ≫ M35Base M i₃) ≫ M.X.hom = S.hom := by
      rw [Category.assoc]
      exact Over.w g'
    have hb' : g'.left ≫ M35Base M i₃ = g₅.left :=
      congrArg (fun t : S ⟶ M.X => t.left)
        (hg₅u (Over.homMk (g'.left ≫ M35Base M i₃) hw')
          ⟨h' ≫ M.A.pullbackFst (M35Base M i₃), hpbd, hιd, m35_P5 M i₃ hP5b⟩)
    have hfst : h' ≫ M.A.pullbackFst (M35Base M i₃) = h₅ := by
      refine M.huniq S A' P5' hs5 hg5 g₅ (h' ≫ M.A.pullbackFst (M35Base M i₃)) h₅
        ⟨?_, hιd, ?_⟩ ⟨hpb₅, hι₅, hP₅⟩
      · rw [← hb']
        exact hpbd
      · rw [← hb']
        exact m35_P5 M i₃ hP5b
    have hpt : g'.left ≫ i₃ = f ≫ i₃ := by
      calc g'.left ≫ i₃
          = g'.left ≫ M35P3 M i₃ ≫ M.A.pullbackFst (M35Base M i₃) := by rw [M35P3_fst]
        _ = (P3' ≫ h') ≫ M.A.pullbackFst (M35Base M i₃) := by rw [hP3b, Category.assoc]
        _ = f ≫ i₃ := by rw [Category.assoc, hfst, hf]
    apply Over.OverMorphism.ext
    show g'.left = f
    exact (cancel_mono i₃).1 hpt

theorem m35_huniq (S : Over Z30Base) (A' : FEC S.left) (P5' P3' : S.left ⟶ A'.F.left)
    (hs5 : P5' ≫ A'.F.hom = 𝟙 S.left) (_hs3 : P3' ≫ A'.F.hom = 𝟙 S.left)
    (hg5 : IsGen 5 A' P5') (_hg3 : IsGen 3 A' P3') (g : S ⟶ M35X M i₃)
    (h h' : A'.F.left ⟶ (M35A M i₃).F.left)
    (H : IsPullback h A'.F.hom (M35A M i₃).F.hom g.left ∧
      (∀ a : O, A'.iota a ≫ h = h ≫ (M35A M i₃).iota a) ∧
      P5' ≫ h = g.left ≫ M35P5 M i₃ ∧ P3' ≫ h = g.left ≫ M35P3 M i₃)
    (H' : IsPullback h' A'.F.hom (M35A M i₃).F.hom g.left ∧
      (∀ a : O, A'.iota a ≫ h' = h' ≫ (M35A M i₃).iota a) ∧
      P5' ≫ h' = g.left ≫ M35P5 M i₃ ∧ P3' ≫ h' = g.left ≫ M35P3 M i₃) :
    h = h' := by
  obtain ⟨hpb, hι, hPa, -⟩ := H
  obtain ⟨hpb', hι', hPb, -⟩ := H'
  obtain ⟨hpbd, hιd⟩ := down_fibre (M35Base M i₃) hpb hι
  obtain ⟨hpbd', hιd'⟩ := down_fibre (M35Base M i₃) hpb' hι'
  have hw' : (g.left ≫ M35Base M i₃) ≫ M.X.hom = S.hom := by
    rw [Category.assoc]
    exact Over.w g
  refine (M.A.pullback_isPullback (M35Base M i₃)).hom_ext ?_ (hpb.w.trans hpb'.w.symm)
  exact M.huniq S A' P5' hs5 hg5 (Over.homMk (g.left ≫ M35Base M i₃) hw')
    (h ≫ M.A.pullbackFst (M35Base M i₃)) (h' ≫ M.A.pullbackFst (M35Base M i₃))
    ⟨hpbd, hιd, m35_P5 M i₃ hPa⟩ ⟨hpbd', hιd', m35_P5 M i₃ hPb⟩

end Level35

/-- The (5, 3)-frame datum from a 5-frame datum and an unpacked 3-frame leaf. -/
def moduli35Of (M : Moduli5) {Z₃ : Scheme.{0}} (i₃ : Z₃ ⟶ M.A.F.left) (hmono : Mono i₃)
    (hchar : FrameChar 3 M.A i₃) : Moduli35 where
  X := M35X M i₃
  A := M35A M i₃
  P5 := M35P5 M i₃
  P3 := M35P3 M i₃
  sec5 := M35P5_sec M i₃
  sec3 := M35P3_sec M i₃
  gen5 := M35P5_gen M i₃
  gen3 := M35P3_gen M i₃ hchar
  rep := m35_rep M i₃ hmono hchar
  huniq := m35_huniq M i₃

/-- The (5, 3)-frame datum from a 5-frame datum and frame representability at `M = 3`. -/
def moduli35 (M5 : Moduli5) (hB2 : BuzzardFrameRepNS 3) : Moduli35 :=
  let F := FrameData.ofRepNS hB2 M5.X M5.A
  moduli35Of M5 F.i F.mono F.char

end Y3Buzzard
