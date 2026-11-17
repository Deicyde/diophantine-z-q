import ZInQKernel.Contrib.OneProof.PicDictionary
import ZInQKernel.Contrib.SmoothFibre.Basic

/-! # pic-dict: `PicZeroAbVar` from four statements (the identity component as an abelian variety) -/

noncomputable section

set_option linter.style.haveILetI false

open CategoryTheory AlgebraicGeometry Opposite MonoidalCategory Limits
open scoped CategoryTheory.MonObj

namespace PicDict

open T09Pic PkgI3 PkgI3.AbVar

/-- A scheme smooth over a field is reduced. -/
theorem isReduced_of_smooth_field {X : Scheme.{0}} {L : Type} [Field L]
    (f : X ⟶ Spec (CommRingCat.of L)) [Smooth f] : IsReduced X := by
  haveI : ∀ i, IsReduced (X.affineCover.X i) := fun i => by
    let g := X.affineCover.f i ≫ f
    haveI : Smooth g := inferInstance
    have hs := g.smooth_appLE (isAffineOpen_top (Spec (CommRingCat.of L)))
      (isAffineOpen_top (X.affineCover.X i)) le_top
    let φ : L →+* Γ(X.affineCover.X i, ⊤) :=
      (g.appLE ⊤ ⊤ le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of L)).inv.hom
    have hφ : φ.Smooth := by
      refine RingHom.Smooth.comp ?_ hs
      exact RingHom.Smooth.of_bijective (ConcreteCategory.bijective_of_isIso _)
    letI := φ.toAlgebra
    haveI : Algebra.Smooth L Γ(X.affineCover.X i, ⊤) := hφ
    haveI : _root_.IsReduced Γ(X.affineCover.X i, ⊤) :=
      ZInQ.SmoothFibre.isReduced_of_smooth_of_field L _
    exact isReduced_of_isAffine_isReduced _
  exact IsReduced.of_openCover (X := X) X.affineCover

/-- Smooth morphisms are geometrically reduced. -/
theorem geometricallyReduced_of_smooth {X Y : Scheme.{0}} (f : X ⟶ Y) [Smooth f] :
    GeometricallyReduced f := by
  rw [GeometricallyReduced.eq_geometrically]
  intro K _ y Z fst snd h
  haveI : Smooth snd := MorphismProperty.of_isPullback (P := @Smooth) h inferInstance
  exact isReduced_of_smooth_field snd

/-! ## Leaves -/

/-- **LEAF (Z1, the Picard scheme is locally of finite type).** For an abelian variety `A` over a field `K`, a
scheme representing `Pic_{A/K}` is locally of finite type over `K`. Kleiman, *The Picard scheme*, Thm 9.4.8
(`Pic_{X/S}` exists, separated and locally of finite presentation, for `X/S` projective flat with geometrically
integral fibres); representing objects are unique up to isomorphism. Locator UNVERIFIED. -/
def PicLocFinType : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (P : Over (Spec (CommRingCat.of K)))
    (_ : (picardFunctor A.X.hom).obj.RepresentableBy P), LocallyOfFiniteType P.hom

/-- **LEAF (Z2, the identity component of a group scheme locally of finite type over a field).** It is open, a
subgroup, and geometrically irreducible. SGA 3, VI_A 2.4; Stacks, Tag 0B7R; Kleiman 9.5.1 (locators
UNVERIFIED). -/
def IdentityComponentLFT : Prop :=
  ∀ (K : Type) [Field K] (G : Over (Spec (CommRingCat.of K))) [GrpObj G], LocallyOfFiniteType G.hom →
    ∃ V : G.left.Opens, (V : Set G.left) = identityComponent G ∧
      (∀ z : (G ⊗ G).left, (CartesianMonoidalCategory.fst G G).left z ∈ V →
        (CartesianMonoidalCategory.snd G G).left z ∈ V → μ[G].left z ∈ V) ∧
      (∀ g : G.left, g ∈ V → ((𝟙 G)⁻¹ : G ⟶ G).left g ∈ V) ∧
      GeometricallyIrreducible (V.ι ≫ G.hom)

/-- **LEAF? (Z3a, `Pic⁰_{A/K}` is smooth).** The identity component of the Picard scheme of an abelian variety is
smooth over `K`. Mumford §13 (over `k̄`: `Â = Pic⁰`, `dim Â = h¹(𝒪) = g`); over `K`: Kleiman 9.5.1 and descent;
BLR 8.4 / Milne 1986 §10 may print it in one statement (pending reading; locators UNVERIFIED). -/
def PicZeroSmooth : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (P : Over (Spec (CommRingCat.of K)))
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P) (V : P.left.Opens),
    letI := picardFunctorCommGrpObj A.X.hom rep
    (V : Set P.left) = identityComponent P → Smooth (V.ι ≫ P.hom)

/-- **LEAF (Z3b, `Pic⁰_{X/K}` is proper).** For `X` proper and geometrically normal over `K`, the identity
component of `Pic_{X/K}` is proper. Kleiman, *The Picard scheme*, Thm 9.5.4 (locator UNVERIFIED). Instance for
an abelian variety. -/
def PicZeroProper : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (P : Over (Spec (CommRingCat.of K)))
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P) (V : P.left.Opens),
    letI := picardFunctorCommGrpObj A.X.hom rep
    (V : Set P.left) = identityComponent P → IsProper (V.ι ≫ P.hom)

/-! ## Glue -/

section OpenSub

variable {K : Type} [Field K] {P : Over (Spec (CommRingCat.of K))} (V : P.left.Opens)

/-- The open subscheme on `V` as a `K`-scheme. -/
abbrev subX : Over (Spec (CommRingCat.of K)) := Over.mk (V.ι ≫ P.hom)

/-- Its inclusion. -/
abbrev subι : subX V ⟶ P := Over.homMk V.ι rfl

instance : Mono (subι V) := by
  constructor
  intro T g h e
  apply Over.OverMorphism.ext
  exact (cancel_mono V.ι).1 (congrArg Over.Hom.left e)

/-- Lift through the open subscheme. -/
lemma range_sub {T : Over (Spec (CommRingCat.of K))} (f : T ⟶ P) (h : ∀ t, f.left t ∈ V) :
    Set.range f.left ⊆ Set.range V.ι := by
  rw [Scheme.Opens.range_ι]
  rintro _ ⟨t, rfl⟩
  exact h t

def liftV {T : Over (Spec (CommRingCat.of K))} (f : T ⟶ P) (h : ∀ t, f.left t ∈ V) : T ⟶ subX V :=
  Over.homMk (IsOpenImmersion.lift V.ι f.left (range_sub V f h))
    (by
      change IsOpenImmersion.lift V.ι f.left _ ≫ V.ι ≫ P.hom = T.hom
      rw [← Category.assoc, IsOpenImmersion.lift_fac, Over.w])

lemma liftV_comp {T : Over (Spec (CommRingCat.of K))} (f : T ⟶ P) (h : ∀ t, f.left t ∈ V) :
    liftV V f h ≫ subι V = f :=
  Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ _)

end OpenSub

/-- **`PicZeroAbVar` from four statements**: the Picard scheme is locally of finite type (Kleiman 9.4.8), the
identity component of a group scheme locally of finite type is an open geometrically irreducible subgroup (SGA 3
VI_A 2.4), and `Pic⁰` is smooth and proper. -/
theorem picZeroAbVar_of_leaves (h1 : PicLocFinType) (h2 : IdentityComponentLFT) (h3a : PicZeroSmooth)
    (h3b : PicZeroProper) : PicZeroAbVar := by
  intro K _ A P rep
  letI := picardFunctorCommGrpObj A.X.hom rep
  obtain ⟨V, hV, hmulV, hinvV, hirr⟩ := h2 K P (h1 K A P rep)
  let j := subι V
  have hmem : ∀ x : P.left, x ∈ identityComponent P → x ∈ V := fun x hx => by
    rw [← SetLike.mem_coe, hV]; exact hx
  have hιV : ∀ y, V.ι y ∈ V := fun y => by
    rw [← SetLike.mem_coe, ← Scheme.Opens.range_ι V]; exact ⟨y, rfl⟩
  -- multiplication
  let pj : subX V ⊗ subX V ⟶ P ⊗ P := CartesianMonoidalCategory.lift
    (CartesianMonoidalCategory.fst (subX V) (subX V) ≫ j) (CartesianMonoidalCategory.snd (subX V) (subX V) ≫ j)
  have hm : ∀ t, (pj ≫ μ[P]).left t ∈ V := fun t => by
    rw [Over.comp_left]
    apply hmulV
    · change (pj ≫ CartesianMonoidalCategory.fst P P).left t ∈ V
      rw [CartesianMonoidalCategory.lift_fst, Over.comp_left, Scheme.Hom.comp_apply]
      exact hιV _
    · change (pj ≫ CartesianMonoidalCategory.snd P P).left t ∈ V
      rw [CartesianMonoidalCategory.lift_snd, Over.comp_left, Scheme.Hom.comp_apply]
      exact hιV _
  let mulY := liftV V (pj ≫ μ[P]) hm
  have hmul : mulY ≫ j = CartesianMonoidalCategory.fst (subX V) (subX V) ≫ j *
      CartesianMonoidalCategory.snd (subX V) (subX V) ≫ j := by
    rw [liftV_comp, CategoryTheory.Hom.mul_def]
  -- unit
  have ho : ∀ t, (η[P]).left t ∈ V := fun t => hmem _ ⟨t, mem_connectedComponent⟩
  let oneY := liftV V η[P] ho
  have hone : oneY ≫ j = η[P] := liftV_comp V _ _
  -- inverse
  have hi : ∀ t, (j ≫ (𝟙 P)⁻¹).left t ∈ V := fun t => by
    rw [Over.comp_left, Scheme.Hom.comp_apply]
    exact hinvV _ (hιV t)
  let invY := liftV V (j ≫ (𝟙 P)⁻¹) hi
  have hinv : invY ≫ j = j⁻¹ := by
    rw [liftV_comp, GrpObj.comp_inv, Category.comp_id]
  letI : GrpObj (subX V) := AVGlue.grpObjOfMono j mulY hmul oneY hone invY hinv
  have hjmon : IsMonHom j := AVGlue.isMonHom_grpObjOfMono j mulY hmul oneY hone invY hinv
  haveI : IsProper (subX V).hom := h3b K A P rep V hV
  haveI : Smooth (subX V).hom := h3a K A P rep V hV
  haveI : GeometricallyReduced (subX V).hom := geometricallyReduced_of_smooth _
  haveI : GeometricallyIrreducible (subX V).hom := hirr
  haveI : GeometricallyIntegral (subX V).hom :=
    GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible _
  refine ⟨AbVar.mk (subX V), j, ?_, ?_, hjmon⟩
  · exact inferInstanceAs (IsOpenImmersion V.ι)
  · change Set.range V.ι = _
    rw [Scheme.Opens.range_ι, hV]

end PicDict
#print axioms PicDict.picZeroAbVar_of_leaves
