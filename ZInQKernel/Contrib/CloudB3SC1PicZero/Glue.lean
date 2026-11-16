import ZInQKernel.Contrib.CloudB3SC1PicZero.Leaves
import ZInQKernel.Contrib.SmoothFibre.Basic
import ZInQKernel.Contrib.AbVarBC.Dim

/-! # Glue for `T09Pic.PicZeroAbVar` from Kleiman's statements (proved)

The open-subgroup construction (`subX`, `subι`, `liftV`), `isReduced_of_smooth_field`,
`geometricallyReduced_of_smooth` and the body of `picZeroAbVar_of_kleiman` are adapted from this project's
task pic-dict (`ZInQKernel/Contrib/OneProof/PicDictionary.lean` on the branch `wip/pic-dict`, commit
4e95795b, theorem `PicDict.picZeroAbVar_of_leaves`); the changes are the leaf names and the projectivity and
geometric-connectedness steps below. -/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory
open scoped CategoryTheory.MonObj

namespace CloudB3SC1PicZero

open T09Pic PkgI3 PkgI3.AbVar

/-- A scheme smooth over a field is reduced. (pic-dict) -/
theorem isReduced_of_smooth_field {X : Scheme.{0}} {L : Type} [Field L]
    (f : X ⟶ Spec (CommRingCat.of L)) [Smooth f] : IsReduced X := by
  have : ∀ i, IsReduced (X.affineCover.X i) := fun i => by
    let g := X.affineCover.f i ≫ f
    have : Smooth g := inferInstance
    have hs := g.smooth_appLE (isAffineOpen_top (Spec (CommRingCat.of L)))
      (isAffineOpen_top (X.affineCover.X i)) le_top
    let φ : L →+* Γ(X.affineCover.X i, ⊤) :=
      (g.appLE ⊤ ⊤ le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of L)).inv.hom
    have hφ : φ.Smooth := by
      refine RingHom.Smooth.comp ?_ hs
      exact RingHom.Smooth.of_bijective (ConcreteCategory.bijective_of_isIso _)
    let := φ.toAlgebra
    have : Algebra.Smooth L Γ(X.affineCover.X i, ⊤) := hφ
    have : _root_.IsReduced Γ(X.affineCover.X i, ⊤) :=
      ZInQ.SmoothFibre.isReduced_of_smooth_of_field L _
    exact isReduced_of_isAffine_isReduced _
  exact IsReduced.of_openCover (X := X) X.affineCover

/-- Smooth morphisms are geometrically reduced. (pic-dict) -/
theorem geometricallyReduced_of_smooth {X Y : Scheme.{0}} (f : X ⟶ Y) [Smooth f] :
    GeometricallyReduced f := by
  rw [GeometricallyReduced.eq_geometrically]
  intro K _ y Z fst snd h
  have : Smooth snd := MorphismProperty.of_isPullback (P := @Smooth) h inferInstance
  exact isReduced_of_smooth_field snd

/-- Geometrically irreducible morphisms are geometrically connected (an irreducible space is connected). -/
theorem geometricallyConnected_of_geometricallyIrreducible {X Y : Scheme.{0}} (f : X ⟶ Y)
    [h : GeometricallyIrreducible f] : GeometricallyConnected f :=
  ⟨fun _K _ y _Z fst snd hp =>
    have := h.geometrically_irreducibleSpace y fst snd hp
    inferInstance⟩

/-- **An abelian variety is projective**: a closed immersion into `ℙ^N_K` over `K` (the vendored
`GrpObj.exists_isImmersion_projectiveSpace_of_smooth_of_geometricallyIntegral` gives an immersion; it is proper
since `A` is proper and `ℙ^N_K` is separated, so its image is closed). -/
theorem exists_isClosedImmersion_projectiveSpace {K : Type} [Field K] (A : AbVar K) :
    ∃ (N : Type) (_ : Finite N) (i : A.X.left ⟶ ℙ(N; Spec (CommRingCat.of K))),
      IsClosedImmersion i ∧ i ≫ ℙ(N; Spec (CommRingCat.of K)) ↘ Spec (CommRingCat.of K) = A.X.hom := by
  obtain ⟨N, hN, i, hi, hover⟩ :=
    GrpObj.exists_isImmersion_projectiveSpace_of_smooth_of_geometricallyIntegral A.X
  refine ⟨N, hN, i, ?_, hover⟩
  have := hN
  have := hi
  have : IsProper (i ≫ ℙ(N; Spec (CommRingCat.of K)) ↘ Spec (CommRingCat.of K)) := by
    rw [hover]; infer_instance
  have : IsProper i := IsProper.of_comp i (ℙ(N; Spec (CommRingCat.of K)) ↘ Spec (CommRingCat.of K))
  exact .of_isPreimmersion i i.isClosedMap.isClosed_range

section OpenSub

variable {K : Type} [Field K] {P : Over (Spec (CommRingCat.of K))} (V : P.left.Opens)

/-- The open subscheme on `V` as a `K`-scheme. (pic-dict) -/
abbrev subX : Over (Spec (CommRingCat.of K)) := Over.mk (V.ι ≫ P.hom)

/-- Its inclusion. (pic-dict) -/
abbrev subι : subX V ⟶ P := Over.homMk V.ι rfl

instance : Mono (subι V) := by
  constructor
  intro T g h e
  apply Over.OverMorphism.ext
  exact (cancel_mono V.ι).1 (congrArg Over.Hom.left e)

lemma range_sub {T : Over (Spec (CommRingCat.of K))} (f : T ⟶ P) (h : ∀ t, f.left t ∈ V) :
    Set.range f.left ⊆ Set.range V.ι := by
  rw [Scheme.Opens.range_ι]
  rintro _ ⟨t, rfl⟩
  exact h t

/-- Lift through the open subscheme. (pic-dict) -/
def liftV {T : Over (Spec (CommRingCat.of K))} (f : T ⟶ P) (h : ∀ t, f.left t ∈ V) : T ⟶ subX V :=
  Over.homMk (IsOpenImmersion.lift V.ι f.left (range_sub V f h))
    (by
      change IsOpenImmersion.lift V.ι f.left _ ≫ V.ι ≫ P.hom = T.hom
      rw [← Category.assoc, IsOpenImmersion.lift_fac, Over.w])

lemma liftV_comp {T : Over (Spec (CommRingCat.of K))} (f : T ⟶ P) (h : ∀ t, f.left t ∈ V) :
    liftV V f h ≫ subι V = f :=
  Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ _)

end OpenSub

/-- **`T09Pic.PicZeroAbVar` from Kleiman 9.4.8 (1), 9.5.1 (3) and 9.5.24.** For a representing object `P` of
`Pic_{A/K}`: `P` is locally of finite type (9.4.8), so its identity component is an open geometrically irreducible
subgroup `V` (9.5.1); `A` has finite dimension `g` (`PkgI3.AbVar.dim_finite`, proved) and is projective, so `V` is
smooth and proper (9.5.24); smooth gives geometrically reduced, so `V` with the
induced group law is an abelian variety and its inclusion is an open immersion onto the identity component and a
homomorphism. (Body adapted from pic-dict's `picZeroAbVar_of_leaves`.) -/
theorem picZeroAbVar_of_kleiman (h948 : KleimanThm948Field) (h951 : KleimanLem951)
    (h9524 : KleimanRmk9524Field) : PicZeroAbVar := by
  intro K _ A P rep
  let := picardFunctorCommGrpObj A.X.hom rep
  have hproj := exists_isClosedImmersion_projectiveSpace A
  have hlft : LocallyOfFiniteType P.hom := h948 K A.X hproj inferInstance inferInstance P rep
  obtain ⟨V, hV, hmulV, hinvV, hirr⟩ := h951 K P hlft
  obtain ⟨g, hg⟩ := A.dim_finite
  obtain ⟨hsm, hpr⟩ := h9524 K A.X inferInstance inferInstance
    (geometricallyConnected_of_geometricallyIrreducible A.X.hom) g hg hproj P rep V hV
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
  let : GrpObj (subX V) := AVGlue.grpObjOfMono j mulY hmul oneY hone invY hinv
  have hjmon : IsMonHom j := AVGlue.isMonHom_grpObjOfMono j mulY hmul oneY hone invY hinv
  have : IsProper (subX V).hom := hpr
  have : Smooth (subX V).hom := hsm
  have : GeometricallyReduced (subX V).hom := geometricallyReduced_of_smooth _
  have : GeometricallyIrreducible (subX V).hom := hirr
  have : GeometricallyIntegral (subX V).hom :=
    GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible _
  refine ⟨AbVar.mk (subX V), j, ?_, ?_, hjmon⟩
  · exact inferInstanceAs (IsOpenImmersion V.ι)
  · change Set.range V.ι = _
    rw [Scheme.Opens.range_ι, hV]

end CloudB3SC1PicZero
