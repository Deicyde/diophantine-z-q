import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.RingTheory.Etale.Pi

/-!
# Split finite étale covers representing discrete sections

A continuous function to a discrete type specifies the summand of a disjoint
union of copies of the base scheme. The resulting lift over the base is
constructed by gluing on the open fibres of the function.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace ZInQ.Manuscript.T10Proetale

noncomputable section

universe u

variable (U : Scheme.{u}) (I : Type u)

/-- The trivial cover with sheets indexed by `I`. -/
def splitProjection : (∐ fun _ : I => U) ⟶ U :=
  Sigma.desc fun _ => 𝟙 U

/-- A nonempty family of sheets makes the trivial cover surjective. -/
theorem splitProjection_surjective [Nonempty I] : Surjective (splitProjection U I) := by
  constructor
  intro x
  obtain ⟨i⟩ := ‹Nonempty I›
  refine ⟨Sigma.ι (fun _ : I => U) i x, ?_⟩
  change (Sigma.ι _ i ≫ splitProjection U I) x = x
  simp [splitProjection]

private abbrev diagonalAlgebraMap (R : CommRingCat.{u}) :
    R ⟶ CommRingCat.of (I → R) := CommRingCat.ofHom (algebraMap R (I → R))

private lemma splitProjection_spec (R : CommRingCat.{u}) :
    splitProjection (Spec R) I = sigmaSpec (fun _ : I => R) ≫ Spec.map (diagonalAlgebraMap I R) := by
  apply Sigma.hom_ext
  intro i
  rw [splitProjection, Sigma.ι_comp_desc, ι_sigmaSpec_assoc, ← Spec.map_comp]
  have eq : diagonalAlgebraMap I R ≫ CommRingCat.ofHom (Pi.evalRingHom (fun _ : I => R) i) = 𝟙 R :=
    rfl
  rw [eq, Spec.map_id]

/-- An affine split cover with finitely many sheets is finite. -/
theorem splitProjection_spec_finite (R : CommRingCat.{u}) [Finite I] :
    IsFinite (splitProjection (Spec R) I) := by
  have : IsFinite (Spec.map (diagonalAlgebraMap I R)) :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  rw [splitProjection_spec]
  infer_instance

/-- An affine split cover with finitely many sheets is étale. -/
theorem splitProjection_spec_etale (R : CommRingCat.{u}) [Finite I] :
    Etale (splitProjection (Spec R) I) := by
  have : Etale (Spec.map (diagonalAlgebraMap I R)) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr inferInstance)
  rw [splitProjection_spec]
  infer_instance

variable [TopologicalSpace I] [DiscreteTopology I]

/-- Read the sheet of a point of the split cover. -/
def splitSheet : C((∐ fun _ : I => U : Scheme), I) :=
  ⟨fun y => ((sigmaMk (fun _ : I => U)).symm y).1,
    (continuous_sigma fun _ => continuous_const).comp (sigmaMk (fun _ : I => U)).symm.continuous⟩

omit [DiscreteTopology I] in
private lemma splitSheet_ι (i : I) (x : U) :
    splitSheet U I (Sigma.ι (fun _ : I => U) i x) = i := by
  change ((sigmaMk (fun _ : I => U)).symm (Sigma.ι (fun _ : I => U) i x)).1 = i
  rw [← sigmaMk_mk, Homeomorph.symm_apply_apply]

variable {U I} {Y : Scheme.{u}} (g : Y ⟶ U) (f : C(Y, I))

private abbrev fibreOpen (i : I) : Y.Opens :=
  ⟨f ⁻¹' {i}, (isOpen_discrete _).preimage f.continuous⟩

private abbrev fibreCover : Y.OpenCover where
  I₀ := I
  X i := fibreOpen f i
  f i := (fibreOpen f i).ι
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨fun y => ⟨f y, ⟨⟨y, rfl⟩, rfl⟩⟩, fun _ => inferInstance⟩

private lemma fibreLift_compatible (i j : I) :
    pullback.fst ((fibreCover f).f i) ((fibreCover f).f j) ≫
        (fibreCover f).f i ≫ g ≫ Sigma.ι (fun _ : I => U) i =
      pullback.snd ((fibreCover f).f i) ((fibreCover f).f j) ≫
        (fibreCover f).f j ≫ g ≫ Sigma.ι (fun _ : I => U) j := by
  by_cases h : i = j
  · subst j
    rw [pullback.condition_assoc]
  · have he : IsEmpty (↑(pullback ((fibreCover f).f i) ((fibreCover f).f j)) : Type u) := by
      constructor
      intro x
      let p : pullback ((fibreCover f).f i) ((fibreCover f).f j) ⟶ (fibreCover f).X i := pullback.fst _ _
      let q : pullback ((fibreCover f).f i) ((fibreCover f).f j) ⟶ (fibreCover f).X j := pullback.snd _ _
      have eq := congrArg (fun a : pullback ((fibreCover f).f i) ((fibreCover f).f j) ⟶ Y =>
        f (a x)) (pullback.condition (f := (fibreCover f).f i) (g := (fibreCover f).f j))
      exact h ((p x).2.symm.trans (eq.trans (q x).2))
    exact isInitialOfIsEmpty.hom_ext _ _

set_option maxHeartbeats 400000 in
/-- The scheme map over the base obtained by assigning a sheet on each open fibre. -/
def splitLift : Y ⟶ (∐ fun _ : I => U) :=
  (fibreCover f).glueMorphisms (fun i => (fibreCover f).f i ≫ g ≫ Sigma.ι (fun _ : I => U) i)
    (fibreLift_compatible g f)

private lemma splitLift_restrict (i : I) :
    (fibreCover f).f i ≫ splitLift g f = (fibreCover f).f i ≫ g ≫ Sigma.ι (fun _ : I => U) i :=
  (fibreCover f).ι_glueMorphisms _ _ i

/-- The lift projects to the original map to the base. -/
theorem splitLift_projection : splitLift g f ≫ splitProjection U I = g := by
  apply (fibreCover f).hom_ext
  intro i
  rw [← Category.assoc, splitLift_restrict]
  simp [splitProjection]

/-- Reading the sheet of the glued scheme map recovers the continuous function. -/
theorem splitLift_sheet (y : Y) : splitSheet U I (splitLift g f y) = f y := by
  let z : (fibreCover f).X (f y) := ⟨y, rfl⟩
  have hz := congrArg (fun a : (fibreCover f).X (f y) ⟶ (∐ fun _ : I => U) => a z)
    (splitLift_restrict g f (f y))
  change splitLift g f y = Sigma.ι (fun _ : I => U) (f y) (g y) at hz
  rw [hz, splitSheet_ι]

/-- A map over the base is determined by its sheet at each point. -/
theorem splitLift_unique (h : Y ⟶ (∐ fun _ : I => U)) (hg : h ≫ splitProjection U I = g)
    (hf : ∀ y, splitSheet U I (h y) = f y) : h = splitLift g f := by
  apply (fibreCover f).hom_ext
  intro i
  rw [splitLift_restrict]
  have hr : Set.range ((fibreCover f).f i ≫ h) ⊆ Set.range (Sigma.ι (fun _ : I => U) i) := by
    rintro _ ⟨z, rfl⟩
    let p := (sigmaMk (fun _ : I => U)).symm (h ((fibreCover f).f i z))
    have hi : p.1 = i := (hf ((fibreCover f).f i z)).trans z.2
    refine ⟨p.2, ?_⟩
    have hp : (⟨i, p.2⟩ : Σ _ : I, U) = p := Sigma.ext hi.symm (by rfl)
    rw [← sigmaMk_mk, hp]
    exact (sigmaMk (fun _ : I => U)).apply_symm_apply _
  let a := IsOpenImmersion.lift (Sigma.ι (fun _ : I => U) i) ((fibreCover f).f i ≫ h) hr
  have ha : a ≫ Sigma.ι (fun _ : I => U) i = (fibreCover f).f i ≫ h :=
    IsOpenImmersion.lift_fac _ _ _
  have eq : a = (fibreCover f).f i ≫ g := by
    rw [← hg, ← Category.assoc, ← ha, Category.assoc, splitProjection, Sigma.ι_comp_desc, Category.comp_id]
  rw [← ha, eq, Category.assoc]

/-- Sections of the split cover over any test scheme are exactly the continuous
functions from that scheme to its discrete set of sheets. -/
def splitSections :
    {h : Y ⟶ (∐ fun _ : I => U) // h ≫ splitProjection U I = g} ≃ C(Y, I) where
  toFun h := (splitSheet U I).comp ⟨h.val, h.val.continuous⟩
  invFun f := ⟨splitLift g f, splitLift_projection g f⟩
  left_inv h := Subtype.ext (splitLift_unique g _ h.val h.2 (fun _ => rfl)).symm
  right_inv f := ContinuousMap.ext (splitLift_sheet g f)

/-- The identification is natural under precomposition in the test scheme. -/
theorem splitSections_restrict {Z : Scheme.{u}} (k : Z ⟶ Y)
    (h : {h : Y ⟶ (∐ fun _ : I => U) // h ≫ splitProjection U I = g}) :
    splitSections (I := I) (k ≫ g) ⟨k ≫ h.val, by rw [Category.assoc, h.2]⟩ =
      (splitSections g h).comp ⟨k, k.continuous⟩ := rfl

end
end ZInQ.Manuscript.T10Proetale
