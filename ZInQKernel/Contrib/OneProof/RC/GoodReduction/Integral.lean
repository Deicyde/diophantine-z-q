import ZInQKernel.Contrib.OneProof.NeronExtAb
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-! Integral extension and valuative reduction for tex 8476–8479.
The constructions and their use together are on-the-spot glue (c). -/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open scoped MonoidalCategory CategoryTheory.Obj CategoryTheory.MonObj

set_option autoImplicit false

namespace ZInQ.Manuscript.RC.GoodReduction

/-- The generic restriction of schemes over a trait. -/
abbrev generic (R K : Type) [CommRing R] [Field K] [Algebra R K] :=
  Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))

/-- Extend the given generic map along specified identifications of the two
generic fibres. The target is the good group model itself: its mapping property
is already proved in the tree (BLR §1.2 Prop. 8, locator UNVERIFIED). -/
theorem existsUnique_integralMap {R K : Type} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    {X E : Over (Spec (.of R))} [Smooth X.hom] [Smooth E.hom] [IsProper E.hom] [GrpObj E]
    {XK EK : Over (Spec (.of K))}
    (eX : (generic R K).obj X ≅ XK) (eE : (generic R K).obj E ≅ EK)
    (π : XK ⟶ EK) :
    ∃! f : X ⟶ E, (generic R K).map f ≫ eE.hom = eX.hom ≫ π := by
  have hN := NeronExt.isNeronModelOver_of_grpObj R K E
  obtain ⟨f, hf⟩ := hN.2.2.2.2 X |>.surjective (eX.hom ≫ π ≫ eE.inv)
  change (generic R K).map f = eX.hom ≫ π ≫ eE.inv at hf
  have hfe : (generic R K).map f ≫ eE.hom = eX.hom ≫ π := by simp [hf]
  refine ⟨f, hfe, fun g hg => ?_⟩
  exact (hN.2.2.2.2 X).injective ((cancel_mono eE.hom).mp (hg.trans hfe.symm))

/-- Properness gives the integral lift of a generic point over any
valuation ring above the base. Inertness plays no role in this lift. -/
theorem exists_integralPoint {A F : Type} [CommRing A] [IsDomain A] [ValuationRing A]
    [Field F] [Algebra A F] [IsFractionRing A F]
    {X S : Scheme.{0}} (b : X ⟶ S) [IsProper b]
    (s : Spec (.of A) ⟶ S) (x : Spec (.of F) ⟶ X)
    (hx : x ≫ b = Spec.map (CommRingCat.ofHom (algebraMap A F)) ≫ s) :
    ∃ xInt : Spec (.of A) ⟶ X,
      Spec.map (CommRingCat.ofHom (algebraMap A F)) ≫ xInt = x ∧ xInt ≫ b = s := by
  have hb : IsProper b := inferInstance
  rw [IsProper.eq_valuativeCriterion] at hb
  let D : ValuativeCommSq b := { R := A, K := F, i₁ := x, i₂ := s, commSq := ⟨hx⟩ }
  have hD := (ValuativeCriterion.existence hb.1.1.1) D
  obtain ⟨⟨l, hl, hr⟩⟩ := hD.exists_lift
  exact ⟨l, hl, hr⟩

set_option synthInstance.maxHeartbeats 250000 in
/-- Transport a generic signed relation written in the group of
morphisms to the elliptic model. Base change preserves multiplication
and integer powers of morphisms into a group object. The morphism `c`
can be the constant given by the image of the moved integral cusp. -/
theorem integralAffine_baseChange {R K : Type} [CommRing R] [Field K] [Algebra R K]
    {X E : Over (Spec (.of R))} [Smooth X.hom] [GrpObj E]
    (hN : CToPrinted.IsNeronModelOver R K E)
    (f : X ⟶ E) (W : X ⟶ X) (c : X ⟶ E) (ε : ℤ)
    (hgen : (generic R K).map W ≫ (generic R K).map f =
      ((generic R K).map f) ^ ε * (generic R K).map c)
    {T : Scheme.{0}} (k : T ⟶ Spec (.of R)) :
    (Over.pullback k).map W ≫ (Over.pullback k).map f =
      ((Over.pullback k).map f) ^ ε * (Over.pullback k).map c := by
  have h : W ≫ f = f ^ ε * c := by
    apply (hN.2.2.2.2 X).injective
    let _ : GrpObj ((generic R K).obj E) := Functor.grpObjObj (F := generic R K)
    let φ := (generic R K).homMonoidHom (X := X) (M := E)
    change φ (W ≫ f) = φ (f ^ ε * c)
    rw [map_mul φ, map_zpow φ]
    simpa only [φ, Functor.homMonoidHom_apply, Functor.map_comp] using hgen
  let _ : GrpObj ((Over.pullback k).obj E) := Functor.grpObjObj (F := Over.pullback k)
  let ψ := (Over.pullback k).homMonoidHom (X := X) (M := E)
  have hh := congrArg (fun g => ψ g) h
  change ψ (W ≫ f) = ψ (f ^ ε * c) at hh
  rw [map_mul ψ, map_zpow ψ] at hh
  simpa only [ψ, Functor.homMonoidHom_apply, Functor.map_comp] using hh


end ZInQ.Manuscript.RC.GoodReduction
