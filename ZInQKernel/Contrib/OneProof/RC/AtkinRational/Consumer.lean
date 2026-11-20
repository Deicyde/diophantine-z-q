import ZInQKernel.Contrib.OneProof.RC.AtkinRational.Difference
import Mathlib.CategoryTheory.Monoidal.Grp

/-! Read the generic equation as a relation in `Over`, as required by
`GoodReduction.atkinQuotient_of_integralRelation`. The comparison with
a supplied group model is on the spot (c), tex 8487–8489. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits UpperHalfPlane WeierstrassCurve CartesianMonoidalCategory
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CST
open scoped Classical MonoidalCategory CategoryTheory.Obj CategoryTheory.MonObj TauCeti.ExactDivisor
open ZInQ.Manuscript.RC.PreparedParam ZInQ.Manuscript.RC.AtkinPin

namespace ZInQ.Manuscript.RC.AtkinRational

/-- Equality after a dominant field point detects equality of group-valued
morphisms. The point reading only needs to be compatible and faithful at
that field. -/
theorem overRelation_of_dominantPoint
    {S : Scheme.{0}} {M G A : Over S} [IsReduced M.left] [IsSeparated G.hom] [GrpObj G]
    (x : A ⟶ M) [IsDominant x.left]
    {T : Type} [Group T] (read : (A ⟶ G) →* T) (hf : Function.Injective read)
    (W : M ⟶ M) (π t : M ⟶ G) (e : ℤ)
    (h : read (x ≫ W ≫ π) = read (x ≫ π) ^ e * read (x ≫ t)) :
    W ≫ π = π ^ e * t := by
  have hx : x ≫ (W ≫ π) = x ≫ (π ^ e * t) := by
    apply hf
    simpa only [MonObj.comp_mul, GrpObj.comp_zpow, map_mul, map_zpow] using h
  ext1
  exact ext_of_isDominant_of_isSeparated G.hom ((Over.w _).trans (Over.w _).symm) x.left
    (congrArg (fun u : A ⟶ G => u.left) hx)

/-- On the identified rational generic fibre, the translated point formula
is the morphism relation used for integral specialization. The supplied
reading compares the group law of that model with the fixed Weierstrass
point type; the constant is read at the image of the moved cusp. -/
theorem overRelationAtScale {N Q : ℕ} [NeZero N]
    {E : WeierstrassCurve ℚ} [E.IsElliptic]
    (f : HeckeRing.GL2.Newform N 2) (hχ : f.χ = 1) (hQ : Q ∥ N)
    (Lat : PeriodPair) (κ : ℂ) (hLat : IsLatticeOf E Lat)
    (π : (X0Branch.model N).X ⟶ Proj E.toProjective.grading)
    (hπ : π ≫ projectiveOverQ E = (X0Branch.model N).overQ)
    (hscale : ∀ τ : ℍ, projectiveValue (((X0Branch.model N).complexPoint τ).comp π hπ).val =
      phiAn E (f.toCuspFormGamma0 hχ) Lat κ τ)
    (hzero : projectiveValue ((infinityPoint N).comp π hπ).val = 0)
    {G : Over (Spec (.of ℚ))} [GrpObj G] [IsSeparated G.hom]
    (j : G.left ⟶ Proj E.toProjective.grading) [Mono j]
    (φ t : Over.mk (X0Branch.model N).overQ ⟶ G) (hφ : φ.left ≫ j = π)
    (ht : t.left ≫ j = (X0Branch.model N).overQ ≫ (infinityPoint N).val ≫ (rationalAtkin hQ).hom ≫ π)
    (read : (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℚ ℂ))) ⟶ G) →*
      Multiplicative (E.baseChange ℂ).toAffine.Point)
    (hread : ∀ a, (read a).toAdd = projectiveValue (a.left ≫ j)) :
    Over.homMk (rationalAtkin hQ).hom (rationalAtkin hQ).overQ ≫ φ = φ ^ (signUnit f hχ hQ : ℤ) * t := by
  let e := (signUnit f hχ hQ : ℤ)
  have h := basedAtkinAtScale f hχ hQ Lat κ hLat π hπ hscale hzero
  obtain ⟨τ, hτ⟩ := exists_dominant_chart N
  let X := X0Branch.model N
  let x := X.complexPoint τ
  let xo : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℚ ℂ))) ⟶ Over.mk X.overQ :=
    Over.homMk x.val x.property
  have : IsIntegral (Over.mk X.overQ).left := X.integral
  have : IsReduced (Over.mk X.overQ).left := inferInstance
  have : IsDominant xo.left := hτ
  refine overRelation_of_dominantPoint xo read ?_ _ _ _ _ ?_
  · intro a b hab
    have hh := congrArg Multiplicative.toAdd hab
    rw [hread, hread] at hh
    have hm := projectiveValue_injective_of_origin E ((infinityPoint N).comp π hπ).val hzero hh
    ext1
    exact (cancel_mono j).mp hm
  · change (read (xo ≫ _ ≫ φ)).toAdd = e • (read (xo ≫ φ)).toAdd + (read (xo ≫ t)).toAdd
    simp only [hread, Over.comp_left, Category.assoc, hφ, ht]
    change projectiveValue (x.val ≫ (rationalAtkin hQ).hom ≫ π) =
      e • projectiveValue (x.val ≫ π) + projectiveValue
        (x.val ≫ X.overQ ≫ (infinityPoint N).val ≫ (rationalAtkin hQ).hom ≫ π)
    rw [← Category.assoc x.val X.overQ, x.property]
    have hh := translatedAtkinAtInfinity (rationalAtkin hQ) π hπ e h hzero ℂ x
    let c := (((infinityPoint N).comp (rationalAtkin hQ).hom (rationalAtkin hQ).overQ).comp π hπ).val
    have hi : (Algebra.ofId ℚ ℂ).toRingHom = algebraMap ℚ ℂ := RingHom.ext_rat _ _
    calc
      _ = e • projectiveValue (x.val ≫ π) +
          Affine.Point.map (W' := E.toAffine) (Algebra.ofId ℚ ℂ) (projectiveValue c) := by
        simpa only [c, FieldPoint.comp, Category.assoc] using hh
      _ = _ := congrArg (fun z => e • projectiveValue (x.val ≫ π) + z) (by
        have hm := projectiveValue_map (E := E) (Algebra.ofId ℚ ℂ) c
        simp only [c, FieldPoint.comp, Category.assoc, hi] at hm
        exact hm)

set_option synthInstance.maxHeartbeats 250000 in
/-- Base change of the relation has the form required on the generic
fibre over the chosen field of the integral model. -/
theorem overRelation_baseChange {S T : Scheme.{0}} (k : T ⟶ S)
    {M G : Over S} [GrpObj G] (W : M ⟶ M) (π t : M ⟶ G) (e : ℤ)
    (h : W ≫ π = π ^ e * t) :
    letI := Functor.grpObjObj (F := Over.pullback k) (G := G)
    (Over.pullback k).map W ≫ (Over.pullback k).map π =
      ((Over.pullback k).map π) ^ e * (Over.pullback k).map t := by
  let _ : GrpObj ((Over.pullback k).obj G) := Functor.grpObjObj (F := Over.pullback k)
  let read := (Over.pullback k).homMonoidHom (X := M) (M := G)
  have hh := congrArg (fun g => read g) h
  change read (W ≫ π) = read (π ^ e * t) at hh
  rw [map_mul read, map_zpow read] at hh
  simpa only [read, Functor.homMonoidHom_apply, Functor.map_comp] using hh


end ZInQ.Manuscript.RC.AtkinRational
