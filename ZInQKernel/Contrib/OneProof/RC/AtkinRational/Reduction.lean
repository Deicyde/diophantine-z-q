import ZInQKernel.Contrib.OneProof.RC.AtkinRational.PointReading
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.GoodReduction
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.IntegralModel
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! Comparison of the fixed Proj point reading with good reduction for
valuation rings containing ℚ. The scheme comparison is on the spot (c):
in the affine chart use the integral coordinates; off it use the origin. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

noncomputable section

open scoped Classical
open AlgebraicGeometry CategoryTheory WeierstrassCurve IsLocalRing
open ZInQ.Contrib.RC53Assist.IsogenyScheme
open ZInQ.Manuscript.RC.PreparedParam

namespace ZInQ.Manuscript.RC.AtkinRational

theorem spec_to_rat {R : Type} [CommRing R] (u v : Spec (.of R) ⟶ Spec (.of ℚ)) :
    u = v := by
  obtain ⟨a, rfl⟩ := Spec.map_surjective u
  obtain ⟨b, rfl⟩ := Spec.map_surjective v
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext_rat a.hom b.hom)

theorem projectiveOverQ_proper (E : WeierstrassCurve ℚ) : IsProper (projectiveOverQ E) := by
  unfold projectiveOverQ
  have := isProper_proj E
  infer_instance

private theorem valuative_ext {E : WeierstrassCurve ℚ}
    {R K : Type} [CommRing R] [IsDomain R] [Field K]
    (a : R →+* K) (ha : Function.Injective a)
    {u w : Spec (.of R) ⟶ Proj E.toProjective.grading}
    (h : Spec.map (CommRingCat.ofHom a) ≫ u = Spec.map (CommRingCat.ofHom a) ≫ w) : u = w := by
  have : IsProper (projectiveOverQ E) := projectiveOverQ_proper E
  have : IsDominant (Spec.map (CommRingCat.ofHom a)) := by
    rw [isDominant_iff]
    apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical a).mpr
    intro x hx
    rw [RingHom.mem_ker, map_eq_zero_iff a ha] at hx
    simp [hx]
  exact ext_of_isDominant_of_isSeparated (projectiveOverQ E) (spec_to_rat _ _)
    (Spec.map (CommRingCat.ofHom a)) h

private theorem read_spec_affine {E : WeierstrassCurve ℚ} [E.IsElliptic]
    {R F : Type} [CommRing R] [Algebra ℚ R] [Field F] [Algebra ℚ F]
    (b : R →ₐ[ℚ] F) (a : E.toAffine.CoordinateRing →ₐ[ℚ] R) :
    projectiveValue (Spec.map (CommRingCat.ofHom b.toRingHom) ≫
      Spec.map (CommRingCat.ofHom a.toRingHom) ≫ ellipticAffineInclusion E) =
    .some (b (a (AdjoinRoot.of E.toAffine.polynomial Polynomial.X)))
      (b (a (AdjoinRoot.root E.toAffine.polynomial)))
      (Affine.equation_iff_nonsingular.mp (Affine.CoordinateRing.equation_of_algHom (b.comp a))) := by
  rw [← Category.assoc, ← Spec.map_comp]
  exact projectiveValue_affine_spec E (b.comp a)

section Valuation

variable {K Γ₀ : Type} [Field K] [Algebra ℚ K] [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation K Γ₀)
    [Algebra ℚ v.valuationSubring] [IsScalarTower ℚ v.valuationSubring K]

private theorem integralModel_eq_baseChange (E : WeierstrassCurve ℚ) :
    have : IsIntegral v.valuationSubring (E.baseChange K) := inferInstance
    integralModel v.valuationSubring (E.baseChange K) = E.baseChange v.valuationSubring := by
  exact integralModel_baseChange_eq_map E

private theorem reducedModel_eq_baseChange (E : WeierstrassCurve ℚ) :
    have : IsIntegral v.valuationSubring (E.baseChange K) := inferInstance
    (integralModel v.valuationSubring (E.baseChange K)).map (residue v.valuationSubring) =
      E.baseChange (ResidueField v.valuationSubring) := by
  dsimp only
  calc
    _ = (E.baseChange v.valuationSubring).map (residue v.valuationSubring) :=
      congrArg (fun W => W.map (residue v.valuationSubring)) (integralModel_eq_baseChange v E)
    _ = _ := E.map_baseChange (IsScalarTower.toAlgHom ℚ v.valuationSubring _)

/-- Good reduction as an additive map between the two readings of the same
rational Weierstrass equation, over the fraction and residue fields. -/
def projectiveReduction (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    (E.baseChange K).toAffine.Point →+
      (E.baseChange (ResidueField v.valuationSubring)).toAffine.Point := by
  have : IsIntegral v.valuationSubring (E.baseChange K) := inferInstance
  have : (integralModel v.valuationSubring (E.baseChange K)).IsElliptic := by
    rw [integralModel_eq_baseChange v]
    infer_instance
  exact (AddEquiv.cast (M := fun W : WeierstrassCurve (ResidueField v.valuationSubring) =>
    W.toAffine.Point) (reducedModel_eq_baseChange v E)).toAddMonoidHom.comp
    (Affine.Point.reductionHom v)

/-- Specialization of a scheme point over a valuation ring agrees with the
good reduction homomorphism on the affine elliptic point type. -/
theorem projectiveValue_specialization (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (o : Spec (.of ℚ) ⟶ Proj E.toProjective.grading) (ho : projectiveValue o = 0)
    (u : Spec (.of v.valuationSubring) ⟶ Proj E.toProjective.grading) :
    projectiveValue (Spec.map (CommRingCat.ofHom (residue v.valuationSubring)) ≫ u) =
      projectiveReduction v E
        (projectiveValue (Spec.map (CommRingCat.ofHom (algebraMap v.valuationSubring K)) ≫ u)) := by
  classical
  let R := v.valuationSubring
  let r : R →ₐ[ℚ] ResidueField R := IsScalarTower.toAlgHom ℚ R _
  let i : R →ₐ[ℚ] K := IsScalarTower.toAlgHom ℚ R _
  let g := Spec.map (CommRingCat.ofHom i.toRingHom)
  let s := Spec.map (CommRingCat.ofHom r.toRingHom)
  change projectiveValue (s ≫ u) = projectiveReduction v E (projectiveValue (g ≫ u))
  have hi : Function.Injective i := Subtype.val_injective
  have : IsIntegral R (E.baseChange K) := inferInstance
  have : (integralModel R (E.baseChange K)).IsElliptic := by
    rw [integralModel_eq_baseChange v]; infer_instance
  cases hgen : projectiveValue (g ≫ u) with
  | zero =>
    change projectiveValue (g ≫ u) = 0 at hgen
    change projectiveValue (s ≫ u) = projectiveReduction v E 0
    rw [map_zero]
    let u₀ := Spec.map (CommRingCat.ofHom (algebraMap ℚ R)) ≫ o
    have hg : g ≫ u₀ = Spec.map (CommRingCat.ofHom (Algebra.ofId ℚ K).toRingHom) ≫ o := by
      change g ≫ Spec.map (CommRingCat.ofHom (algebraMap ℚ R)) ≫ o = _
      rw [← Category.assoc]
      exact congrArg (fun k => k ≫ o) (spec_to_rat _ _)
    have hs : s ≫ u₀ = Spec.map (CommRingCat.ofHom (Algebra.ofId ℚ (ResidueField R)).toRingHom) ≫ o := by
      change s ≫ Spec.map (CommRingCat.ofHom (algebraMap ℚ R)) ≫ o = _
      rw [← Category.assoc]
      exact congrArg (fun k => k ≫ o) (spec_to_rat _ _)
    have hu : u = u₀ := by
      apply valuative_ext i.toRingHom hi
      apply projectiveValue_injective_of_origin E o ho
      rw [hgen, hg, ← projectiveValue_map, ho, map_zero]
    rw [hu, hs, ← projectiveValue_map, ho, map_zero]
  | some x y hxy =>
    by_cases hx : v x ≤ 1
    · let a : R := ⟨x, (v.mem_valuationSubring_iff x).mpr hx⟩
      let b : R := ⟨y, (v.mem_valuationSubring_iff y).mpr
        (Affine.valuation_y_le_one_of_valuation_x_le_one v hxy.1 hx)⟩
      have he : (E.baseChange R).toAffine.Equation a b := by
        apply ((E.baseChange R).toAffine.map_equation (f := i.toRingHom) hi a b).mp
        change ((E.baseChange R).map i.toRingHom).toAffine.Equation x y
        have hi' : (E.baseChange R).map i.toRingHom = E.baseChange K := E.map_baseChange i
        rw [hi']
        exact hxy.1
      let f : E.toAffine.CoordinateRing →ₐ[ℚ] R := Affine.CoordinateRing.evalAlgHom he
      let u₀ := Spec.map (CommRingCat.ofHom f.toRingHom) ≫ ellipticAffineInclusion E
      have hu : u = u₀ := by
        apply valuative_ext i.toRingHom hi
        apply projectiveValue_injective_of_origin E o ho
        rw [hgen]
        change _ = projectiveValue (Spec.map (CommRingCat.ofHom i.toRingHom) ≫
          Spec.map (CommRingCat.ofHom f.toRingHom) ≫ ellipticAffineInclusion E)
        rw [read_spec_affine]
        simp only [f, Affine.CoordinateRing.evalAlgHom_of_X, Affine.CoordinateRing.evalAlgHom_root]
        rfl
      rw [hu]
      change projectiveValue (Spec.map (CommRingCat.ofHom r.toRingHom) ≫
          Spec.map (CommRingCat.ofHom f.toRingHom) ≫ ellipticAffineInclusion E) = _
      rw [read_spec_affine]
      simp only [f, Affine.CoordinateRing.evalAlgHom_of_X, Affine.CoordinateRing.evalAlgHom_root]
      have hns : ((integralModel R (E.baseChange K)).map (residue R)).toAffine.Nonsingular
          (r a) (r b) := by
        rw [reducedModel_eq_baseChange v]
        apply Affine.equation_iff_nonsingular.mp
        have h := he.map r.toRingHom
        change ((E.baseChange R).map r.toRingHom).toAffine.Equation (r a) (r b) at h
        have hr' : (E.baseChange R).map r.toRingHom = E.baseChange (ResidueField R) :=
          E.map_baseChange r
        rw [hr'] at h
        exact h
      change _ = cast (congrArg (fun W => W.toAffine.Point) (reducedModel_eq_baseChange v E))
        (Affine.Point.reductionHom v (.some x y hxy))
      rw [Affine.Point.reductionHom_some_of_valuation_le_one v hxy hx hns,
        Affine.Point.cast_some (reducedModel_eq_baseChange v E)]
      rfl
    · have h0 : projectiveValue (s ≫ u) = 0 := by
        by_contra h0
        have hc : u (closedPoint R) ∈ ellipticAffineOpen E := by
          apply (mem_ellipticAffineOpen_iff E _).2
          apply mt (projectiveValue_eq_zero_iff E (s ≫ u)).2 at h0
          have hs : s (default : Spec (.of (ResidueField R))) = closedPoint R := by
            rw [← Subsingleton.elim (closedPoint (ResidueField R))
                (default : Spec (.of (ResidueField R)))]
            exact IsLocalRing.comap_closedPoint (IsLocalRing.residue R)
          rwa [Scheme.Hom.comp_apply, hs] at h0
        have hU : Set.range u ⊆ ellipticAffineOpen E := by
          have hw := Scheme.preimage_eq_top_of_closedPoint_mem u hc
          rintro _ ⟨p, rfl⟩
          exact show p ∈ u ⁻¹ᵁ ellipticAffineOpen E from hw.ge trivial
        let f := affineRingMap E (ellipticAffineLift E u hU)
        have hu : u = Spec.map (CommRingCat.ofHom f.toRingHom) ≫ ellipticAffineInclusion E := by
          rw [← ellipticAffineLift_fac E u hU]
          congr 1
          apply affineRingMap_injective E
          rw [affineRingMap_Spec]
        rw [hu, read_spec_affine] at hgen
        have he := (Affine.Point.some.inj hgen).1
        exact hx (he ▸ (f (AdjoinRoot.of E.toAffine.polynomial Polynomial.X)).property)
      rw [h0]
      change _ = cast (congrArg (fun W => W.toAffine.Point) (reducedModel_eq_baseChange v E))
        (Affine.Point.reductionHom v (.some x y hxy))
      rw [Affine.Point.reductionHom_some_of_one_lt v hxy (lt_of_not_ge hx),
        Affine.Point.cast_zero (reducedModel_eq_baseChange v E)]

end Valuation


end ZInQ.Manuscript.RC.AtkinRational
