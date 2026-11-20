import ZInQKernel.Contrib.CloudR2Poincare.L2.QuotientGraph

/-!
# Actual scheme lift into the closed quotient graph

A globally trivial normalized difference family on a REDUCED test scheme
forces image containment in the ORIGINAL global residue locus by genuine
field/fpqc detection. Its reduced induced closed structure then gives an
actual scheme morphism, not just a choice on Ω-points.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory
  CartesianMonoidalCategory MonObj

namespace ZInQ.Contrib.CloudR2Poincare.L2

universe u

/-- Global normalized-family equality on reduced U gives a real U→Γ scheme
factorization. No graph-isomorphism, dual or Picard-representability premise. -/
theorem exists_quotientGraph_lift_of_family_eq_one
    {k : Type u} [Field k] (J B Q : PkgI3.AbVar k)
    (i : PkgI3.AbVar.Hom B J) (L : J.X.left.Pic)
    (P : (pullback B.X.hom Q.X.hom).Pic) (hP : L1.IsNormalizedFamily B Q.X P)
    (U : Over (Spec (.of k))) [AlgebraicGeometry.IsReduced U.left]
    (g : U ⟶ J.X ⊗ Q.X)
    (hF : Scheme.Pic.map (JacobianChallenge.baseChangeMap B.X.hom g)
      (quotientGraphFamily J B Q i L P) = 1) :
    ∃ a : U ⟶ quotientGraph J B Q i L P, a ≫ quotientGraphι J B Q i L P = g := by
  let T := J.X ⊗ Q.X
  letI : IsProper T.hom := abVarProduct_proper J Q
  letI : IsLocallyNoetherian T.left := LocallyOfFiniteType.isLocallyNoetherian T.hom
  have hr : Set.range g.left ⊆ quotientGraphClosed J B Q i L P := by
    rintro y ⟨u, rfl⟩
    let Ω := U.left.residueField u
    let c : CommRingCat.of k ⟶ Ω := Spec.preimage (U.left.fromSpecResidueField u ≫ U.hom)
    letI : Algebra k Ω := c.hom.toAlgebra
    let r : L1.fieldTest k Ω ⟶ U := Over.homMk (U.left.fromSpecResidueField u) (by
      change U.left.fromSpecResidueField u ≫ U.hom = Spec.map c
      exact (Spec.map_preimage _).symm)
    have hpt : Scheme.Pic.map (JacobianChallenge.baseChangeMap B.X.hom (r ≫ g))
        (quotientGraphFamily J B Q i L P) = 1 := by
      rw [JacobianChallenge.baseChangeMap_comp, Scheme.Pic.map_comp, hF, Scheme.Pic.map_one]
    have hm := (fibreTriviality_mem_fieldTest_iff B.X.hom η[B.X].left (L1.groupUnit_over B.X)
      T (quotientGraphFamily J B Q i L P) (quotientGraphFamily_normalized J B Q i L P hP)
      (r ≫ g)).mpr hpt
    change g.left u ∈ (quotientGraphClosed J B Q i L P : Set T.left)
    change g.left ((U.left.fromSpecResidueField u) (IsLocalRing.closedPoint Ω)) ∈
      (quotientGraphClosed J B Q i L P : Set T.left) at hm
    rw [Scheme.fromSpecResidueField_apply] at hm
    exact hm
  obtain ⟨b, hb⟩ := L1.exists_factor_reducedClosedSupport (quotientGraphClosed J B Q i L P) g.left hr
  let a : U ⟶ quotientGraph J B Q i L P := Over.homMk b (by
    change b ≫ (L1.reducedClosedSupportι T.left (quotientGraphClosed J B Q i L P) ≫ T.hom) = U.hom
    rw [← Category.assoc, hb]
    exact Over.w g)
  refine ⟨a, ?_⟩
  apply Over.OverMorphism.ext
  exact hb

/-- The actual embedding/quotient pair B→J×Q lies in Γ as a SCHEME morphism,
from the literal restricted bundle and quotient-descent comparison. -/
theorem exists_B_lift_into_quotientGraph
    {k : Type u} [Field k] (J B Q : PkgI3.AbVar k) (i : PkgI3.AbVar.Hom B J)
    (L : J.X.left.Pic) (M : B.X.left.Pic) (hM : M = Scheme.Pic.map i.hom.left L)
    (q : PkgI3.AbVar.Hom B Q) (P : (pullback B.X.hom Q.X.hom).Pic)
    (hP : L1.IsNormalizedFamily B Q.X P)
    (hp : Scheme.Pic.map (JacobianChallenge.baseChangeMap B.X.hom q.hom) P =
      L1.normalizedPolarizationFamily B.X M (𝟙 B.X)) :
    ∃ a : B.X ⟶ quotientGraph J B Q i L P,
      a ≫ quotientGraphι J B Q i L P = lift i.hom q.hom := by
  letI : IsIntegral B.X.left := GeometricallyIntegral.isIntegral_of_subsingleton B.X.hom
  apply exists_quotientGraph_lift_of_family_eq_one J B Q i L P hP B.X (lift i.hom q.hom)
  rw [quotientGraphFamily_pair]
  have hr := normalizedPolarizationFamily_pullback i.hom L (𝟙 B.X)
  rw [Category.id_comp] at hr
  rw [hr, ← hM, hp, _root_.mul_inv_cancel]

end ZInQ.Contrib.CloudR2Poincare.L2
