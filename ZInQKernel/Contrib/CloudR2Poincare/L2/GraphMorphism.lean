import ZInQKernel.Contrib.CloudR2Poincare.L2.GraphPointBijection
import ZInQKernel.Contrib.CloudR2Poincare.L2.GraphSchemeLift
import ZInQKernel.Contrib.CloudR2Poincare.L2.GraphProjectionCriterion
import ZInQKernel.Contrib.CloudR2Poincare.L2.PointedHom

/-!
# INTERNAL graph-projection morphism and pointed homomorphism

The graph and its all-Ω point bijectivity are genuinely constructed. The
standard generic normal-projection criterion is an explicit named ordinary
input until its native endpoint proof is supplied; no graph-isomorphism Fact.
The B→Γ lift is a genuine scheme morphism, so φ∘i=q is proved as a categorical
equality, not inferred from a rational-point choice.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory
  CartesianMonoidalCategory MonObj

namespace ZInQ.Contrib.CloudR2Poincare.L2

/-- INTERNAL: the actual graph gives an extension homomorphism. The only
geometric endpoint input is the independently labelled generic normality
criterion, never a desired extension/PolarizationRetract hypothesis. -/
theorem exists_polarization_extension_of_graph_inputs
    (hB2 : L3.PicZeroPointSurjectivity.{0}) (hSquare : NativeTheoremOfTheSquare.{0})
    (hGeometry : NativeNormalGraphProjectionCriterion)
    {k : Type} [Field k] [CharZero k] (J B Q : PkgI3.AbVar k)
    (i : PkgI3.AbVar.Hom B J) (L : J.X.left.Pic)
    (M : B.X.left.Modules) [M.IsInvertible] (hM : VeryAmple B.X.hom M)
    (hMclass : Scheme.Pic.mk M = Scheme.Pic.map i.hom.left L)
    (H : L1.FiniteStabilizerScheme B (Scheme.Pic.mk M))
    (q : PkgI3.AbVar.Hom B Q) [IsFinite q.hom.left] [Surjective q.hom.left]
    (hk : IsPullback ((fst H.K B.X ≫ H.j) * snd H.K B.X) (snd H.K B.X) q.hom q.hom)
    (P : (pullback B.X.hom Q.X.hom).Pic) (hP : L1.IsNormalizedFamily B Q.X P)
    (hp : Scheme.Pic.map (JacobianChallenge.baseChangeMap B.X.hom q.hom) P =
      L1.normalizedPolarizationFamily B.X (Scheme.Pic.mk M) (𝟙 B.X)) :
    ∃ φ : PkgI3.AbVar.Hom J Q, i.hom ≫ φ.hom = q.hom := by
  let G := quotientGraph J B Q i L P
  let j : G ⟶ J.X ⊗ Q.X := quotientGraphι J B Q i L P
  let p : G ⟶ J.X := j ≫ fst J.X Q.X
  let r : G ⟶ Q.X := j ≫ snd J.X Q.X
  letI : IsProper p.left := quotientGraph_projection_isProper J B Q i L P
  letI : IsIso p := hGeometry J G p (by
    intro Ω _ _ _ _
    exact quotientGraph_fieldPoint_projection_bijective hB2 hSquare J B Q i L M hM H q hk P hP hp)
  obtain ⟨a, ha⟩ := exists_B_lift_into_quotientGraph J B Q i L (Scheme.Pic.mk M) hMclass q P hP hp
  have hap : a ≫ p = i.hom := by
    dsimp only [p, j]
    rw [← Category.assoc, ha, lift_fst]
  have har : a ≫ r = q.hom := by
    dsimp only [r, j]
    rw [← Category.assoc, ha, lift_snd]
  let f : J.X ⟶ Q.X := inv p ≫ r
  have hfi : i.hom ≫ f = q.hom := by
    rw [← hap]
    dsimp only [f]
    rw [Category.assoc, IsIso.hom_inv_id_assoc]
    exact har
  have hf0 : η[J.X] ≫ f = η[Q.X] := by
    rw [← IsMonHom.one_hom i.hom, Category.assoc, hfi, IsMonHom.one_hom q.hom]
  refine ⟨homOfPointed f hf0, ?_⟩
  simpa only [homOfPointed_hom] using hfi

end ZInQ.Contrib.CloudR2Poincare.L2
