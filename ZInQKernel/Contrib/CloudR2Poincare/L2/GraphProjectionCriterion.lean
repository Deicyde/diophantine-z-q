import ZInQKernel.Contrib.CloudR2Poincare.L2.KernelFibres
import ZInQKernel.Contrib.CloudR2Poincare.L1.DualInterface
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective

/-!
# Generic normality/characteristic-zero graph-projection criterion

The reduced closed graph is proper and its geometric field points are proved
bijective by B2/quotient classes. The standard finite/birational/normal endpoint
is kept as an EXPLICIT generic ordinary input until its native proof is banked.
It mentions no Picard, quotient, complement, or desired extension morphism.
No graph-isomorphism Fact or instance is installed by this declaration.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory MonObj

namespace ZInQ.Contrib.CloudR2Poincare.L2

/-- INTERNAL generic geometric input, not a supplied theorem: a reduced proper
scheme over a smooth actual AV, bijective on every algebraically closed field
extension, has isomorphic projection (ZMT + char0 birationality + normality). -/
def NativeNormalGraphProjectionCriterion : Prop :=
  ∀ {k : Type} [Field k] [CharZero k] (J : PkgI3.AbVar k)
    (G : Over (Spec (.of k))) [AlgebraicGeometry.IsReduced G.left]
    (p : G ⟶ J.X) [IsProper p.left],
    (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [CharZero Ω] [Algebra k Ω],
      Function.Bijective (fun a : L1.fieldTest k Ω ⟶ G => a ≫ p)) →
    IsIso p

/-- Actual ZMT part of the criterion, over an algebraically closed base:
point-injectivity makes every rational fibre finite, then proper ⇒ finite. -/
theorem isFinite_of_injective_rationalPoints_to_abVar
    {k : Type} [Field k] [IsAlgClosed k] (J : PkgI3.AbVar k)
    (G : Over (Spec (.of k))) (p : G ⟶ J.X) [IsProper p.left]
    (hp : Function.Injective (fun a : 𝟙_ (Over (Spec (.of k))) ⟶ G => a ≫ p)) :
    IsFinite p.left := by
  letI : IsProper G.hom := by rw [← p.w]; infer_instance
  apply isFinite_of_finite_rational_point_fibres p
  intro y
  have hs : Set.Subsingleton {a : 𝟙_ (Over (Spec (.of k))) ⟶ G | a ≫ p = y} := by
    intro a ha b hb
    exact hp (ha.trans hb.symm)
  exact hs.finite

end ZInQ.Contrib.CloudR2Poincare.L2
