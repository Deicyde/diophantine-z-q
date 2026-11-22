import ZInQKernel.Contrib.CloudR2Poincare.L2.GlobalStabilizerLocus
import ZInQKernel.Contrib.CloudR2Poincare.L2.FiniteClosedStabilizer

/-!
# INTERNAL composition with the exact planned global normalized seesaw

The one unresolved geometric theorem is an EXPLICIT ordinary hypothesis in
this module. Its telescope is exactly L1's ReducedSeesawProbe/planned
normalizedPicardClass_eq_one_of_residueFibres_reduced. It is not a Fact,
instance, axiom, or asserted proof. Once L1 proves it, these compositions need
no further global locus, coverage, ampleness, or finiteness premise.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory MonObj

namespace ZInQ.Contrib.CloudR2Poincare.L2

/-- INTERNAL, unproved geometric statement supplied as an ordinary hypothesis
only. This matches the literal L1 global normalized seesaw telescope. -/
def ReducedGlobalNormalizedSeesaw : Prop :=
  ∀ {k : Type} [Field k] {X : Scheme} (π : X ⟶ Spec (.of k))
    [IsProper π] [GeometricallyIntegral π]
    (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ π = 𝟙 _)
    (T : Over (Spec (.of k))) [IsLocallyNoetherian T.left] [AlgebraicGeometry.IsReduced T.left]
    (L : (pullback π T.hom).Pic),
    Scheme.Pic.map (sectionBaseChange π σ hσ T) L = 1 →
    (∀ t : T.left,
      Scheme.Pic.map
        (pullback.fst (pullback.snd π T.hom) (T.left.fromSpecResidueField t)) L = 1) →
    L = 1

/-- INTERNAL: the actual global reduced K satisfies the SINGLE normalized
family condition, provided the exact global seesaw theorem is supplied. -/
theorem normalizedKernel_family_eq_one_of_globalSeesaw
    (hSeesaw : ReducedGlobalNormalizedSeesaw)
    {k : Type} [Field k] (A : PkgI3.AbVar k) (L : A.X.left.Pic) :
    L1.normalizedPolarizationFamily A.X L (globalNormalizedKernelι A L) = 1 := by
  let K := globalNormalizedKernel A L
  let j : K ⟶ A.X := globalNormalizedKernelι A L
  letI : IsLocallyNoetherian A.X.left := LocallyOfFiniteType.isLocallyNoetherian A.X.hom
  letI : IsLocallyNoetherian K.left := LocallyOfFiniteType.isLocallyNoetherian j.left
  let C := L1.normalizedPolarizationFamily A.X L (𝟙 A.X)
  let D := L1.normalizedPolarizationFamily A.X L j
  have hNorm : Scheme.Pic.map
      (sectionBaseChange A.X.hom η[A.X].left (L1.groupUnit_over A.X) K) D = 1 :=
    L1.normalizedPolarizationFamily_normalized A.X L j
  have hFibres (t : K.left) :
      Scheme.Pic.map ((pullback.snd A.X.hom K.hom).fiberι t) D = 1 := by
    have ht : j.left t ∈ (globalNormalizedKernelClosed A L : Set A.X.left) := by
      change (globalNormalizedKernelι A L).left t ∈ (globalNormalizedKernelClosed A L : Set A.X.left)
      rw [← range_globalNormalizedKernelι]
      exact ⟨t, rfl⟩
    change Scheme.Pic.map ((pullback.snd A.X.hom A.X.hom).fiberι (j.left t)) C = 1 at ht
    have hb := fibrePicardClass_baseChange_of_eq_one
      (isPullback_baseChangeMap A.X.hom j) C t ht
    dsimp only [C] at hb
    rw [L1.normalizedPolarizationFamily_parameter, Category.comp_id] at hb
    exact hb
  exact hSeesaw A.X.hom η[A.X].left (L1.groupUnit_over A.X) K D hNorm hFibres

/-- INTERNAL: the original global reduced kernel scheme is finite, with only
L1's exact still-unproved seesaw theorem retained as an explicit hypothesis. -/
theorem isFinite_globalNormalizedKernel_of_globalSeesaw
    (hSeesaw : ReducedGlobalNormalizedSeesaw)
    {k : Type} [Field k] (A : PkgI3.AbVar k)
    (M : A.X.left.Modules) (hM : VeryAmple A.X.hom M) :
    letI : M.IsInvertible := hM.isInvertible
    IsFinite (globalNormalizedKernel A (Scheme.Pic.mk M)).hom := by
  letI : M.IsInvertible := hM.isInvertible
  exact isFinite_of_normalizedInvariant_closedSubscheme A
    (globalNormalizedKernel A (Scheme.Pic.mk M)) (globalNormalizedKernelι A (Scheme.Pic.mk M))
    M hM (normalizedKernel_family_eq_one_of_globalSeesaw hSeesaw A (Scheme.Pic.mk M))

/-- INTERNAL: complete very-ample⇒finite ACTUAL translation-stabilizer
composition over an algebraically closed field. No further K/locus/coverage or
finite-kernel input remains. This becomes unconditional only after a REAL
proof of the explicit global seesaw statement is substituted. -/
theorem finite_translationStabilizer_of_globalSeesaw
    (hSeesaw : ReducedGlobalNormalizedSeesaw)
    {k : Type} [Field k] [IsAlgClosed k] (A : PkgI3.AbVar k)
    (M : A.X.left.Modules) (hM : VeryAmple A.X.hom M) :
    letI : M.IsInvertible := hM.isInvertible
    (L1.translationStabilizer A.X (Scheme.Pic.mk M)).Finite := by
  letI : M.IsInvertible := hM.isInvertible
  exact finite_translationStabilizer_of_normalized_closedCover A
    (globalNormalizedKernel A (Scheme.Pic.mk M)) (globalNormalizedKernelι A (Scheme.Pic.mk M))
    M hM (normalizedKernel_family_eq_one_of_globalSeesaw hSeesaw A (Scheme.Pic.mk M))
    (fun a ha => (globalNormalizedKernel_rationalPoint_factor_iff A (Scheme.Pic.mk M) a).mpr ha)

end ZInQ.Contrib.CloudR2Poincare.L2
