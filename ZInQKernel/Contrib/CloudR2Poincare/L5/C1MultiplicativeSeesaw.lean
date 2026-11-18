import ZInQKernel.Contrib.CloudR2Poincare.L2.SeesawFiniteness
import ZInQKernel.Contrib.CloudR2Poincare.L2.GeneralInvariant
import ZInQKernel.Contrib.CloudR2Poincare.L3.B2Interface
import Mathlib.Topology.JacobsonSpace

/-!
# C1: translation invariance gives multiplicativity from the single named seesaw

H72 lead continuation, 2026-11-14. The ONLY carried geometric input is the
exact existing `L2.ReducedGlobalNormalizedSeesaw`, which L1 owns. It is an
ordinary named argument, never a Fact/instance or an asserted proof.

Closedness of the normalized fibre locus, rational closed-point detection,
and Jacobson density are proved and reused. We derive actual multiplicative
bundle and inverse-pullback identities, not merely pointwise invariance.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped AlgebraicGeometry.Scheme.Modules

namespace ZInQ.Contrib.CloudR2Poincare.L5

/-- Every closed point belongs to the actual normalized self-family triviality
locus for a translation-invariant class; Jacobson density makes it the whole
scheme. No identification of rational points with all scheme points is used. -/
theorem normalizedSelfFamily_fibreTrivial_of_translationInvariant
    {k : Type} [Field k] [IsAlgClosed k] (B : PkgI3.AbVar k) (L : B.X.left.Pic)
    (invariant : L3.TranslationInvariant B L) :
    ∀ t : B.X.left, Scheme.Pic.map
      ((pullback.snd B.X.hom B.X.hom).fiberι t)
        (L1.normalizedPolarizationFamily B.X L (𝟙 B.X)) = 1 := by
  haveI : JacobsonSpace B.X.left := LocallyOfFiniteType.jacobsonSpace B.X.hom
  let S := L2.globalNormalizedKernelClosed B L
  have containsClosed : closedPoints B.X.left ⊆ (S : Set B.X.left) := by
    intro t closed
    let a : 𝟙_ (Over (Spec (.of k))) ⟶ B.X :=
      Over.homMk (pointOfClosedPoint B.X.hom t closed) (pointOfClosedPoint_comp _ _ _)
    have ha : a.left (IsLocalRing.closedPoint k) = t := pointOfClosedPoint_apply _ _ _ _
    have membership := (L2.mem_globalNormalizedKernelClosed_rationalPoint_iff B L a).mpr
      (invariant a)
    change Scheme.Pic.map ((pullback.snd B.X.hom B.X.hom).fiberι
      (a.left (IsLocalRing.closedPoint k)))
        (L1.normalizedPolarizationFamily B.X L (𝟙 B.X)) = 1 at membership
    change Scheme.Pic.map ((pullback.snd B.X.hom B.X.hom).fiberι t)
        (L1.normalizedPolarizationFamily B.X L (𝟙 B.X)) = 1
    rw [ha] at membership
    exact membership
  have dense : closure (closedPoints B.X.left) = Set.univ := by
    exact closure_closedPoints
  have allPoints : (S : Set B.X.left) = Set.univ := by
    apply Set.eq_univ_of_univ_subset
    rw [← dense]
    exact closure_minimal containsClosed S.isClosed
  intro t
  have membership : t ∈ (S : Set B.X.left) := by rw [allPoints]; trivial
  exact membership

/-- The single seesaw input turns the actual normalized invariant self-family
into the neutral native Picard class. All hypotheses of seesaw are intrinsic
properties of B, except its explicitly named proof argument. -/
theorem normalizedSelfFamily_eq_one_of_translationInvariant
    (hA : L2.ReducedGlobalNormalizedSeesaw)
    {k : Type} [Field k] [IsAlgClosed k] (B : PkgI3.AbVar k) (L : B.X.left.Pic)
    (invariant : L3.TranslationInvariant B L) :
    L1.normalizedPolarizationFamily B.X L (𝟙 B.X) = 1 := by
  haveI : IsLocallyNoetherian B.X.left := LocallyOfFiniteType.isLocallyNoetherian B.X.hom
  haveI : IsIntegral B.X.left := GeometricallyIntegral.isIntegral_of_subsingleton B.X.hom
  haveI : AlgebraicGeometry.IsReduced B.X.left := inferInstance
  exact hA B.X.hom η[B.X].left (L1.groupUnit_over B.X) B.X
    (L1.normalizedPolarizationFamily B.X L (𝟙 B.X))
    (L1.normalizedPolarizationFamily_normalized B.X L (𝟙 B.X))
    (normalizedSelfFamily_fibreTrivial_of_translationInvariant B L invariant)

/-- The exact multiplication-pullback Picard identity, derived from actual
normalized seesaw, not assumed from ground-field point invariance. -/
theorem mul_pullback_class_of_translationInvariant
    (hA : L2.ReducedGlobalNormalizedSeesaw)
    {k : Type} [Field k] [IsAlgClosed k] (B : PkgI3.AbVar k) (L : B.X.left.Pic)
    (invariant : L3.TranslationInvariant B L) :
    Scheme.Pic.map μ[B.X].left L =
      Scheme.Pic.map (fst B.X B.X).left L * Scheme.Pic.map (snd B.X B.X).left L := by
  have h := normalizedSelfFamily_eq_one_of_translationInvariant hA B L invariant
  rw [L2.normalizedPointFamily_formula] at h
  have multiplication : L1.translationAction B.X (𝟙 B.X) = μ[B.X] := by
    simp only [L1.translationAction, Category.comp_id]
    rw [mul_comm]
    simp [CategoryTheory.Hom.mul_def]
  rw [multiplication, Over.id_left, Scheme.Pic.map_id] at h
  have h' : Scheme.Pic.map μ[B.X].left L *
      (Scheme.Pic.map (fst B.X B.X).left L * Scheme.Pic.map (snd B.X B.X).left L)⁻¹ = 1 := by
    rw [mul_inv_rev,
      mul_comm (Scheme.Pic.map (snd B.X B.X).left L)⁻¹
        (Scheme.Pic.map (fst B.X B.X).left L)⁻¹,
      ← _root_.mul_assoc]
    exact h
  exact mul_inv_eq_one.mp h'

/-- The actual coefficient-sheaf isomorphism required in the Kunneth/shear
vanishing proof. Translation invariance plus the ONE named seesaw input
produces it without any representable general AV Picard scheme. -/
theorem mul_pullback_of_translationInvariant
    (hA : L2.ReducedGlobalNormalizedSeesaw)
    {k : Type} [Field k] [IsAlgClosed k] (B : PkgI3.AbVar k)
    (N : B.X.left.Modules) [N.IsInvertible]
    (invariant : L3.TranslationInvariant B (Scheme.Pic.mk N)) :
    Nonempty ((Scheme.Modules.pullback μ[B.X].left).obj N ≅
      (Scheme.Modules.pullback (fst B.X B.X).left).obj N ⊗
        (Scheme.Modules.pullback (snd B.X B.X).left).obj N) := by
  have h := mul_pullback_class_of_translationInvariant hA B (Scheme.Pic.mk N) invariant
  rw [Scheme.Pic.map_mk, Scheme.Pic.map_mk, Scheme.Pic.map_mk,
    ← Scheme.Pic.mk_tensorObj] at h
  exact (Scheme.Pic.mk_eq_mk_iff _ _).mp h

/-- Anti-diagonal pullback of the normalized self-family gives the actual
inverse-pullback Picard identity needed by L1's native H0 vanishing theorem. -/
theorem inverse_pullback_class_of_translationInvariant
    (hA : L2.ReducedGlobalNormalizedSeesaw)
    {k : Type} [Field k] [IsAlgClosed k] (B : PkgI3.AbVar k) (L : B.X.left.Pic)
    (invariant : L3.TranslationInvariant B L) :
    Scheme.Pic.map ι[B.X].left L = L⁻¹ := by
  have family := normalizedSelfFamily_eq_one_of_translationInvariant hA B L invariant
  have h := L2.restrictedSymmetrizedClass_eq_one_of_normalizedInvariant
    B.X L (𝟙 B.X) family
  simp only [Over.id_left, Scheme.Pic.map_id, CategoryTheory.Hom.inv_def,
    Category.id_comp] at h
  exact eq_inv_of_mul_eq_one_right h

end ZInQ.Contrib.CloudR2Poincare.L5
