import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.PrimitiveEisensteinMixedMembership
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.PrimitiveEisensteinCuspComplement

/-!
# Actual mixed weight-three orthogonality reduction

Orthogonality to the actual mixed/cusp intersection is a legitimate input
property. The produced primitive interpolation lies in the actual class-series
span and mixed space. Subtracting it leaves an actual cusp still in the mixed
space. The intersection property kills that cusp and genuine Eisenstein/cusp
orthogonality kills the interpolant. This transports the given property to all
mixed tests; it does not prove the orthogonal complement is zero.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set UpperHalfPlane Complex Matrix.SpecialLinearGroup
open scoped Topology MatrixGroups ModularForm ComplexConjugate

namespace ZInQ.Contrib.HeckePrimeRationality.MixedCuspOrthogonalityReduction
open ZInQ.Contrib.HeckePrimeRationality
open PrimitiveEisensteinInterpolation PrimitiveEisensteinComplement PrimitiveEisensteinMixedMembership

/-- The actual mixed/cusp intersection as a modular-form submodule. -/
def mixedCuspIntersection (N : ℕ) (hN : 0 < N) : Submodule ℂ (ModularForm (principalReal N) 3) :=
  MixedAllLevelTrace.mixedSpace N hN ⊓ cuspSubmodule N 3

/-- The actual residual cusp of an actual mixed test lies in the intersection. -/
theorem residualCusp_mem_intersection (N : ℕ) [NeZero N] (h3 : 3 ≤ N)
    (G : ModularForm (principalReal N) 3) (hG : G ∈ MixedAllLevelTrace.mixedSpace N (by omega)) :
    (residualCusp N h3 3 le_rfl G : ModularForm (principalReal N) 3) ∈
      mixedCuspIntersection N (by omega) :=
  ⟨residualCusp_three_mem_mixedSpace N h3 G hG,⟨residualCusp N h3 3 le_rfl G,rfl⟩⟩

/-- Given orthogonality to the actual mixed/cusp intersection, derive it for
EVERY actual mixed test using the produced decomposition and real membership. -/
theorem intersection_orthogonality_implies_all_mixed (N : ℕ) [NeZero N] (h3 : 3 ≤ N)
    (f : CuspForm (principalReal N) 3)
    (hOrth : ∀ H : ModularForm (principalReal N) 3,
      H ∈ mixedCuspIntersection N (by omega) → pairing N 3 f H = 0)
    (G : ModularForm (principalReal N) 3) (hG : G ∈ MixedAllLevelTrace.mixedSpace N (by omega)) :
    pairing N 3 f G = 0 := by
  have hE := pairing_eisenstein_zero N h3 3 le_rfl f (interpolation N 3 le_rfl G)
    (interpolation_mem_eisensteinSpan N 3 le_rfl G)
  have hg := hOrth _ (residualCusp_mem_intersection N h3 G hG)
  change pairingRight N 3 f G = 0
  rw [actual_interpolant_plus_cusp N h3 3 le_rfl G,map_add]
  change pairing N 3 f (interpolation N 3 le_rfl G) +
    pairing N 3 f (residualCusp N h3 3 le_rfl G) = 0
  exact (congrArg₂ (fun x y : ℂ => x+y) hE hg).trans (zero_add 0)

/-- Exact Petersson formulation for the actual mixed space and actual cusp range. -/
theorem actual_mixed_petersson_reduction (N : ℕ) [NeZero N] (h3 : 3 ≤ N)
    (f : CuspForm (principalReal N) 3)
    (hOrth : ∀ H : ModularForm (principalReal N) 3,
      H ∈ MixedAllLevelTrace.mixedSpace N (by omega) ⊓ ModularForm.cuspFormSubmodule (principalReal N) 3 →
      UpperHalfPlane.peterssonInner 3 (PrimitivePetersson.principalDomain N) f H = 0) :
    ∀ G : ModularForm (principalReal N) 3, G ∈ MixedAllLevelTrace.mixedSpace N (by omega) →
      IntegrableOn (UpperHalfPlane.petersson 3 f G) (PrimitivePetersson.principalDomain N) volume ∧
      UpperHalfPlane.peterssonInner 3 (PrimitivePetersson.principalDomain N) f G = 0 := by
  intro G hG
  exact ⟨pairing_integrable N 3 f G,intersection_orthogonality_implies_all_mixed N h3 f hOrth G hG⟩

/-- Equivalent input stated with actual cusp bundles in the mixed space. -/
theorem actual_mixed_cusp_test_reduction (N : ℕ) [NeZero N] (h3 : 3 ≤ N)
    (f : CuspForm (principalReal N) 3)
    (hOrth : ∀ g : CuspForm (principalReal N) 3,
      (g : ModularForm (principalReal N) 3) ∈ MixedAllLevelTrace.mixedSpace N (by omega) →
      UpperHalfPlane.peterssonInner 3 (PrimitivePetersson.principalDomain N) f g = 0) :
    ∀ G : ModularForm (principalReal N) 3, G ∈ MixedAllLevelTrace.mixedSpace N (by omega) →
      UpperHalfPlane.peterssonInner 3 (PrimitivePetersson.principalDomain N) f G = 0 := by
  apply intersection_orthogonality_implies_all_mixed N h3 f
  intro H hH
  obtain ⟨g,hg⟩ := hH.2
  have hgm : (g : ModularForm (principalReal N) 3) ∈ MixedAllLevelTrace.mixedSpace N (by omega) := by
    change CuspForm.toModularFormₗ g ∈ MixedAllLevelTrace.mixedSpace N (by omega)
    rw [hg]
    exact hH.1
  have hz := hOrth g hgm
  change pairing N 3 f (CuspForm.toModularFormₗ g) = 0 at hz
  rw [hg] at hz
  exact hz

/-- Every genuine x-lambda test, including all signed and bad labels, is annihilated. -/
theorem actual_cross_test_petersson_zero (N : ℕ) [NeZero N] (h3 : 3 ≤ N)
    (f : CuspForm (principalReal N) 3)
    (hOrth : ∀ H : ModularForm (principalReal N) 3,
      H ∈ mixedCuspIntersection N (by omega) → pairing N 3 f H = 0)
    (a b c d : ℤ) :
    IntegrableOn (UpperHalfPlane.petersson 3 f (MixedWeightThreeDistribution.crossForm N (by omega) a b c d))
      (PrimitivePetersson.principalDomain N) volume ∧
    UpperHalfPlane.peterssonInner 3 (PrimitivePetersson.principalDomain N) f
      (MixedWeightThreeDistribution.crossForm N (by omega) a b c d) = 0 :=
  ⟨pairing_integrable N 3 f _,intersection_orthogonality_implies_all_mixed N h3 f hOrth _
    (MixedAllLevelTrace.crossForm_mem_mixedSpace N (by omega) a b c d)⟩

end ZInQ.Contrib.HeckePrimeRationality.MixedCuspOrthogonalityReduction
