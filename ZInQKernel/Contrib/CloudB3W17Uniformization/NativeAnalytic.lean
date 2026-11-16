import ZInQKernel.Contrib.CloudB3W17Hodge.Port.Lemmas.AlgebraicGeometry.ComplexPoint.Manifold
import ZInQKernel.Contrib.CloudB3W17LocalExp.ManifoldIFT

/-!
# Native complex-point regular-function and morphism analyticity

Adapters over the genuine complex-point manifold ported from
Paul-Lez/HodgeConjecture at `2ead713179628a3c738197d5996f51c8a9c886ac`, committed
by the W17 Hodge donor as `e222d7ba1999d47ab0618cc0d812bb0b6f8b7229`.
The native chart inverse and its regular-section analyticity are donor results;
this file only packages them as `ContMDiffOn`, regular Γ local diffeomorphism
coordinates and analytic scheme morphisms. No point/evaluation/topology bridge
to BP is redefined and no donor file is modified.

The morphism argument follows the local-target-coordinate inversion logic of
host unif-printed Stage2a at `dbf043a4eb8d977b1d4bf0b03010f915b70bcfb8`, now
using the native donor's actual evaluation and analytic topology instead of a
printed dictionary premise. Source/license notices remain in the port.
-/

open scoped Manifold ContDiff Topology
open Set Filter Function CategoryTheory AlgebraicGeometry

namespace CloudB3W17Uniformization

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry.Point AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]

/-- Regular-section evaluation is continuous on its own analytic open. -/
theorem continuousOn_nativeEvaluate (U : X.left.Opens) (s : Γ(X.left, U)) :
    ContinuousOn (Point.evaluate U s) (Point.overOpen U : Set (ComplexPoint X)) := by
  rw [continuousOn_iff_continuous_domRestrict, continuous_def]
  intro O hO
  have h := (Point.isOpen_overOpen_inter_preimage U s O hO).preimage
    (continuous_subtype_val : Continuous (Subtype.val : Point.overOpen U → ComplexPoint X))
  have heq : Subtype.val ⁻¹' (Point.overOpen U ∩ Point.evaluate U s ⁻¹' O) =
      (Point.overOpen U).domRestrict (Point.evaluate U s) ⁻¹' O := by
    ext p
    simp only [mem_preimage, mem_inter_iff, Set.domRestrict_apply, p.property, true_and]
  rw [heq] at h
  exact h

/-- Every native regular-section evaluation is holomorphic on its analytic open. -/
theorem contMDiffOn_nativeEvaluate (U : X.left.Opens) (s : Γ(X.left, U)) :
    ContMDiffOn 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, ℂ) ω (Point.evaluate U s)
      (Point.overOpen U : Set (ComplexPoint X)) := by
  intro p hp
  rw [contMDiffWithinAt_iff]
  refine ⟨continuousOn_nativeEvaluate X U s p hp, ?_⟩
  have hsrc : p ∈ (localChart X d p).source := mem_localChart_source X d p
  have han := analyticAt_localChart_symm_evaluate X d p
    ((localChart X d p).map_source hsrc) U s (by rwa [(localChart X d p).left_inv hsrc])
  change ContDiffWithinAt ℂ ω
    (fun v => Point.evaluate U s ((localChart X d p).symm v)) _ (localChart X d p p)
  exact han.contDiffAt.contDiffWithinAt

/-- Some native regular Γ sections are a local analytic diffeomorphism at every point. -/
theorem native_regularCoordinates (p : ComplexPoint X) :
    ∃ (U : X.left.Opens) (f : Fin d → Γ(X.left, U)), p ∈ Point.overOpen U ∧
      IsLocalDiffeomorphAt 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) ω
        (fun q i => Point.evaluate U (f i) q) p := by
  let D := localEtaleCoordinates X d p
  refine ⟨D.ambientCoordinateOpen, D.ambientCoordinateSection, ?_, ?_⟩
  · have hmem := mem_coordinateNeighborhood_of_mem_localChart_source X d p p
      (mem_localChart_source X d p)
    simpa only [D, LocalEtaleCoordinates.ambientCoordinateOpen, Scheme.Opens.ι_image_top] using hmem
  · refine ⟨CloudB3W17LocalExp.chartPartialDiffeo p, mem_localChart_source X d p, ?_⟩
    intro q hq
    funext i
    exact (localChart_apply_component_eq_evaluate X d p q hq i).symm

/-- Scheme morphisms between native smooth complex-point manifolds are globally analytic. -/
theorem contMDiff_nativeMap {Y : Over (Spec ↧ℂ)} (m : ℕ)
    [SmoothOfRelativeDimension m Y.hom] (α : X ⟶ Y) :
    ContMDiff 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin m → ℂ) ω (Point.map α) := by
  intro p
  obtain ⟨U, f, hU, hloc⟩ := native_regularCoordinates Y m (Point.map α p)
  let c : ComplexPoint Y → (Fin m → ℂ) := fun q i => Point.evaluate U (f i) q
  have hcF : ContMDiffAt 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin m → ℂ) ω
      (fun q => c (Point.map α q)) p := by
    apply contMDiffAt_pi_module_iff.mpr
    intro i
    have h := contMDiffOn_nativeEvaluate X d (α.left ⁻¹ᵁ U) (α.left.app U (f i))
    have hpU : p ∈ Point.overOpen (α.left ⁻¹ᵁ U) := (Point.mem_overOpen_map_iff α p U).mp hU
    have h' := (h p hpU).contMDiffAt ((Point.isOpen_overOpen _).mem_nhds hpU)
    exact h'.congr_of_eventuallyEq (.of_forall (fun q => Point.evaluate_map α U (f i) q))
  have heq : Point.map α =ᶠ[𝓝 p] (fun q => hloc.localInverse (c (Point.map α q))) := by
    have h1 := hloc.localInverse_eventuallyEq_left.comp_tendsto ((Point.continuous_map α).tendsto p)
    exact h1.symm
  exact (hloc.contMDiffAt_localInverse.comp p hcF).congr_of_eventuallyEq heq

end CloudB3W17Uniformization
