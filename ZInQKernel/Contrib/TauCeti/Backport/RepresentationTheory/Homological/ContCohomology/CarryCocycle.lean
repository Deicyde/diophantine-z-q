/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
-- Backported from Tau Ceti (https://github.com/TauCetiProject/TauCeti, commit 97a5b23586f9, module
-- TauCeti.RepresentationTheory.Homological.ContCohomology.CarryCocycle), Apache-2.0: declarations added to that module after commit 5a01f5fe, whose
-- version is vendored as `ZInQKernel.Contrib.TauCeti.RepresentationTheory.Homological.ContCohomology.CarryCocycle`.
module

public import ZInQKernel.Contrib.TauCeti.RepresentationTheory.Homological.ContCohomology.CarryCocycle
public import ZInQKernel.Contrib.TauCeti.RepresentationTheory.Homological.ContCohomology.ExplicitFunctoriality
public import ZInQKernel.Contrib.TauCeti.Algebra.AddCircle
public import ZInQKernel.Contrib.TauCeti.Topology.Algebra.Group.LocallyConstant

public section
noncomputable section

section
namespace TauCeti.ContCohomology

open groupCohomology
universe u v uH uN
variable {G : Type u} [Group G] [TopologicalSpace G]
variable [ContinuousMul G]
  {M : Type v} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M]

/-- **A carry class pulled back to a coefficient where its invariant vanishes is zero**: if the
compatible pair `(φ, f)` sends the invariant `a` to `0`, it sends the carry class of `χ` and `a` to
`0`. -/
theorem explicitMap2_characterCarryCocycle_eq_zero {H : Type uH} [Group H] [TopologicalSpace H]
    [ContinuousMul H] [ContinuousSMul G M]
    {N : Type uN} [AddCommGroup N] [TopologicalSpace N]
    [IsTopologicalAddGroup N] [DistribMulAction H N] [ContinuousSMul H N]
    (φ : H →ₜ* G) (f : M →+ N) (hf : Continuous f)
    (hequiv : ∀ (h : H) (m : M), f (φ h • m) = h • f m)
    (χ : Additive G →+ AddCircle (1 : ℚ)) (hχ : IsOpen (χ.ker : Set (Additive G)))
    (a : H0 G M) (ha : f a = 0) :
    explicitMap2 G M H N φ f hf hequiv (characterCarryCocycle χ hχ a : H2 G M) = 0 := by
  rw [explicitMap2_characterCarryCocycle]
  generalize hz : explicitMap0 G M (φ : H →* G) f hequiv a = z
  obtain rfl : z = 0 := Subtype.ext (by rw [← hz, coe_explicitMap0]; exact ha)
  rw [map_zero]
  rfl

end TauCeti.ContCohomology
end

end
end
