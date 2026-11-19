import ZInQKernel.Contrib.TauCeti.RepresentationTheory.Homological.ContCohomology.Inflation.Basic

/-!
# Inflation and the two local hypotheses of boundary (4.5)

Let `N` be a normal subgroup of a topological group `G`, acting
continuously on an additive topological group `M`. The coefficient
module over `G/N` is the actual invariant subgroup `M^N`, not an
arbitrary submodule. In degree zero inflation is its inclusion into
`M`; in degree one it is pullback of continuous cochains along the
quotient map, followed by that inclusion.

This file puts the proved degree-zero surjectivity and degree-one
injectivity of continuous inflation into the exact representative-level
form used by the finite boundary theorem. Unlike a criterion requiring
surjectivity on every degree-zero cochain, this argument also handles
a proper invariant subgroup `M^N`. No closedness or finite-index
hypothesis on `N` is used. Continuity of the quotient action is an
explicit hypothesis, as in the existing inflation theorem.

The manuscript uses the two local facts at lines 3917-3918; the
unramified local condition is described at lines 3471-3498. All proofs
use existing continuous-cohomology lemmas. There is no printed leaf.
-/


noncomputable section

namespace ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Inflation

open TauCeti.ContCohomology

universe u v

section Coboundary

variable (G : Type u) [Group G] [TopologicalSpace G]
  (M : Type v) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M]

/-- The genuine continuous degree-zero differential, with its continuous codomain. -/
def coboundaryC1 : M →+ C1 G M :=
  (d0 G M).codRestrict (C1 G M) (fun m => B1_le_C1 G M (d0_mem_B1 m))

end Coboundary

section Inflation

variable (G : Type u) [Group G] [TopologicalSpace G]
  (M : Type v) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M]
  (N : Subgroup G) [N.Normal]
  [ContinuousSMul (G ⧸ N) (FixedPoints.addSubgroup N M)]

/-- The actual degree-zero coefficient inclusion for inflation. -/
def inflation0 : FixedPoints.addSubgroup N M →+ M :=
  (FixedPoints.addSubgroup N M).subtype

/-- Inflation on all continuous degree-one cochains, not only on cohomology classes. -/
def inflation1 : C1 (G ⧸ N) (FixedPoints.addSubgroup N M) →+ C1 G M :=
  ((cochainsMap1 (QuotientGroup.mk' N) (FixedPoints.addSubgroup N M).subtype).domRestrict
    (C1 (G ⧸ N) (FixedPoints.addSubgroup N M))).codRestrict (C1 G M)
    (fun c => continuous_cochainsMap1 (Subgroup.quotientMkContinuousMonoidHom N)
      (FixedPoints.addSubgroup N M).subtype continuous_subtype_val c.2)

/-- The degree-zero square commutes for these precise continuous cochain maps. -/
theorem inflation_coboundary (w : FixedPoints.addSubgroup N M) :
    inflation1 G M N (coboundaryC1 (G ⧸ N) (FixedPoints.addSubgroup N M) w) =
      coboundaryC1 G M (inflation0 G M N w) := by
  apply Subtype.ext
  exact cochainsMap1_d0 (QuotientGroup.mk' N) (FixedPoints.addSubgroup N M).subtype
    N.fixedPoints_subtype_mk'_smul w

/-- The exact `honto` and `hinj` representative-level statements for inflation.
The degree-one differential in the second statement is the ordinary
continuous-cocycle identity, viewed in the ambient function group. -/
theorem inflation_localFacts :
    (∀ c : M, coboundaryC1 G M c = 0 →
      ∃ w : FixedPoints.addSubgroup N M,
        coboundaryC1 (G ⧸ N) (FixedPoints.addSubgroup N M) w = 0 ∧
          inflation0 G M N w = c) ∧
    (∀ a : C1 (G ⧸ N) (FixedPoints.addSubgroup N M),
      d1 (G ⧸ N) (FixedPoints.addSubgroup N M) a = 0 →
      (∃ c : M, inflation1 G M N a = coboundaryC1 G M c) →
      ∃ w : FixedPoints.addSubgroup N M,
        coboundaryC1 (G ⧸ N) (FixedPoints.addSubgroup N M) w = a) := by
  constructor
  · intro c hc
    have hfix : ∀ g : G, g • c = c := by
      intro g
      have h := congrFun (congrArg Subtype.val hc) g
      exact sub_eq_zero.1 h
    let c0 : H0 G M := ⟨c, (FixedPoints.mem_addSubgroup G M c).2 hfix⟩
    obtain ⟨w, hw⟩ := explicitInfl0_surjective G M N c0
    refine ⟨w.1, ?_, ?_⟩
    · apply Subtype.ext
      funext q
      change q • w.1 - w.1 = 0
      exact sub_eq_zero.2 ((FixedPoints.mem_addSubgroup (G ⧸ N)
        (FixedPoints.addSubgroup N M) w.1).1 w.2 q)
    · exact congrArg Subtype.val hw
  · intro a ha hca
    obtain ⟨c, hc⟩ := hca
    let z : Z1 (G ⧸ N) (FixedPoints.addSubgroup N M) :=
      ⟨a.1, mem_Z1_iff.2 ⟨a.2, d1_apply_eq_zero_iff.1 ha⟩⟩
    have hinfl : explicitInfl1 G M N (z : H1 (G ⧸ N) (FixedPoints.addSubgroup N M)) = 0 := by
      rw [explicitInfl1_mk, H1pi_eq_zero_iff]
      refine AddMonoidHom.mem_range.2 ⟨c, ?_⟩
      exact (congrArg Subtype.val hc).symm
    have hz : (z : H1 (G ⧸ N) (FixedPoints.addSubgroup N M)) = 0 := by
      apply explicitInfl1_injective G M N
      rw [map_zero]
      exact hinfl
    obtain ⟨w, hw⟩ := mem_B1_iff.1 (H1pi_eq_zero_iff.1 hz)
    refine ⟨w, Subtype.ext ?_⟩
    funext q
    exact hw q

end Inflation

end ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Inflation
