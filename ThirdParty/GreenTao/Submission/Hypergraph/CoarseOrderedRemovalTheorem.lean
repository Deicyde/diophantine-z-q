import Submission.Hypergraph.CoarseConfigurationCounting
import Submission.Hypergraph.OrderedRemovalTheorem

/-!
# The coarse-configuration ordered removal contradiction

`CoarseOrderedRemoval` cleans tuples according to their own atoms in the
coarse upper partitions.  `CoarseConfigurationCounting` counts the resulting
mixed-good closed coarse configurations.  This file joins those two pieces
to the edge-monochromatic input partition.

The argument is semantic.  If an occurrence survives every deletion, its
canonical coarse atom configuration is mixed-good.  A positive uniform lower
bound for that configuration contradicts the assumed upper bound for the
original pattern count, since the coarse top layer still refines the original
edge predicate.
-/

namespace Submission.GreenTao

/-! ## Abstract mixed-good cover contradiction -/

/-- A uniform lower count for every mixed-good coarse configuration forces
the canonical coarse bad-base family to cover every occurrence. -/
theorem orderedCoarseBadBaseDeletionFamily_isCover_of_mixedGood_count
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k n : ℕ} (hrk : n + 1 ≤ k)
    (H : OrderedPattern G k (n + 1))
    (P : OrderedCoarseFineComplex G k (n + 1))
    (hinitial :
      P.coarse.Refines (orderedPatternInitialComplex H))
    (α β : ℕ → ℝ) (c : ℝ)
    (hcount : H.toWeighted.patternCount < c)
    (hgoodCount :
      ∀ A : ClosedOrderedAtomConfiguration
          G k (n + 1) P.coarse,
        A.IsMixedGood P α β →
          c ≤ fullConfigurationCount A) :
    H.IsCover
      (P.orderedCoarseBadBaseDeletionFamily α β) := by
  intro x hx
  by_contra hsurvives
  push Not at hsurvives
  let A :
      ClosedOrderedAtomConfiguration
        G k (n + 1) P.coarse :=
    ClosedOrderedAtomConfiguration.ofTuple P.coarse x
  have hgood : A.IsMixedGood P α β := by
    exact
      ClosedOrderedAtomConfiguration.isMixedGood_of_avoids_coarseTopBadBaseDeletion
        hrk P x α β hsurvives
  have hcA : c ≤ fullConfigurationCount A :=
    hgoodCount A hgood
  have htop :
      OrderedFacePartitionRefines P.coarse.topLayer
        (orderedPatternTopPartition H) :=
    orderedPatternTopPartition_refines_of_complex_refines_initial
      H hinitial
  have hAH :
      fullConfigurationCount A ≤
        H.toWeighted.patternCount :=
    fullConfigurationCount_le_patternCount
      H htop A ((H.mem_occurrenceFinset x).1 hx)
  linarith

/-! ## Rankwise quantitative cover theorem -/

/-- The rank-dependent mixed counting lower bound gives the corresponding
coarse ordered-removal cover theorem. -/
theorem orderedCoarseBadBaseDeletionFamily_isCover_rankwise
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k n : ℕ} (hrk : n + 1 ≤ k)
    (H : OrderedPattern G k (n + 1))
    (P : OrderedCoarseFineComplex G k (n + 1))
    (hinitial :
      P.coarse.Refines (orderedPatternInitialComplex H))
    (α β : ℕ → ℝ)
    (τ : OrderedRegularityTolerance (n + 1))
    (hregular :
      IsFullyMixedPreliminaryOrderedRegular P τ)
    (δ : ℕ → ℝ)
    (hα : ∀ m, 0 ≤ α m)
    (hτ : ∀ j, 0 ≤ τ j)
    (hδ : ∀ m, 0 ≤ δ m)
    (hβ0 : ∀ m, 0 ≤ β m)
    (hβδ : ∀ m, β m ≤ (δ m) ^ 2)
    (hcount :
      H.toWeighted.patternCount <
        (∏ e : PositiveOrderedFace k (n + 1),
            α e.rank) -
          (∑ e : PositiveOrderedFace k (n + 1),
            (δ e.rank + τ e.lowerRank))) :
    H.IsCover
      (P.orderedCoarseBadBaseDeletionFamily α β) := by
  let c : ℝ :=
    (∏ e : PositiveOrderedFace k (n + 1),
        α e.rank) -
      (∑ e : PositiveOrderedFace k (n + 1),
        (δ e.rank + τ e.lowerRank))
  apply
    orderedCoarseBadBaseDeletionFamily_isCover_of_mixedGood_count
      hrk H P hinitial α β c hcount
  intro A hgood
  exact
    mixedFullConfigurationCount_lower_bound_rankwise
      P A α β hgood τ hregular δ
      hα hτ hδ hβ0 hβδ

end Submission.GreenTao
