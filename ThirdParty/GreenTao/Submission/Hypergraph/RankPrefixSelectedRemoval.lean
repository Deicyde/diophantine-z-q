import Submission.Hypergraph.ConfigurationWeightedHierarchy
import Submission.Hypergraph.ExactGapSelectedRemovalParameters

/-!
# Rank-prefix selected ordered removal

This file connects the nonlinear rank-prefix counting theorem to the
existing coarse-target cleaning machinery.

For one selected coarse-target regularity certificate, the counting side
uses the triangular bounds

```
β_j ≤ (α_j / 4)^2 P_j,
τ_e ≤ (α_e / 4) P_rank(e),
P_j = ∏_{rank(f) ≤ j} α_f / 2.
```

The cleaning side retains the certificate's literal selected gaps:

```
∑ q (upper_q * α_q + gap_q / β_q) ≤ ξ.
```

No reciprocal-horizon bound and no common global complexity window appears.
The resulting theorem is the exact semantic endpoint needed from a
source-faithful rank-hierarchical regularity selector.
-/

namespace Submission.GreenTao

open scoped BigOperators

/-! ## The weighted counting cover -/

/-- A pattern count below the complete half-density barrier is covered by
the canonical coarse bad-base family under the rank-prefix thresholds. -/
theorem orderedCoarseBadBaseDeletionFamily_isCover_rankPrefix
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k n : ℕ} (hrank : n + 1 ≤ k)
    (H : OrderedPattern G k (n + 1))
    (P : OrderedCoarseFineComplex G k (n + 1))
    (hinitial :
      P.coarse.Refines (orderedPatternInitialComplex H))
    (α β : ℕ → ℝ)
    (τ : OrderedRegularityTolerance (n + 1))
    (hregular :
      IsFullyMixedPreliminaryOrderedRegular P τ)
    (hαpos : ∀ m, 0 < α m)
    (hα1 : ∀ m, α m ≤ 1)
    (hβ0 : ∀ m, 0 ≤ β m)
    (hβprefix :
      ∀ j,
        β j ≤
          (α j / 4) ^ 2 *
            configurationRankPrefixBarrier
              k (n + 1) α j)
    (hτprefix :
      ∀ e : PositiveOrderedFace k (n + 1),
        τ e.lowerRank ≤
          (α e.rank / 4) *
            configurationRankPrefixBarrier
              k (n + 1) α e.rank)
    (hcount :
      H.toWeighted.patternCount <
        configurationHalfDensityBarrier
          (k := k) (r := n + 1) α Finset.univ) :
    H.IsCover
      (P.orderedCoarseBadBaseDeletionFamily α β) := by
  apply
    orderedCoarseBadBaseDeletionFamily_isCover_of_mixedGood_count
      hrank H P hinitial α β
      (configurationHalfDensityBarrier
        (k := k) (r := n + 1) α Finset.univ)
      hcount
  intro A hgood
  exact
    configurationHalfDensityBarrier_le_fullConfigurationCount_of_rankPrefixBounds
      P A α β hgood τ hregular
      hαpos hα1 hβ0 hβprefix hτprefix

/-! ## Selected-certificate cleaning and removal -/

namespace CoarseTargetOrderedComplexRegularityCertificate

/-- Direct selected-certificate endpoint for rank-prefix counting and exact
literal-gap cleaning.

The caller supplies only the actual selected upper-complexity vector and
the exact finite deletion sum.  The theorem returns the canonical deletion
family, its cover property, and the requested density bound on every top
face. -/
theorem exists_orderedPatternRemoval_of_rankPrefixSelectedBounds
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k n : ℕ} (hrank : n + 1 ≤ k)
    {initial : OrderedPartitionComplex G k (n + 1)}
    {ε : (j : Fin (n + 1)) → ℕ → ℝ}
    {budget : (j : Fin (n + 1)) → ℕ → ℕ}
    {length : Fin (n + 1) → ℕ}
    (R : CoarseTargetOrderedComplexRegularityCertificate
      G k (n + 1) initial ε budget length)
    (H : OrderedPattern G k (n + 1))
    (hinitial :
      R.coarse.Refines (orderedPatternInitialComplex H))
    (α β : ℕ → ℝ)
    (hαpos : ∀ m, 0 < α m)
    (hα1 : ∀ m, α m ≤ 1)
    (hβpos : ∀ m, 0 < β m)
    (hβprefix :
      ∀ j,
        β j ≤
          (α j / 4) ^ 2 *
            configurationRankPrefixBarrier
              k (n + 1) α j)
    (hτprefix :
      ∀ e : PositiveOrderedFace k (n + 1),
        selectedOrderedComplexTolerance ε R.index e.lowerRank ≤
          (α e.rank / 4) *
            configurationRankPrefixBarrier
              k (n + 1) α e.rank)
    (upperBound : Fin (n + 1) → ℕ)
    (hcoarse :
      ∀ (j : Fin (n + 1))
          (e : OrderedFace k (j.1 + 1)),
        FacePartition.complexity
            (R.coarse.partition j.succ e) ≤
          upperBound j)
    {ξ : ℝ}
    (hdelete :
      (∑ q : OrderedPositiveSubface (n + 1),
        ((upperBound q.1 : ℝ) * α (q.1.1 + 1) +
          R.toCoarseFine.coarseUpperLayerAtomEnergyGap q.1 /
            β (q.1.1 + 1))) ≤ ξ)
    (hcount :
      H.toWeighted.patternCount <
        configurationHalfDensityBarrier
          (k := k) (r := n + 1) α Finset.univ) :
    ∃ D : OrderedPattern.DeletionFamily
        (G := G) k (n + 1),
      H.IsCover D ∧
        ∀ e,
          OrderedPattern.faceDeletionDensity D e ≤ ξ := by
  let τ : OrderedRegularityTolerance (n + 1) :=
    selectedOrderedComplexTolerance ε R.index
  let D : OrderedPattern.DeletionFamily
      (G := G) k (n + 1) :=
    R.toCoarseFine.orderedCoarseBadBaseDeletionFamily α β
  have hcover : H.IsCover D := by
    exact
      orderedCoarseBadBaseDeletionFamily_isCover_rankPrefix
        hrank H R.toCoarseFine hinitial
        α β τ
        R.isFullyMixedPreliminaryOrderedRegular
        hαpos hα1 (fun m => (hβpos m).le)
        hβprefix hτprefix hcount
  refine ⟨D, hcover, ?_⟩
  intro e
  have hbound :=
    R.faceDeletionDensity_orderedCoarseBadBase_exactGap_rankwise_le
      upperBound hcoarse α β
      (fun j => (hαpos (j + 1)).le)
      (fun j => hβpos (j + 1)) e
  exact hbound.trans hdelete

end CoarseTargetOrderedComplexRegularityCertificate

end Submission.GreenTao
