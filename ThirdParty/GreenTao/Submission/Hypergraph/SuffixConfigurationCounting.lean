-- Modified in this repository (2026, port to Lean 4.35.0 and Mathlib 56a00585): see ThirdParty/GreenTao/NOTICE.md.
import Submission.Hypergraph.ConfigurationWeightedHierarchy

/-!
# Why configuration counting is ordered from maximal faces downward

The nonlinear configuration-counting recurrence controls the uniform term
by grouping every remaining face factor under a coordinate omitted by that
factor.  Rank maximality is a convenient sufficient condition: a distinct
face of no larger rank must omit a coordinate of the selected face.

This file records the exact combinatorial condition and two obstructions to
reversing the recurrence.

* A remaining coface contains every coordinate of the selected face, so it
  cannot be assigned to any factor of a face-cut test.
* Erasing an immediate boundary while its coface remains destroys downward
  closure.

It also defines the natural rank-suffix half-density product and shows that
it need not be below the actual lower-rank remainder product.  Thus the
rank-prefix barrier in `ConfigurationWeightedHierarchy` cannot simply be
replaced by a suffix barrier in the existing maximum-face recurrence.

The surrounding regularity APIs do not provide a hidden suffix remedy.
`FaceRegularityState.IsRegularAgainst` can abstractly test a residual
against an arbitrary finite family of full-tuple subsets.  Refining by such
a subset, however, produces an arbitrary partition of the selected
full-face space.  It need not be an `orderedBoundaryPartition` assembled
from shared codimension-one face partitions, so it cannot be inserted into
an `OrderedPartitionComplex` or charged by the existing lower-face cleaning
argument.  The realizable APIs
`IsPreliminaryOrderedRegular`, `IsPreliminaryOrderedBoundedRegular`, and
`IsFaceCutRegularFamily` deliberately restrict tests to Boolean or bounded
products of codimension-one functions.  `BoundaryBernoulli` only passes
between those two versions; it does not represent an arbitrary coface
slice as a boundary product.

The generated-cell API can propagate the finitely many lower cells selected
by a higher-rank regularization.  That supports a different, bundled
cell-lifting induction, but it does not change this single-face recurrence:
a remaining coface still contains every selected coordinate, and its
restricted indicator is not one of the coordinate-omitting factors
controlled by face-cut regularity.  Any successful use of generated cells
therefore has to replace the present telescoping/counting interface rather
than merely reverse its order or substitute a suffix product.
-/

namespace Submission.GreenTao

open scoped BigOperators

/-! ## The exact missing-coordinate condition -/

/-- Every factor remaining after selecting `e` omits some coordinate of
`e`.  This is the precise combinatorial input used to group the remainder
into a boundary face-cut test. -/
def HasFaceCutRemainder
    {k r : ℕ}
    (s : Finset (PositiveOrderedFace k r))
    (e : PositiveOrderedFace k r) : Prop :=
  ∀ f ∈ s.erase e,
    ∃ i : Fin (e.lowerRank.1 + 1),
      e.face i ∉ Set.range f.face

/-- Rank maximality implies the exact missing-coordinate condition used by
the current face-cut proof. -/
theorem hasFaceCutRemainder_of_rankMax
    {k r : ℕ}
    (s : Finset (PositiveOrderedFace k r))
    (e : PositiveOrderedFace k r)
    (hmax : ∀ f ∈ s.erase e, f.rank ≤ e.rank) :
    HasFaceCutRemainder s e := by
  intro f hf
  exact exists_positiveFace_coordinate_not_mem_range
    e f (hmax f hf) (Finset.mem_erase.mp hf).1

/-- A range-containing coface has no missing selected coordinate. -/
theorem not_exists_selectedCoordinate_not_mem_range_of_range_subset
    {k r : ℕ}
    (e f : PositiveOrderedFace k r)
    (hcoface : Set.range e.face ⊆ Set.range f.face) :
    ¬∃ i : Fin (e.lowerRank.1 + 1),
      e.face i ∉ Set.range f.face := by
  rintro ⟨i, hi⟩
  exact hi (hcoface ⟨i, rfl⟩)

/-- Having a missing selected coordinate is equivalent to the failure of
range inclusion. -/
theorem exists_selectedCoordinate_not_mem_range_iff
    {k r : ℕ}
    (e f : PositiveOrderedFace k r) :
    (∃ i : Fin (e.lowerRank.1 + 1),
        e.face i ∉ Set.range f.face) ↔
      ¬Set.range e.face ⊆ Set.range f.face := by
  constructor
  · rintro ⟨i, hi⟩ hsubset
    exact hi (hsubset ⟨i, rfl⟩)
  · intro hsubset
    by_contra hmissing
    push Not at hmissing
    apply hsubset
    rintro v ⟨i, rfl⟩
    exact hmissing i

/-- Exact characterization of the face-cut grouping condition: no
remaining factor may be a coface of the selected face. -/
theorem hasFaceCutRemainder_iff_no_coface
    {k r : ℕ}
    (s : Finset (PositiveOrderedFace k r))
    (e : PositiveOrderedFace k r) :
    HasFaceCutRemainder s e ↔
      ∀ f ∈ s.erase e,
        ¬Set.range e.face ⊆ Set.range f.face := by
  constructor
  · intro hcut f hf
    exact
      (exists_selectedCoordinate_not_mem_range_iff e f).1
        (hcut f hf)
  · intro hnocoface f hf
    exact
      (exists_selectedCoordinate_not_mem_range_iff e f).2
        (hnocoface f hf)

/-- Consequently, one remaining coface prevents the remainder from being a
face-cut remainder for the selected face. -/
theorem not_hasFaceCutRemainder_of_coface
    {k r : ℕ}
    (s : Finset (PositiveOrderedFace k r))
    (e f : PositiveOrderedFace k r)
    (hf : f ∈ s.erase e)
    (hcoface : Set.range e.face ⊆ Set.range f.face) :
    ¬HasFaceCutRemainder s e := by
  intro hcut
  exact
    not_exists_selectedCoordinate_not_mem_range_of_range_subset
      e f hcoface (hcut f hf)

/-- If a distinct face contains every coordinate of `e`, it has strictly
larger rank.  Thus a permissible elimination order may be more general
than rank order, but it must still be reverse inclusion order. -/
theorem rank_lt_of_strict_coface
    {k r : ℕ}
    (e f : PositiveOrderedFace k r)
    (hne : f ≠ e)
    (hcoface : Set.range e.face ⊆ Set.range f.face) :
    e.rank < f.rank := by
  have hnot : ¬f.rank ≤ e.rank := by
    intro hle
    obtain ⟨i, hi⟩ :=
      exists_positiveFace_coordinate_not_mem_range
        e f hle hne
    exact hi (hcoface ⟨i, rfl⟩)
  omega

/-! ## Downward closure also forces reverse inclusion -/

/-- Erasing one face from a downward-closed family preserves downward
closure exactly when that face is not an immediate boundary of any
remaining face. -/
theorem downwardClosed_erase_iff_no_remaining_boundary
    {k r : ℕ}
    {s : Finset (PositiveOrderedFace k r)}
    (hclosed : IsDownwardClosedPositiveFaces s)
    (e : PositiveOrderedFace k r) :
    IsDownwardClosedPositiveFaces (s.erase e) ↔
      ∀ upper ∈ s.erase e,
        ∀ (hpos : 0 < upper.lowerRank.1)
          (i : Fin (upper.lowerRank.1 + 1)),
          upper.boundary hpos i ≠ e := by
  constructor
  · intro herase upper hupper hpos i hboundary
    have hb :=
      herase upper hupper hpos i
    rw [hboundary] at hb
    exact (Finset.mem_erase.mp hb).1 rfl
  · intro hnoboundary upper hupper hpos i
    apply Finset.mem_erase.mpr
    refine ⟨hnoboundary upper hupper hpos i, ?_⟩
    exact hclosed upper
      (Finset.mem_of_mem_erase hupper) hpos i

/-- Erasing an immediate boundary face while its upper face remains makes
the family non-downward-closed. -/
theorem not_downwardClosed_erase_boundary
    {k r : ℕ}
    (s : Finset (PositiveOrderedFace k r))
    (upper lower : PositiveOrderedFace k r)
    (hupper : upper ∈ s)
    (hpos : 0 < upper.lowerRank.1)
    (i : Fin (upper.lowerRank.1 + 1))
    (hboundary : upper.boundary hpos i = lower) :
    ¬IsDownwardClosedPositiveFaces (s.erase lower) := by
  have hlt : lower.rank < upper.rank := by
    rw [← hboundary]
    exact upper.boundary_rank_lt hpos i
  have hne : upper ≠ lower := by
    intro h
    exact (Nat.ne_of_lt hlt)
      (congrArg PositiveOrderedFace.rank h.symm)
  intro hclosed
  have hlowerErase :
      lower ∈ s.erase lower := by
    have hb :=
      hclosed upper
        (Finset.mem_erase.mpr ⟨hne, hupper⟩) hpos i
    simpa only [hboundary] using hb
  exact (Finset.mem_erase.mp hlowerErase).1 rfl

/-- In particular, deleting a boundary face from the full face family
cannot be the first genuine configuration-counting step. -/
theorem not_downwardClosed_univ_erase_boundary
    {k r : ℕ}
    (upper : PositiveOrderedFace k r)
    (hpos : 0 < upper.lowerRank.1)
    (i : Fin (upper.lowerRank.1 + 1)) :
    ¬IsDownwardClosedPositiveFaces
      ((Finset.univ :
          Finset (PositiveOrderedFace k r)).erase
        (upper.boundary hpos i)) := by
  exact not_downwardClosed_erase_boundary
    Finset.univ upper (upper.boundary hpos i)
    (Finset.mem_univ _) hpos i rfl

/-! ## The naïve suffix barrier does not bound a lower remainder -/

/-- Positive ordered faces of rank at least `j`. -/
noncomputable def positiveOrderedFacesFromRank
    (k r j : ℕ) : Finset (PositiveOrderedFace k r) :=
  Finset.univ.filter fun e => j ≤ e.rank

@[simp]
theorem mem_positiveOrderedFacesFromRank
    {k r j : ℕ} (e : PositiveOrderedFace k r) :
    e ∈ positiveOrderedFacesFromRank k r j ↔ j ≤ e.rank := by
  simp [positiveOrderedFacesFromRank]

/-- The natural half-density product over the rank suffix beginning at
`j`. -/
noncomputable def configurationRankSuffixBarrier
    (k r : ℕ) (α : ℕ → ℝ) (j : ℕ) : ℝ :=
  configurationHalfDensityBarrier α
    (positiveOrderedFacesFromRank k r j)

/-- A density schedule equal to zero below `j` and one from `j` onward. -/
def suffixCounterDensity (j n : ℕ) : ℝ :=
  if j ≤ n then 1 else 0

/-- Every half-density product is at most one when its density schedule is
nonnegative and bounded by one. -/
theorem configurationHalfDensityBarrier_le_one
    {k r : ℕ} (α : ℕ → ℝ)
    (hα0 : ∀ n, 0 ≤ α n)
    (hα1 : ∀ n, α n ≤ 1)
    (s : Finset (PositiveOrderedFace k r)) :
    configurationHalfDensityBarrier α s ≤ 1 := by
  unfold configurationHalfDensityBarrier
  apply Finset.prod_le_one₀
  · intro e _he
    exact div_nonneg (hα0 e.rank) (by norm_num)
  · intro e _he
    have := hα1 e.rank
    linarith [hα0 e.rank]

/-- The suffix barrier for `suffixCounterDensity` is strictly positive. -/
theorem configurationRankSuffixBarrier_suffixCounterDensity_pos
    (k r j : ℕ) :
    0 <
      configurationRankSuffixBarrier
        k r (suffixCounterDensity j) j := by
  unfold configurationRankSuffixBarrier
    configurationHalfDensityBarrier
  exact Finset.prod_pos fun e he => by
    have hj : j ≤ e.rank :=
      (mem_positiveOrderedFacesFromRank e).1 he
    simp [suffixCounterDensity, hj]

/-- Replace the zero lower-rank values in `suffixCounterDensity` by the
positive value of its own suffix product.  This keeps the suffix unchanged
while making every density floor strictly positive. -/
noncomputable def positiveSuffixCounterDensity
    (k r j n : ℕ) : ℝ :=
  if j ≤ n then 1
  else
    configurationRankSuffixBarrier
      k r (suffixCounterDensity j) j

theorem positiveSuffixCounterDensity_pos
    (k r j n : ℕ) :
    0 < positiveSuffixCounterDensity k r j n := by
  unfold positiveSuffixCounterDensity
  split_ifs
  · norm_num
  · exact
      configurationRankSuffixBarrier_suffixCounterDensity_pos
        k r j

theorem positiveSuffixCounterDensity_le_one
    (k r j n : ℕ) :
    positiveSuffixCounterDensity k r j n ≤ 1 := by
  unfold positiveSuffixCounterDensity
  split_ifs
  · exact le_rfl
  · unfold configurationRankSuffixBarrier
    apply configurationHalfDensityBarrier_le_one
    · intro m
      simp only [suffixCounterDensity]
      split_ifs <;> positivity
    · intro m
      simp only [suffixCounterDensity]
      split_ifs <;> norm_num

/-- The positive counter-schedule has exactly the same suffix product as
the zero-below-rank schedule. -/
theorem configurationRankSuffixBarrier_positiveSuffixCounterDensity
    (k r j : ℕ) :
    configurationRankSuffixBarrier
        k r (positiveSuffixCounterDensity k r j) j =
      configurationRankSuffixBarrier
        k r (suffixCounterDensity j) j := by
  unfold configurationRankSuffixBarrier
    configurationHalfDensityBarrier
  apply Finset.prod_congr rfl
  intro e he
  have hj : j ≤ e.rank :=
    (mem_positiveOrderedFacesFromRank e).1 he
  simp [positiveSuffixCounterDensity,
    suffixCounterDensity, hj]

/-- If the actual remainder contains even one lower-rank face, its
half-density product can vanish while the corresponding suffix product is
positive.  Hence there is no unconditional suffix analogue of
`configurationRankPrefixBarrier_le_erase`. -/
theorem not_configurationRankSuffixBarrier_le_erase_of_lowerFace
    {k r : ℕ}
    (s : Finset (PositiveOrderedFace k r))
    (e f : PositiveOrderedFace k r)
    (hf : f ∈ s.erase e)
    (hlt : f.rank < e.rank) :
    ¬ configurationRankSuffixBarrier
          k r (suffixCounterDensity e.rank) e.rank ≤
        configurationHalfDensityBarrier
          (suffixCounterDensity e.rank) (s.erase e) := by
  have hright :
      configurationHalfDensityBarrier
          (suffixCounterDensity e.rank) (s.erase e) = 0 := by
    unfold configurationHalfDensityBarrier
    apply Finset.prod_eq_zero hf
    simp [suffixCounterDensity, Nat.not_le.mpr hlt]
  rw [hright]
  exact not_le_of_gt
    (configurationRankSuffixBarrier_suffixCounterDensity_pos
      k r e.rank)

/-- The same failure occurs with strictly positive density floors bounded
by one.  Therefore positivity of the scheduled floors does not repair the
suffix comparison. -/
theorem
    not_configurationRankSuffixBarrier_le_erase_of_lowerFace_positive
    {k r : ℕ}
    (s : Finset (PositiveOrderedFace k r))
    (e f : PositiveOrderedFace k r)
    (hf : f ∈ s.erase e)
    (hlt : f.rank < e.rank) :
    ¬ configurationRankSuffixBarrier
          k r
          (positiveSuffixCounterDensity k r e.rank)
          e.rank ≤
        configurationHalfDensityBarrier
          (positiveSuffixCounterDensity k r e.rank)
          (s.erase e) := by
  let B :=
    configurationRankSuffixBarrier
      k r (suffixCounterDensity e.rank) e.rank
  let α := positiveSuffixCounterDensity k r e.rank
  have hBpos : 0 < B :=
    configurationRankSuffixBarrier_suffixCounterDensity_pos
      k r e.rank
  have hα0 : ∀ n, 0 ≤ α n :=
    fun n =>
      (positiveSuffixCounterDensity_pos
        k r e.rank n).le
  have hα1 : ∀ n, α n ≤ 1 :=
    fun n =>
      positiveSuffixCounterDensity_le_one
        k r e.rank n
  have hαf : α f.rank = B := by
    simp [α, positiveSuffixCounterDensity,
      Nat.not_le.mpr hlt, B]
  have hrest :
      configurationHalfDensityBarrier
          α ((s.erase e).erase f) ≤ 1 :=
    configurationHalfDensityBarrier_le_one
      α hα0 hα1 _
  have hright :
      configurationHalfDensityBarrier α (s.erase e) ≤
        B / 2 := by
    rw [configurationHalfDensityBarrier_eq_mul_erase
      α (s.erase e) f hf, hαf]
    exact mul_le_of_le_one_right
      (div_nonneg hBpos.le (by norm_num)) hrest
  have hleft :
      configurationRankSuffixBarrier k r α e.rank = B := by
    exact
      configurationRankSuffixBarrier_positiveSuffixCounterDensity
        k r e.rank
  rw [show positiveSuffixCounterDensity k r e.rank = α by rfl]
  rw [hleft]
  intro h
  have : B ≤ B / 2 := h.trans hright
  linarith

end Submission.GreenTao
