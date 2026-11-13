import Submission.Hypergraph.ConfigurationWeightedDefect

/-!
# Nonlinear configuration-weighted counting

`ConfigurationWeightedDefect` proves the sharp one-face estimate

```
|C(s) - dₑ C(s \ {e})| ≤
  sqrt (βₑ C(s \ {e})) + τₑ.
```

The usual counting lemma discards the remaining count by using
`C(s \ {e}) ≤ 1`.  That turns the defect into the additive error
`sqrt βₑ` and forces every defect threshold to be smaller than the square
of the complete density product.

This file retains the remaining count through the whole downward-closed
recursion.  A nonnegative barrier `L(s)` propagates provided that, whenever
a maximum-rank face `e` is removed,

```
βₑ ≤ αₑ² L(s \ {e})
```

and

```
L(s) + sqrt (βₑ L(s \ {e})) + τₑ
  ≤ αₑ L(s \ {e}).
```

The first inequality is exactly the monotonicity range of
`x ↦ αₑ x - sqrt (βₑ x)`.  Consequently a lower bound for the remaining
configuration count can be substituted into the nonlinear error without
replacing it by `sqrt βₑ`.  This is the rank-hierarchical counting interface
needed by the dense-removal selector.
-/

namespace Submission.GreenTao

open scoped BigOperators

/-! ## Scalar monotonicity in the admissible range -/

/-- If `β ≤ α² L`, then the nonlinear main term
`x ↦ α * x - sqrt (β * x)` is increasing from `L` onward. -/
theorem mul_sub_sqrt_mul_mono_of_small
    {α β L C : ℝ}
    (hα : 0 ≤ α)
    (hβ : 0 ≤ β)
    (hL : 0 ≤ L)
    (hLC : L ≤ C)
    (hsmall : β ≤ α ^ 2 * L) :
    α * L - Real.sqrt (β * L) ≤
      α * C - Real.sqrt (β * C) := by
  have hC : 0 ≤ C := hL.trans hLC
  have hsqrtLC : Real.sqrt L ≤ Real.sqrt C :=
    Real.sqrt_le_sqrt hLC
  have hsqrtβ :
      Real.sqrt β ≤ α * Real.sqrt L := by
    apply (Real.sqrt_le_iff).2
    constructor
    · exact mul_nonneg hα (Real.sqrt_nonneg L)
    · calc
        β ≤ α ^ 2 * L := hsmall
        _ = (α * Real.sqrt L) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hL]
  have hfirst :
      0 ≤ Real.sqrt C - Real.sqrt L := by
    linarith
  have hsecond :
      0 ≤
        α * (Real.sqrt C + Real.sqrt L) -
          Real.sqrt β := by
    have hsum :
        Real.sqrt L ≤ Real.sqrt C + Real.sqrt L := by
      linarith [Real.sqrt_nonneg C]
    have hαsum :
        α * Real.sqrt L ≤
          α * (Real.sqrt C + Real.sqrt L) :=
      mul_le_mul_of_nonneg_left hsum hα
    linarith
  rw [Real.sqrt_mul hβ, Real.sqrt_mul hβ]
  nlinarith [mul_nonneg hfirst hsecond,
    Real.sq_sqrt hL, Real.sq_sqrt hC]

/-- One approximate weighted recurrence step transports a lower barrier.

The actual density `d` may be larger than the scheduled floor `α`.  The
remaining actual count `C` may also be larger than its barrier `L`; the
smallness condition is precisely what makes that replacement valid inside
the square-root error. -/
theorem weightedCount_step_lower
    {S C d α β τ L : ℝ}
    (hα : 0 ≤ α)
    (hβ : 0 ≤ β)
    (hL : 0 ≤ L)
    (hLC : L ≤ C)
    (hαd : α ≤ d)
    (hsmall : β ≤ α ^ 2 * L)
    (hstep :
      |S - d * C| ≤ Real.sqrt (β * C) + τ) :
    α * L - Real.sqrt (β * L) - τ ≤ S := by
  have hC : 0 ≤ C := hL.trans hLC
  have hdensity :
      α * C ≤ d * C :=
    mul_le_mul_of_nonneg_right hαd hC
  have hmono :=
    mul_sub_sqrt_mul_mono_of_small
      hα hβ hL hLC hsmall
  have hlower :
      d * C - (Real.sqrt (β * C) + τ) ≤ S := by
    have := (abs_le.mp hstep).1
    linarith
  linarith

/-! ## Downward-closed barrier recursion -/

/-- A barrier satisfying the nonlinear maximum-face recurrence is a lower
bound for every downward-closed partial configuration count.

The recursion removes a maximum-rank face, so downward closure is preserved
at every induction step.  No artificial totalization on non-closed face
families is required. -/
theorem configurationWeightedBarrier_le_partialConfigurationCount
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (α β : ℕ → ℝ)
    (hgood : A.IsMixedGood P α β)
    (τ : OrderedRegularityTolerance r)
    (hregular :
      IsFullyMixedPreliminaryOrderedRegular P τ)
    (barrier :
      Finset (PositiveOrderedFace k r) → ℝ)
    (hα : ∀ n, 0 ≤ α n)
    (hβ : ∀ n, 0 ≤ β n)
    (hbarrier : ∀ s, 0 ≤ barrier s)
    (hempty : barrier ∅ ≤ 1)
    (hsmall :
      ∀ (s : Finset (PositiveOrderedFace k r)),
        IsDownwardClosedPositiveFaces s →
        ∀ (e : PositiveOrderedFace k r), e ∈ s →
          (∀ f ∈ s, f.rank ≤ e.rank) →
          β e.rank ≤
            α e.rank ^ 2 * barrier (s.erase e))
    (hrecur :
      ∀ (s : Finset (PositiveOrderedFace k r)),
        IsDownwardClosedPositiveFaces s →
        ∀ (e : PositiveOrderedFace k r), e ∈ s →
          (∀ f ∈ s, f.rank ≤ e.rank) →
          barrier s +
                Real.sqrt
                  (β e.rank * barrier (s.erase e)) +
              τ e.lowerRank ≤
            α e.rank * barrier (s.erase e)) :
    ∀ (s : Finset (PositiveOrderedFace k r)),
      IsDownwardClosedPositiveFaces s →
      barrier s ≤ partialConfigurationCount A s := by
  classical
  intro s
  induction hsCard : s.card using Nat.strong_induction_on
      generalizing s with
  | h n ih =>
      intro hclosed
      by_cases hs : s = ∅
      · subst s
        simpa [partialConfigurationCount_empty] using hempty
      · have hsNonempty : s.Nonempty :=
          Finset.nonempty_iff_ne_empty.mpr hs
        obtain ⟨e, he, hmax⟩ :=
          exists_maxRank_mem s hsNonempty
        have hclosedErase :
            IsDownwardClosedPositiveFaces (s.erase e) :=
          hclosed.erase_maxRank he hmax
        have hcardErase :
            (s.erase e).card < n := by
          rw [← hsCard]
          exact Finset.card_erase_lt_of_mem he
        have hremaining :
            barrier (s.erase e) ≤
              partialConfigurationCount A (s.erase e) :=
          ih (s.erase e).card hcardErase
            (s.erase e) rfl hclosedErase
        have hstep :=
          abs_partialConfigurationCount_sub_mixedDensity_mul_le_sqrt
            P A α β hgood τ hregular
            s hclosed e he
            (fun f hf =>
              hmax f (Finset.mem_of_mem_erase hf))
            (hβ e.rank)
        have hlower :=
          weightedCount_step_lower
            (hα e.rank) (hβ e.rank)
            (hbarrier (s.erase e))
            hremaining
            (mixedConfigurationCoarseDensity_lower
              P A α β hgood e)
            (hsmall s hclosed e he hmax)
            hstep
        have hrec := hrecur s hclosed e he hmax
        linarith

/-- Full-configuration specialization of the nonlinear barrier theorem. -/
theorem configurationWeightedBarrier_le_fullConfigurationCount
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (α β : ℕ → ℝ)
    (hgood : A.IsMixedGood P α β)
    (τ : OrderedRegularityTolerance r)
    (hregular :
      IsFullyMixedPreliminaryOrderedRegular P τ)
    (barrier :
      Finset (PositiveOrderedFace k r) → ℝ)
    (hα : ∀ n, 0 ≤ α n)
    (hβ : ∀ n, 0 ≤ β n)
    (hbarrier : ∀ s, 0 ≤ barrier s)
    (hempty : barrier ∅ ≤ 1)
    (hsmall :
      ∀ (s : Finset (PositiveOrderedFace k r)),
        IsDownwardClosedPositiveFaces s →
        ∀ (e : PositiveOrderedFace k r), e ∈ s →
          (∀ f ∈ s, f.rank ≤ e.rank) →
          β e.rank ≤
            α e.rank ^ 2 * barrier (s.erase e))
    (hrecur :
      ∀ (s : Finset (PositiveOrderedFace k r)),
        IsDownwardClosedPositiveFaces s →
        ∀ (e : PositiveOrderedFace k r), e ∈ s →
          (∀ f ∈ s, f.rank ≤ e.rank) →
          barrier s +
                Real.sqrt
                  (β e.rank * barrier (s.erase e)) +
              τ e.lowerRank ≤
            α e.rank * barrier (s.erase e)) :
    barrier Finset.univ ≤ fullConfigurationCount A := by
  exact
    configurationWeightedBarrier_le_partialConfigurationCount
      P A α β hgood τ hregular barrier
      hα hβ hbarrier hempty hsmall hrecur
      Finset.univ downwardClosed_univ

/-- A strictly positive full barrier gives a positive configuration count. -/
theorem fullConfigurationCount_pos_of_configurationWeightedBarrier
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (α β : ℕ → ℝ)
    (hgood : A.IsMixedGood P α β)
    (τ : OrderedRegularityTolerance r)
    (hregular :
      IsFullyMixedPreliminaryOrderedRegular P τ)
    (barrier :
      Finset (PositiveOrderedFace k r) → ℝ)
    (hα : ∀ n, 0 ≤ α n)
    (hβ : ∀ n, 0 ≤ β n)
    (hbarrier : ∀ s, 0 ≤ barrier s)
    (hempty : barrier ∅ ≤ 1)
    (hsmall :
      ∀ (s : Finset (PositiveOrderedFace k r)),
        IsDownwardClosedPositiveFaces s →
        ∀ (e : PositiveOrderedFace k r), e ∈ s →
          (∀ f ∈ s, f.rank ≤ e.rank) →
          β e.rank ≤
            α e.rank ^ 2 * barrier (s.erase e))
    (hrecur :
      ∀ (s : Finset (PositiveOrderedFace k r)),
        IsDownwardClosedPositiveFaces s →
        ∀ (e : PositiveOrderedFace k r), e ∈ s →
          (∀ f ∈ s, f.rank ≤ e.rank) →
          barrier s +
                Real.sqrt
                  (β e.rank * barrier (s.erase e)) +
              τ e.lowerRank ≤
            α e.rank * barrier (s.erase e))
    (hpositive : 0 < barrier Finset.univ) :
    0 < fullConfigurationCount A := by
  exact hpositive.trans_le
    (configurationWeightedBarrier_le_fullConfigurationCount
      P A α β hgood τ hregular barrier
      hα hβ hbarrier hempty hsmall hrecur)

end Submission.GreenTao
