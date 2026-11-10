-- Modified in this repository (2026, port to Lean 4.35.0 and Mathlib 56a00585): see ThirdParty/GreenTao/NOTICE.md.
import Submission.Hypergraph.ConfigurationWeightedCounting

/-!
# Rank-prefix parameters for nonlinear configuration counting

The abstract barrier theorem in `ConfigurationWeightedCounting` becomes
triangular after observing that the face recursion always removes a
maximum-rank face.  When a rank-`j` face is removed, every remaining face
has rank at most `j`.  If every density floor lies in `[0,1]`, the product
over *all* faces of rank at most `j` is therefore a lower bound for the
product over the actual remaining family.

This file turns that observation into a concrete sufficient condition.
With

```
qₑ = αₑ / 2
L(s) = ∏ e ∈ s, qₑ
Pⱼ = ∏ e with rank(e) ≤ j, qₑ,
```

it is enough to require

```
βⱼ ≤ (αⱼ / 4)² Pⱼ,
τⱼ ≤ (αⱼ / 4) Pⱼ.
```

The defect and uniform errors then spend one quarter of
`αⱼ L(s \ {e})` each, while `L(s)` spends the remaining half.  Crucially,
the rank-`j` thresholds depend only on density floors at ranks at most `j`,
not on the complete product through higher ranks.  This is the numerical
shape needed for the top-down dense-removal hierarchy.
-/

namespace Submission.GreenTao

open scoped BigOperators

/-! ## Product barriers and rank prefixes -/

/-- Positive ordered faces of rank at most `j`. -/
noncomputable def positiveOrderedFacesUpToRank
    (k r j : ℕ) : Finset (PositiveOrderedFace k r) :=
  Finset.univ.filter fun e => e.rank ≤ j

@[simp]
theorem mem_positiveOrderedFacesUpToRank
    {k r j : ℕ} (e : PositiveOrderedFace k r) :
    e ∈ positiveOrderedFacesUpToRank k r j ↔ e.rank ≤ j := by
  simp [positiveOrderedFacesUpToRank]

/-- The multiplicative half-density barrier on a selected face family. -/
noncomputable def configurationHalfDensityBarrier
    {k r : ℕ} (α : ℕ → ℝ)
    (s : Finset (PositiveOrderedFace k r)) : ℝ :=
  ∏ e ∈ s, α e.rank / 2

/-- The universal half-density product through rank `j`. -/
noncomputable def configurationRankPrefixBarrier
    (k r : ℕ) (α : ℕ → ℝ) (j : ℕ) : ℝ :=
  configurationHalfDensityBarrier α
    (positiveOrderedFacesUpToRank k r j)

@[simp]
theorem configurationHalfDensityBarrier_empty
    {k r : ℕ} (α : ℕ → ℝ) :
    configurationHalfDensityBarrier
      (k := k) (r := r) α ∅ = 1 := by
  simp [configurationHalfDensityBarrier]

theorem configurationHalfDensityBarrier_nonneg
    {k r : ℕ} (α : ℕ → ℝ)
    (hα : ∀ n, 0 ≤ α n)
    (s : Finset (PositiveOrderedFace k r)) :
    0 ≤ configurationHalfDensityBarrier α s := by
  unfold configurationHalfDensityBarrier
  exact Finset.prod_nonneg fun e _he =>
    div_nonneg (hα e.rank) (by norm_num)

theorem configurationRankPrefixBarrier_nonneg
    (k r : ℕ) (α : ℕ → ℝ)
    (hα : ∀ n, 0 ≤ α n) (j : ℕ) :
    0 ≤ configurationRankPrefixBarrier k r α j :=
  configurationHalfDensityBarrier_nonneg α hα _

/-- Removing one selected face splits off its half-density factor. -/
theorem configurationHalfDensityBarrier_eq_mul_erase
    {k r : ℕ} (α : ℕ → ℝ)
    (s : Finset (PositiveOrderedFace k r))
    (e : PositiveOrderedFace k r) (he : e ∈ s) :
    configurationHalfDensityBarrier α s =
      (α e.rank / 2) *
        configurationHalfDensityBarrier α (s.erase e) := by
  classical
  unfold configurationHalfDensityBarrier
  rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem he]
  simp only [Finset.sdiff_singleton_eq_erase]

/-- A maximum-rank remainder is contained in the corresponding universal
rank prefix. -/
theorem erase_subset_positiveOrderedFacesUpToRank_of_max
    {k r : ℕ}
    (s : Finset (PositiveOrderedFace k r))
    (e : PositiveOrderedFace k r)
    (hmax : ∀ f ∈ s, f.rank ≤ e.rank) :
    s.erase e ⊆
      positiveOrderedFacesUpToRank k r e.rank := by
  intro f hf
  rw [mem_positiveOrderedFacesUpToRank]
  exact hmax f (Finset.mem_of_mem_erase hf)

/-- Products of factors in `[0,1]` reverse inclusion.  Hence the universal
rank-prefix product is below the product on the actual maximum-rank
remainder. -/
theorem configurationRankPrefixBarrier_le_erase
    {k r : ℕ} (α : ℕ → ℝ)
    (hα0 : ∀ n, 0 ≤ α n)
    (hα1 : ∀ n, α n ≤ 1)
    (s : Finset (PositiveOrderedFace k r))
    (e : PositiveOrderedFace k r)
    (hmax : ∀ f ∈ s, f.rank ≤ e.rank) :
    configurationRankPrefixBarrier k r α e.rank ≤
      configurationHalfDensityBarrier α (s.erase e) := by
  classical
  unfold configurationRankPrefixBarrier
    configurationHalfDensityBarrier
  apply Finset.prod_le_prod_of_subset_of_le_one₀
    (erase_subset_positiveOrderedFacesUpToRank_of_max
      s e hmax)
  · intro f _hf
    exact div_nonneg (hα0 f.rank) (by norm_num)
  · intro f _hf _hnot
    have := hα1 f.rank
    linarith [hα0 f.rank]

/-! ## Quarter-budget arithmetic -/

/-- The prefix defect threshold controls the square-root error on every
larger actual remainder barrier. -/
theorem sqrt_mul_configurationHalfDensityBarrier_le_quarter
    {k r : ℕ} (α β : ℕ → ℝ)
    (hα0 : ∀ n, 0 ≤ α n)
    (hα1 : ∀ n, α n ≤ 1)
    (hβprefix :
      ∀ j,
        β j ≤
          (α j / 4) ^ 2 *
            configurationRankPrefixBarrier k r α j)
    (s : Finset (PositiveOrderedFace k r))
    (e : PositiveOrderedFace k r)
    (hmax : ∀ f ∈ s, f.rank ≤ e.rank) :
    Real.sqrt
        (β e.rank *
          configurationHalfDensityBarrier α (s.erase e)) ≤
      (α e.rank / 4) *
        configurationHalfDensityBarrier α (s.erase e) := by
  let L :=
    configurationHalfDensityBarrier α (s.erase e)
  have hprefix :
      configurationRankPrefixBarrier k r α e.rank ≤ L := by
    exact configurationRankPrefixBarrier_le_erase
      α hα0 hα1 s e hmax
  have hL : 0 ≤ L :=
    configurationHalfDensityBarrier_nonneg α hα0 _
  have hquarter : 0 ≤ α e.rank / 4 := by
    exact div_nonneg (hα0 e.rank) (by norm_num)
  have hβL :
      β e.rank * L ≤
        ((α e.rank / 4) * L) ^ 2 := by
    have hβ :
        β e.rank ≤ (α e.rank / 4) ^ 2 * L :=
      (hβprefix e.rank).trans
        (mul_le_mul_of_nonneg_left hprefix
          (sq_nonneg _))
    calc
      β e.rank * L ≤
          ((α e.rank / 4) ^ 2 * L) * L :=
        mul_le_mul_of_nonneg_right hβ hL
      _ = ((α e.rank / 4) * L) ^ 2 := by ring
  apply (Real.sqrt_le_iff).2
  exact ⟨mul_nonneg hquarter hL, hβL⟩

/-- The same prefix threshold is more than strong enough for the
monotonicity range required by the abstract nonlinear barrier theorem. -/
theorem beta_le_sq_mul_configurationHalfDensityBarrier
    {k r : ℕ} (α β : ℕ → ℝ)
    (hα0 : ∀ n, 0 ≤ α n)
    (hα1 : ∀ n, α n ≤ 1)
    (hβprefix :
      ∀ j,
        β j ≤
          (α j / 4) ^ 2 *
            configurationRankPrefixBarrier k r α j)
    (s : Finset (PositiveOrderedFace k r))
    (e : PositiveOrderedFace k r)
    (hmax : ∀ f ∈ s, f.rank ≤ e.rank) :
    β e.rank ≤
      α e.rank ^ 2 *
        configurationHalfDensityBarrier α (s.erase e) := by
  have hprefix :=
    configurationRankPrefixBarrier_le_erase
      α hα0 hα1 s e hmax
  have hL :
      0 ≤ configurationHalfDensityBarrier α (s.erase e) :=
    configurationHalfDensityBarrier_nonneg α hα0 _
  calc
    β e.rank ≤
        (α e.rank / 4) ^ 2 *
          configurationRankPrefixBarrier k r α e.rank :=
      hβprefix e.rank
    _ ≤
        (α e.rank / 4) ^ 2 *
          configurationHalfDensityBarrier α (s.erase e) :=
      mul_le_mul_of_nonneg_left hprefix (sq_nonneg _)
    _ ≤
        α e.rank ^ 2 *
          configurationHalfDensityBarrier α (s.erase e) := by
      apply mul_le_mul_of_nonneg_right _ hL
      nlinarith [sq_nonneg (α e.rank)]

/-! ## Concrete triangular counting theorems -/

/-- Rank-prefix defect and uniform thresholds put the complete half-density
product below every mixed-good full configuration count.

The uniform threshold is indexed by the lower-rank coordinate of the face,
while its allowed size is triangular in the face rank.  This matches the
actual ordered-complex regularity interface. -/
theorem
    configurationHalfDensityBarrier_le_fullConfigurationCount_of_rankPrefixBounds
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (α β : ℕ → ℝ)
    (hgood : A.IsMixedGood P α β)
    (τ : OrderedRegularityTolerance r)
    (hregular :
      IsFullyMixedPreliminaryOrderedRegular P τ)
    (hαpos : ∀ n, 0 < α n)
    (hα1 : ∀ n, α n ≤ 1)
    (hβ0 : ∀ n, 0 ≤ β n)
    (hβprefix :
      ∀ j,
        β j ≤
          (α j / 4) ^ 2 *
            configurationRankPrefixBarrier k r α j)
    (hτprefix :
      ∀ (e : PositiveOrderedFace k r),
        τ e.lowerRank ≤
          (α e.rank / 4) *
            configurationRankPrefixBarrier k r α e.rank) :
    configurationHalfDensityBarrier
        (k := k) (r := r) α Finset.univ ≤
      fullConfigurationCount A := by
  let barrier :
      Finset (PositiveOrderedFace k r) → ℝ :=
    configurationHalfDensityBarrier α
  have hα0 : ∀ n, 0 ≤ α n :=
    fun n => (hαpos n).le
  have hbarrier : ∀ s, 0 ≤ barrier s :=
    fun s =>
      configurationHalfDensityBarrier_nonneg α hα0 s
  change barrier Finset.univ ≤ fullConfigurationCount A
  apply
    configurationWeightedBarrier_le_fullConfigurationCount
      P A α β hgood τ hregular barrier
      hα0 hβ0 hbarrier
      (by simp [barrier])
      (fun s _hclosed e _he hmax =>
        beta_le_sq_mul_configurationHalfDensityBarrier
          α β hα0 hα1 hβprefix s e hmax)
      ?_
  intro s _hclosed e he hmax
  have hsqrt :=
    sqrt_mul_configurationHalfDensityBarrier_le_quarter
      α β hα0 hα1 hβprefix s e hmax
  have hprefix :=
    configurationRankPrefixBarrier_le_erase
      α hα0 hα1 s e hmax
  have hquarter : 0 ≤ α e.rank / 4 := by
    exact div_nonneg (hα0 e.rank) (by norm_num)
  have hτ :
      τ e.lowerRank ≤
        (α e.rank / 4) *
          configurationHalfDensityBarrier α (s.erase e) :=
    (hτprefix e).trans
      (mul_le_mul_of_nonneg_left hprefix hquarter)
  dsimp only [barrier]
  rw [configurationHalfDensityBarrier_eq_mul_erase
    α s e he]
  linarith

/-- Strictly positive rank-prefix density floors therefore give a positive
full configuration count. -/
theorem fullConfigurationCount_pos_of_rankPrefixBounds
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (α β : ℕ → ℝ)
    (hgood : A.IsMixedGood P α β)
    (τ : OrderedRegularityTolerance r)
    (hregular :
      IsFullyMixedPreliminaryOrderedRegular P τ)
    (hαpos : ∀ n, 0 < α n)
    (hα1 : ∀ n, α n ≤ 1)
    (hβ0 : ∀ n, 0 ≤ β n)
    (hβprefix :
      ∀ j,
        β j ≤
          (α j / 4) ^ 2 *
            configurationRankPrefixBarrier k r α j)
    (hτprefix :
      ∀ (e : PositiveOrderedFace k r),
        τ e.lowerRank ≤
          (α e.rank / 4) *
            configurationRankPrefixBarrier k r α e.rank) :
    0 < fullConfigurationCount A := by
  have hbarrier :
      0 <
        configurationHalfDensityBarrier α
          (Finset.univ :
            Finset (PositiveOrderedFace k r)) := by
    unfold configurationHalfDensityBarrier
    exact Finset.prod_pos fun e _he =>
      div_pos (hαpos e.rank) (by norm_num)
  exact hbarrier.trans_le
    (configurationHalfDensityBarrier_le_fullConfigurationCount_of_rankPrefixBounds
      P A α β hgood τ hregular hαpos hα1 hβ0
      hβprefix hτprefix)

end Submission.GreenTao
