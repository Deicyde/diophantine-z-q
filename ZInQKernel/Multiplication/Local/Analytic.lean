import ZInQKernel.Multiplication.Local.Valuations

/-!
# Convergent series in a complete discretely valued field

For a field `K` with a valuation `Valued.v : K → ℤᵐ⁰`, `vK K = ordOf Valued.v` is the
additive valuation `K → ℤ ∪ {∞}`. This file provides the three facts about series used for the
formal logarithm:

* `nonarchimedean_valued`: the valuation topology is nonarchimedean;
* `summable_of_vK`: in a complete such field, a sequence whose valuations tend to `∞` is
  summable;
* `le_vK_tsum`: a valuation lower bound for all terms passes to the sum.
-/

namespace ZInQ.Mult

open Filter Topology WithZero

variable (K : Type*) [Field K] [Valued K ℤᵐ⁰]

/-- The additive valuation `K → ℤ ∪ {∞}` of a `ℤᵐ⁰`-valued field. -/
noncomputable abbrev vK : AddValuation K (WithTop ℤ) := ordOf Valued.v

variable {K}

theorem vK_le_vK_iff (a b : K) : vK K a ≤ vK K b ↔ Valued.v b ≤ Valued.v a := by
  by_cases ha : a = 0
  · subst ha; simp
  by_cases hb : b = 0
  · subst hb; simp [ordOf_apply _ ha]
  have hva : (Valued.v a : ℤᵐ⁰) ≠ 0 := (Valuation.ne_zero_iff _).mpr ha
  have hvb : (Valued.v b : ℤᵐ⁰) ≠ 0 := (Valuation.ne_zero_iff _).mpr hb
  rw [ordOf_apply _ ha, ordOf_apply _ hb, WithTop.coe_le_coe, ← log_le_log hvb hva]
  omega

/-- The valuation topology of a `ℤᵐ⁰`-valued field is nonarchimedean. -/
theorem nonarchimedean_valued : NonarchimedeanAddGroup K where
  is_nonarchimedean U hU := by
    obtain ⟨γ, -, hγ⟩ := (Valued.hasBasis_nhds_zero K ℤᵐ⁰).mem_iff.mp hU
    exact ⟨⟨(Valued.v.restrict).ltAddSubgroup γ, Valued.isOpen_ball K γ.1⟩, hγ⟩

/-- Every neighbourhood of `0` contains a set `{x : v(x) ≥ M}`. -/
theorem exists_vge_subset {U : Set K} (hU : U ∈ 𝓝 (0 : K)) :
    ∃ M : ℤ, {x : K | (M : WithTop ℤ) ≤ vK K x} ⊆ U := by
  obtain ⟨γ, -, hγ⟩ := (Valued.hasBasis_nhds_zero K ℤᵐ⁰).mem_iff.mp hU
  set g : ℤᵐ⁰ := MonoidWithZeroHom.ValueGroup₀.embedding γ.1 with hg
  have hg0 : g ≠ 0 := (γ.isUnit.map MonoidWithZeroHom.ValueGroup₀.embedding).ne_zero
  refine ⟨1 - log g, fun x hx => hγ ?_⟩
  simp only [Set.mem_ofPred_eq] at hx ⊢
  rw [Valuation.restrict_lt_iff_lt_embedding, ← hg]
  rw [le_ordOf_iff] at hx
  refine lt_of_le_of_lt hx ?_
  conv_rhs => rw [← exp_log hg0]
  rw [exp_lt_exp]
  omega

theorem tendsto_zero_of_vK {f : ℕ → K} (h : ∀ M : ℤ, ∀ᶠ n in atTop, (M : WithTop ℤ) ≤ vK K (f n)) :
    Tendsto f atTop (𝓝 0) := by
  intro U hU
  obtain ⟨M, hM⟩ := exists_vge_subset hU
  exact (h M).mono fun n hn => hM hn

theorem tendsto_zero_of_vK' {ι : Type*} {l : Filter ι} {f : ι → K}
    (h : ∀ M : ℤ, ∀ᶠ i in l, (M : WithTop ℤ) ≤ vK K (f i)) : Tendsto f l (𝓝 0) := by
  intro U hU
  obtain ⟨M, hM⟩ := exists_vge_subset hU
  exact (h M).mono fun n hn => hM hn

/-- In a complete field, a family whose valuations tend to infinity along the cofinite filter is
summable. -/
theorem summable_of_vK_cofinite [CompleteSpace K] {ι : Type*} {f : ι → K}
    (h : ∀ M : ℤ, ∀ᶠ i in cofinite, (M : WithTop ℤ) ≤ vK K (f i)) : Summable f := by
  have := nonarchimedean_valued (K := K)
  exact NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero (tendsto_zero_of_vK' h)

/-- In a complete field, a sequence whose valuations tend to infinity is summable. -/
theorem summable_of_vK [CompleteSpace K] {f : ℕ → K}
    (h : ∀ M : ℤ, ∀ᶠ n in atTop, (M : WithTop ℤ) ≤ vK K (f n)) : Summable f := by
  have := nonarchimedean_valued (K := K)
  refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_
  rw [Nat.cofinite_eq_atTop]
  exact tendsto_zero_of_vK h

theorem isClosed_vK_ge (c : K) : IsClosed {x : K | vK K c ≤ vK K x} := by
  have : {x : K | vK K c ≤ vK K x} = {x : K | (Valued.v).restrict x ≤ (Valued.v).restrict c} := by
    ext x; simp only [Set.mem_ofPred_eq, Valuation.restrict_le_iff, vK_le_vK_iff]
  rw [this]
  exact Valued.isClosed_closedBall K _

/-- A lower bound `v(c)` for the valuations of all terms of a convergent series bounds the
valuation of its sum. -/
theorem le_vK_tsum {f : ℕ → K} (hf : Summable f) {c : K} (h : ∀ n, vK K c ≤ vK K (f n)) :
    vK K c ≤ vK K (∑' n, f n) := by
  have hS := isClosed_vK_ge c
  refine hS.mem_of_tendsto hf.hasSum.tendsto_sum_nat (Eventually.of_forall fun n => ?_)
  simp only [Set.mem_ofPred_eq]
  exact AddValuation.map_le_sum _ fun i _ => h i

theorem isClosed_vK_gt (c : K) : IsClosed {x : K | vK K c < vK K x} := by
  have : {x : K | vK K c < vK K x} = {x : K | (Valued.v).restrict x < (Valued.v).restrict c} := by
    ext x
    simp only [Set.mem_ofPred_eq, lt_iff_not_ge, vK_le_vK_iff,
      Valuation.restrict_le_iff]
  rw [this]
  exact Valued.isClosed_ball K _

/-- A strict lower bound `v(c)` for the valuations of all terms bounds the sum strictly. -/
theorem lt_vK_tsum {f : ℕ → K} (hf : Summable f) {c : K} (h : ∀ n, vK K c < vK K (f n)) :
    vK K c < vK K (∑' n, f n) := by
  have hS := isClosed_vK_gt c
  refine hS.mem_of_tendsto hf.hasSum.tendsto_sum_nat (Eventually.of_forall fun n => ?_)
  simp only [Set.mem_ofPred_eq]
  exact AddValuation.map_lt_sum' _ (lt_of_lt_of_le (h 0) le_top) fun i _ => h i

/-- The same with an integer bound, given a uniformizer `ϖ` (`v(ϖ) = 1`). -/
theorem le_vK_tsum_of_int {f : ℕ → K} (hf : Summable f) {ϖ : K} (hϖ : vK K ϖ = 1) (M : ℤ)
    (h : ∀ n, (M : WithTop ℤ) ≤ vK K (f n)) : (M : WithTop ℤ) ≤ vK K (∑' n, f n) := by
  have hϖ0 : ϖ ≠ 0 := by
    intro h0; rw [h0, (vK K).map_zero] at hϖ; exact WithTop.top_ne_coe hϖ
  have hc : vK K (ϖ ^ M) = M := by
    have := val_zpow_coe (v := vK K) (show vK K ϖ = ((1 : ℤ) : WithTop ℤ) from hϖ) M
    rw [this, mul_one]
  rw [← hc] at h ⊢
  exact le_vK_tsum hf h

end ZInQ.Mult
