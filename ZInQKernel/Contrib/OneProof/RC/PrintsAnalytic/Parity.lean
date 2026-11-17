import ZInQKernel.Contrib.OneProof.RC.PrintsAnalytic.Basic

/-!
# Lane RC8: uniqueness of continuations and the parity of the order at the centre

Let `N > 0`, let `F` be entire, and let `Λ_N(s) = N^{s/2} (2π)^{-s} Γ(s) F(s)` be its completion
(`completedL`). If `Λ_N(2 - s) = w Λ_N(s)` on the strip `0 < Re s < 2`, then the order of
vanishing `m` of `F` at the centre `s = 1` satisfies `(-1)^m = w`
(`parity_of_functional_equation`). In particular the root number of `E` (`RootNumber E w`) is
`(-1)^{ord_{s=1} L(E, s)}`.

**Proof.** The factor `N^{s/2} (2π)^{-s} Γ(s)` is analytic and nonzero on `Re s > 0`, so
`ord_{s=1} Λ_N = ord_{s=1} F = m` (`analyticOrderAt_completedL`). Write `Λ_N(s) = (s - 1)^m h(s)`
near `1`, with `h` analytic at `1` and `h(1) ≠ 0`. Since `(2 - s) - 1 = -(s - 1)`, the
functional equation reads `(-1)^m (s - 1)^m h(2 - s) = w (s - 1)^m h(s)` near `1`; cancelling
`(s - 1)^m` for `s ≠ 1` gives `(-1)^m h(2 - s) = w h(s)` on a punctured neighbourhood of `1`,
hence `(-1)^m h(1) = w h(1)` by continuity, and `(-1)^m = w`.

Main results (all PROVED):

* `IsEntireContinuation.eq`: an entire continuation of a Dirichlet series is unique (identity
  theorem); with `isLContinuation_eq` (from the lane's `Basic` module), `analyticRank_unique`.
* `completedL_factor_analyticAt`, `completedL_analyticAt`, `analyticOrderAt_completedL`.
* `neg_one_pow_eq_of_functional_equation` (a complex sign `w`) and
  `parity_of_functional_equation` (an integer sign `w`).
* `RootNumberAt.parity`, `rootNumber_parity`, `rootNumber_parity_of_analyticRank`:
  `(-1)^{ord_{s=1} L(E, s)} = w`, for every entire continuation of `L(E, s)`.
* `rootNumber_odd_of_neg_one`, `rootNumber_even_of_one`, `rootNumber_central_eq_zero_of_neg_one`,
  `rootNumber_analyticOrder_ne_zero_of_neg_one`.
* `rootNumber_eq_one_of_analyticRank_zero` (with `analyticRank_zero_iff` from the `Basic` module).
* `rootNumber_unique_of_ne_zero`, `rootNumber_unique_of_LSeries_ne_zero`: the sign of the
  functional equation is unique as soon as `L(E, s)` is not identically zero.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.PrintsAnalytic

open ZInQ.Contrib.CloudB3RC53 Filter
open scoped Topology

/-! ### Uniqueness of entire continuations -/

/-- **Entire continuations of a Dirichlet series are unique** (PROVED). If `F` and `G` are
entire and agree with `∑ aₙ n^{-s}` on `Re s > σ₀` and on `Re s > σ₁` respectively, then
`F = G`: both equal the series on the nonempty open half-plane `Re s > max σ₀ σ₁`, and two entire
functions that agree near one point agree everywhere (identity theorem). -/
theorem IsEntireContinuation.eq {a : ℕ → ℂ} {σ₀ σ₁ : ℝ} {F G : ℂ → ℂ}
    (hF : IsEntireContinuation a σ₀ F) (hG : IsEntireContinuation a σ₁ G) : F = G := by
  have hU : {s : ℂ | max σ₀ σ₁ < s.re} ∈ 𝓝 ((max σ₀ σ₁ + 1 : ℝ) : ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by
      show max σ₀ σ₁ < ((max σ₀ σ₁ + 1 : ℝ) : ℂ).re
      rw [Complex.ofReal_re]
      linarith)
  have hev : F =ᶠ[𝓝 ((max σ₀ σ₁ + 1 : ℝ) : ℂ)] G :=
    Filter.mem_of_superset hU fun s hs =>
      (hF.2 s (lt_of_le_of_lt (le_max_left _ _) hs)).trans
        (hG.2 s (lt_of_le_of_lt (le_max_right _ _) hs)).symm
  have hFa := Complex.analyticOnNhd_univ_iff_differentiable.mpr hF.1
  have hGa := Complex.analyticOnNhd_univ_iff_differentiable.mpr hG.1
  funext z
  exact hFa.eqOn_of_preconnected_of_eventuallyEq hGa isPreconnected_univ (Set.mem_univ _) hev
    (Set.mem_univ z)

/-- **The analytic rank is well defined** (PROVED): if `ord_{s=1} L(E, s) = r` and
`ord_{s=1} L(E, s) = r'` (`AnalyticRank`), then `r = r'`, since the continuation is unique. -/
theorem analyticRank_unique {E : WeierstrassCurve ℚ} {r r' : ℕ} (h : AnalyticRank E r)
    (h' : AnalyticRank E r') : r = r' := by
  obtain ⟨F, hFd, hFL, hF⟩ := h
  obtain ⟨G, hGd, hGL, hG⟩ := h'
  obtain rfl : F = G := isLContinuation_eq ⟨hFd, hFL⟩ ⟨hGd, hGL⟩
  exact_mod_cast hF.symm.trans hG

/-! ### The completion factor -/

/-- **The completion factor is analytic on `Re s > 0`** (PROVED): for `N > 0` the function
`s ↦ N^{s/2} (2π)^{-s} Γ(s)` is complex analytic at every point `s` with `Re s > 0`. -/
theorem completedL_factor_analyticAt {N : ℕ} (hN : 0 < N) {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ
      (fun z : ℂ => (N : ℂ) ^ (z / 2) * (2 * Real.pi : ℂ) ^ (-z) * Complex.Gamma z) s := by
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hpi : (2 * Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)
  have hd : DifferentiableOn ℂ
      (fun z : ℂ => (N : ℂ) ^ (z / 2) * (2 * Real.pi : ℂ) ^ (-z) * Complex.Gamma z)
      {z : ℂ | 0 < z.re} := by
    intro z hz
    have hz' : 0 < z.re := hz
    have hΓ : DifferentiableAt ℂ Complex.Gamma z := by
      refine Complex.differentiableAt_Gamma z fun k hk => ?_
      rw [hk, Complex.neg_re, Complex.natCast_re] at hz'
      linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    have h1 : DifferentiableAt ℂ (fun z : ℂ => (N : ℂ) ^ (z / 2)) z :=
      (differentiableAt_id.div_const 2).const_cpow (Or.inl hN')
    have h2 : DifferentiableAt ℂ (fun z : ℂ => (2 * Real.pi : ℂ) ^ (-z)) z :=
      differentiableAt_id.neg.const_cpow (Or.inl hpi)
    exact ((h1.mul h2).mul hΓ).differentiableWithinAt
  exact hd.analyticAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs)

/-- **The completed L-function is analytic on `Re s > 0`** (PROVED): for `N > 0` and `F`
entire, `Λ_N(s) = N^{s/2} (2π)^{-s} Γ(s) F(s)` is analytic at every `s` with `Re s > 0`. -/
theorem completedL_analyticAt {N : ℕ} (hN : 0 < N) {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    {s : ℂ} (hs : 0 < s.re) : AnalyticAt ℂ (completedL N F) s :=
  (completedL_factor_analyticAt hN hs).mul (hF.analyticAt s)

/-- **Completing does not change the order of vanishing on `Re s > 0`** (PROVED): for `N > 0`
and `F` entire, `ord_s Λ_N = ord_s F` whenever `Re s > 0`, because the factor
`N^{s/2} (2π)^{-s} Γ(s)` is analytic and nonzero there. -/
theorem analyticOrderAt_completedL {N : ℕ} (hN : 0 < N) {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    {s : ℂ} (hs : 0 < s.re) : analyticOrderAt (completedL N F) s = analyticOrderAt F s := by
  have hg := completedL_factor_analyticAt hN hs
  have hΛ : completedL N F =
      (fun z : ℂ => (N : ℂ) ^ (z / 2) * (2 * Real.pi : ℂ) ^ (-z) * Complex.Gamma z) * F := rfl
  rw [hΛ, analyticOrderAt_mul hg (hF.analyticAt s),
    hg.analyticOrderAt_eq_zero.mpr (completedL_factor_ne_zero hN hs), zero_add]

/-! ### Parity of the order of vanishing at the centre -/

/-- **Parity of the order at the centre, for a complex sign** (PROVED). Let `N > 0`, let `F` be
entire with `ord_{s=1} F = m` finite, and suppose `Λ_N(2 - s) = w Λ_N(s)` on `0 < Re s < 2` for
some `w ∈ ℂ`, where `Λ_N(s) = N^{s/2} (2π)^{-s} Γ(s) F(s)`. Then `w = (-1)^m`. -/
theorem neg_one_pow_eq_of_functional_equation {N : ℕ} (hN : 0 < N) {F : ℂ → ℂ}
    (hF : Differentiable ℂ F) {w : ℂ}
    (hFE : ∀ s : ℂ, 0 < s.re → s.re < 2 → completedL N F (2 - s) = w * completedL N F s)
    {m : ℕ} (hm : analyticOrderAt F 1 = m) : (-1 : ℂ) ^ m = w := by
  have h1re : (0 : ℝ) < (1 : ℂ).re := by norm_num
  -- `Λ_N(s) = (s - 1)^m h(s)` near `1`, with `h` analytic at `1` and `h(1) ≠ 0`
  obtain ⟨h, hha, hh1, hev⟩ := (completedL_analyticAt hN hF h1re).analyticOrderAt_eq_natCast.mp
    ((analyticOrderAt_completedL hN hF h1re).trans hm)
  -- the reflection `s ↦ 2 - s` fixes `1`
  have hT : Tendsto (fun s : ℂ => 2 - s) (𝓝 1) (𝓝 1) := by
    have h2 : Tendsto (fun s : ℂ => 2 - s) (𝓝 1) (𝓝 (2 - 1)) :=
      (continuous_const.sub continuous_id).tendsto 1
    rwa [show (2 : ℂ) - 1 = 1 by norm_num] at h2
  -- near `1` we are inside the strip `0 < Re s < 2`
  have hstrip : ∀ᶠ s in 𝓝 (1 : ℂ), 0 < s.re ∧ s.re < 2 :=
    ((Complex.continuous_re.tendsto 1).eventually (lt_mem_nhds h1re)).and
      ((Complex.continuous_re.tendsto 1).eventually
        (gt_mem_nhds (by norm_num : (1 : ℂ).re < 2)))
  -- on a punctured neighbourhood of `1`: `(-1)^m h(2 - s) = w h(s)`
  have hkey : ∀ᶠ s in 𝓝[≠] (1 : ℂ), (-1 : ℂ) ^ m * h (2 - s) = w * h s := by
    filter_upwards [hev.filter_mono nhdsWithin_le_nhds,
      (hT.eventually hev).filter_mono nhdsWithin_le_nhds,
      hstrip.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with s hs hs' hstr hne
    have hne' : s - 1 ≠ 0 := sub_ne_zero.mpr hne
    have hFEs := hFE s hstr.1 hstr.2
    rw [hs', hs] at hFEs
    simp only [smul_eq_mul] at hFEs
    rw [show (2 - s - 1 : ℂ) = -(s - 1) by ring, neg_pow] at hFEs
    apply mul_left_cancel₀ (pow_ne_zero m hne')
    linear_combination hFEs
  -- pass to the limit `s → 1`
  have hA : Tendsto (fun s : ℂ => (-1 : ℂ) ^ m * h (2 - s)) (𝓝[≠] 1)
      (𝓝 ((-1 : ℂ) ^ m * h 1)) :=
    (tendsto_const_nhds.mul (hha.continuousAt.tendsto.comp hT)).mono_left nhdsWithin_le_nhds
  have hB : Tendsto (fun s : ℂ => w * h s) (𝓝[≠] 1) (𝓝 (w * h 1)) :=
    (tendsto_const_nhds.mul hha.continuousAt.tendsto).mono_left nhdsWithin_le_nhds
  exact mul_right_cancel₀ hh1 (tendsto_nhds_unique_of_eventuallyEq hA hB hkey)

/-- **The parity of the order at the centre is the sign of the functional equation** (PROVED).
Let `N > 0`, `F` entire, `w ∈ ℤ`, and suppose the completion
`Λ_N(s) = N^{s/2} (2π)^{-s} Γ(s) F(s)` satisfies `Λ_N(2 - s) = w Λ_N(s)` on `0 < Re s < 2`. If
`F` vanishes to order exactly `m` at `s = 1`, then `(-1)^m = w` (so in particular `w = ±1`). -/
theorem parity_of_functional_equation {N : ℕ} (hN : 0 < N) {F : ℂ → ℂ}
    (hF : Differentiable ℂ F) {w : ℤ}
    (hFE : ∀ s : ℂ, 0 < s.re → s.re < 2 → completedL N F (2 - s) = w * completedL N F s)
    {m : ℕ} (hm : analyticOrderAt F 1 = m) : (-1 : ℤ) ^ m = w := by
  exact_mod_cast neg_one_pow_eq_of_functional_equation hN hF hFE hm

/-! ### Consequences for `L(E, s)` -/

/-- **Parity from a functional equation of `L(E, s)` at a given level** (PROVED). If
`RootNumberAt E N w` (a functional equation of level `N` and sign `w`), then every entire
continuation `F` of `L(E, s)` with `ord_{s=1} F = m` has `(-1)^m = w`. (The continuation in the
functional equation is `F` itself, by `isLContinuation_eq`.) -/
theorem RootNumberAt.parity {E : WeierstrassCurve ℚ} {N : ℕ} {w : ℤ} (h : RootNumberAt E N w)
    {F : ℂ → ℂ} (hF : IsLContinuation E F) {m : ℕ} (hm : analyticOrderAt F 1 = m) :
    (-1 : ℤ) ^ m = w := by
  obtain ⟨hN, G, hG, hFE⟩ := h
  obtain rfl : G = F := isLContinuation_eq hG hF
  exact parity_of_functional_equation hN hG.1 hFE hm

/-- **Parity of the analytic rank is the root number** (PROVED). If `w` is the root number of
`E/ℚ` (the sign of the functional equation of `L(E, s)`, `RootNumber E w`), then every entire
continuation `F` of `L(E, s)` with `ord_{s=1} F = m` has `(-1)^m = w`. -/
theorem rootNumber_parity {E : WeierstrassCurve ℚ} {w : ℤ} (h : RootNumber E w) {F : ℂ → ℂ}
    (hF : IsLContinuation E F) {m : ℕ} (hm : analyticOrderAt F 1 = m) : (-1 : ℤ) ^ m = w := by
  obtain ⟨N, hN⟩ := rootNumber_iff_exists_rootNumberAt.mp h
  exact hN.parity hF hm

/-- **Parity of the analytic rank is the root number, in terms of `AnalyticRank`** (PROVED): if
`RootNumber E w` and `ord_{s=1} L(E, s) = r`, then `(-1)^r = w`. -/
theorem rootNumber_parity_of_analyticRank {E : WeierstrassCurve ℚ} {w : ℤ} (h : RootNumber E w)
    {r : ℕ} (hr : AnalyticRank E r) : (-1 : ℤ) ^ r = w := by
  obtain ⟨F, hFd, hFL, hF⟩ := hr
  exact rootNumber_parity h ⟨hFd, hFL⟩ hF

/-- **Root number `-1` gives odd order at the centre** (PROVED): if `RootNumber E (-1)` and `F`
is an entire continuation of `L(E, s)` with `ord_{s=1} F = m`, then `m` is odd. -/
theorem rootNumber_odd_of_neg_one {E : WeierstrassCurve ℚ} (h : RootNumber E (-1))
    {F : ℂ → ℂ} (hF : IsLContinuation E F) {m : ℕ} (hm : analyticOrderAt F 1 = m) : Odd m :=
  (neg_one_pow_eq_neg_one_iff_odd (by decide)).mp (rootNumber_parity h hF hm)

/-- **Root number `+1` gives even order at the centre** (PROVED): if `RootNumber E 1` and `F` is
an entire continuation of `L(E, s)` with `ord_{s=1} F = m`, then `m` is even. -/
theorem rootNumber_even_of_one {E : WeierstrassCurve ℚ} (h : RootNumber E 1)
    {F : ℂ → ℂ} (hF : IsLContinuation E F) {m : ℕ} (hm : analyticOrderAt F 1 = m) : Even m :=
  (neg_one_pow_eq_one_iff_even (by decide)).mp (rootNumber_parity h hF hm)

/-- **Root number `-1` forces `L(E, 1) = 0`** (PROVED): if `RootNumber E (-1)`, then every entire
continuation `F` of `L(E, s)` vanishes at `s = 1`. -/
theorem rootNumber_central_eq_zero_of_neg_one {E : WeierstrassCurve ℚ} (h : RootNumber E (-1))
    {F : ℂ → ℂ} (hF : IsLContinuation E F) : F 1 = 0 := by
  by_contra hF1
  have h0 : analyticOrderAt F 1 = ((0 : ℕ) : ℕ∞) := by
    rw [Nat.cast_zero]
    exact (hF.1.analyticAt 1).analyticOrderAt_eq_zero.mpr hF1
  exact absurd (rootNumber_parity h hF h0) (by norm_num)

/-- **Root number `-1` forces positive order at the centre** (PROVED): if `RootNumber E (-1)`,
then every entire continuation `F` of `L(E, s)` has `ord_{s=1} F ≠ 0`. -/
theorem rootNumber_analyticOrder_ne_zero_of_neg_one {E : WeierstrassCurve ℚ}
    (h : RootNumber E (-1)) {F : ℂ → ℂ} (hF : IsLContinuation E F) : analyticOrderAt F 1 ≠ 0 :=
  (hF.1.analyticAt 1).analyticOrderAt_ne_zero.mpr (rootNumber_central_eq_zero_of_neg_one h hF)

/-- **Analytic rank zero forces root number `+1`** (PROVED): if `RootNumber E w` and
`ord_{s=1} L(E, s) = 0`, then `w = 1`. -/
theorem rootNumber_eq_one_of_analyticRank_zero {E : WeierstrassCurve ℚ} {w : ℤ}
    (h : RootNumber E w) (h0 : AnalyticRank E 0) : w = 1 := by
  have h1 := rootNumber_parity_of_analyticRank h h0
  rw [pow_zero] at h1
  exact h1.symm

/-! ### Uniqueness of the sign -/

/-- **An entire function that is not identically zero has finite order everywhere** (PROVED):
if `F` is entire and `F z ≠ 0` for some `z`, then `ord_s F < ∞` for every `s` (identity
theorem: infinite order at `s` means `F = 0` near `s`, hence everywhere). -/
theorem analyticOrderAt_ne_top_of_differentiable {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    {z : ℂ} (hz : F z ≠ 0) (s : ℂ) : analyticOrderAt F s ≠ ⊤ := by
  intro htop
  have hFa := Complex.analyticOnNhd_univ_iff_differentiable.mpr hF
  exact hz (hFa.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
    (Set.mem_univ s) (analyticOrderAt_eq_top.mp htop) (Set.mem_univ z))

/-- **The root number is unique once `L(E, s)` is not identically zero** (PROVED): if
`RootNumber E w` and `RootNumber E w'`, and some entire continuation `F` of `L(E, s)` takes a
nonzero value somewhere, then `w = w'` (both equal `(-1)^{ord_{s=1} F}`). -/
theorem rootNumber_unique_of_ne_zero {E : WeierstrassCurve ℚ} {w w' : ℤ} (h : RootNumber E w)
    (h' : RootNumber E w') {F : ℂ → ℂ} (hF : IsLContinuation E F) {z : ℂ} (hz : F z ≠ 0) :
    w = w' := by
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (analyticOrderAt_ne_top_of_differentiable hF.1 hz 1)
  rw [← rootNumber_parity h hF hm.symm, ← rootNumber_parity h' hF hm.symm]

/-- **The root number is unique once the Dirichlet series of `L(E, s)` is nonzero at one
point** (PROVED): if `RootNumber E w`, `RootNumber E w'`, and `L(E, s₀) ≠ 0` for some `s₀` with
`Re s₀ > 3/2`, then `w = w'`. -/
theorem rootNumber_unique_of_LSeries_ne_zero {E : WeierstrassCurve ℚ} {w w' : ℤ}
    (h : RootNumber E w) (h' : RootNumber E w') {s₀ : ℂ} (hs₀ : 3 / 2 < s₀.re)
    (hL : E.LSeries s₀ ≠ 0) : w = w' := by
  obtain ⟨F, hF⟩ : ∃ F : ℂ → ℂ, IsLContinuation E F := by
    obtain ⟨N, -, F, hF, -⟩ := h
    exact ⟨F, hF⟩
  refine rootNumber_unique_of_ne_zero h h' hF (z := s₀) ?_
  rw [hF.2 s₀ hs₀]
  exact hL

end ZInQ.Manuscript.RC.PrintsAnalytic
