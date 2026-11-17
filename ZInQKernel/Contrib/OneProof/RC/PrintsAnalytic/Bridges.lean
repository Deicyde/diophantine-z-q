import ZInQKernel.Contrib.OneProof.RC.PrintsAnalytic.BFH
import ZInQKernel.Contrib.OneProof.PoleS12.Leaves

/-!
# Lane RC8: bridges from genuine newforms to Mathlib's `L(E, s)`

`Newform.lean` states the lane's hypotheses about newforms (`ModularNewform`, `HasseConvergence`,
`TwistDictionary`) over Tau Ceti's genuine `HeckeRing.GL2.Newform`; `HoffsteinLuo.lean` and
`BFH.lean` state the prints of Hoffstein–Luo, of Bump–Friedberg–Hoffstein and Hecke's twisted
functional equation for newforms, together with their curve forms; the shared top layer states the
manuscript's analytic notions over Mathlib's `L(E, s)` (`IsLContinuation`, `AnalyticRank`,
`RootNumber`, with `RootNumberAt` in `Basic.lean`). This file proves the bridges between the two
vocabularies.

* `newformSign_eq_one_or_neg_one` (PROVED): the sign `i^k ε_N(f)` of a newform of trivial
  nebentypus is `1` or `-1`.
* `completedL_L_eq_frickeCompletedL` (PROVED): on `Re s > 0`, the completion
  `N^{s/2} (2π)^{-s} Γ(s) L(f, s)` (`completedL`) of Mathlib's `ModularForm.L` is Tau Ceti's
  level-`N` completion `Λ_N(s, f)`.
* `newform_functional_equation`, `newform_functional_equation_two` (PROVED): Hecke's functional
  equation in the `completedL` convention, `Λ_N(k - s) = i^k ε_N(f) Λ_N(s)` on `0 < Re s < k`.
* `isEntireContinuation_L` (PROVED): Mathlib's `ModularForm.L` is the entire continuation of
  `∑ a_n(f) n^{-s}` from `Re s > k/2 + 1` (the width of `Γ₁(N)` at `∞` is `1`).
* `isModular_of_isNewformOf`, `bcdtThmA_of_modularNewform` (PROVED): a newform of `E` gives a
  `Γ₀(N)` cusp form with the same `q`-expansion, so `ModularNewform` implies the tree's
  `PoleS12.BCDTThmA`.
* `eqOn_LSeries_of_forall_summable` (PROVED): the identity-theorem step moving an entire
  continuation of a Dirichlet series to its half-plane `Re s > 3/2` of absolute convergence.
* `isLContinuation_L_of_isNewformOf`, `eq_L_of_isLContinuation` (PROVED): `L(f, s)` is an entire
  continuation of `L(E, s)`, and the only one.
* `analyticRank_iff_newformAnalyticRank`, `analyticRankOne_iff_newformAnalyticRank` (PROVED):
  `ord_{s=1} L(E, s)` is Tau Ceti's `Newform.analyticRank` of the newform of `E`.
* `rootNumberAt_of_isNewformOf`, `rootNumber_of_isNewformOf`, `exists_rootNumber` (PROVED):
  `L(E, s)` satisfies the functional equation of the level `N` of the newform of `E`, with the
  sign of the newform; hence every elliptic curve over `ℚ` has a root number (`RootNumber`).
* `exists_ne_zero_pair`, `level_sign_unique` (PROVED): a nonzero entire function satisfies
  functional equations of at most one level and one sign.
* `eq_level_and_sign_of_rootNumberAt`, `rootNumberAt_unique`, `rootNumber_unique`,
  `rootNumber_eq_one_or_neg_one` (PROVED): the level and the sign of any functional equation of
  `L(E, s)` are those of the newform of `E`; so the root number is unique and is `±1`.
* `isLContinuation_qtwist` (PROVED): an entire continuation of `L(s, f, χ_D)` is an entire
  continuation of `L(E^{(D)}, s)`.
* `hoffsteinLuoCurve_of`, `twistedRootNumberCurve_of`, `bfhCurve_of` (PROVED): the curve forms
  `HoffsteinLuoCurve`, `TwistedRootNumberCurve` and `BFHCurve` from the newform prints
  `HoffsteinLuoTheorem`, `TwistedFunctionalEquation` and `BFHTheorem` with `ModularNewform`,
  `TwistDictionary` and `HasseConvergence` (`kronecker_eq_zero_of_dvd` and
  `isCoprime_of_forall_kronecker_eq_one`, PROVED, give the coprimality to the level in BFH).

**Why the strip.** Mathlib's `ModularForm.L hk f s` is defined as `Λ(s, f) · (2 / Γ_ℂ(s))` with
Mathlib's `Γ`, which takes the value `0` at `0, -1, -2, …`. On `Re s > 0` the factor `Γ(s)` is
nonzero, so `(2π)^{-s} Γ(s) L(f, s) = Λ(s, f)` there; on the strip `0 < Re s < k` this holds at
both `s` and `k - s`, and Tau Ceti's functional equation transfers verbatim.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.PrintsAnalytic

open ZInQ.Manuscript ZInQ.Contrib.CloudB3RC53 HeckeRing.GL2 UpperHalfPlane Complex
  CongruenceSubgroup

/-! ### The sign and the functional equation of a newform -/

/-- **The sign of a newform of trivial nebentypus is `±1`** (PROVED): `i^k ε_N(f) ∈ {1, -1}`
(Tau Ceti's `Newform.I_zpow_mul_frickeSign_eq_one_or_neg_one`). -/
theorem newformSign_eq_one_or_neg_one {N : ℕ} [NeZero N] {k : ℤ} (f : HeckeRing.GL2.Newform N k)
    (hχ : f.χ = 1) : newformSign f hχ = 1 ∨ newformSign f hχ = -1 :=
  f.I_zpow_mul_frickeSign_eq_one_or_neg_one hχ

/-- **The two completions agree on `Re s > 0`** (PROVED): for a newform `f` of positive weight,
`N^{s/2} (2π)^{-s} Γ(s) L(f, s) = Λ_N(s, f)`, where `L(f, s)` is Mathlib's `ModularForm.L` and
`Λ_N(s, f) = N^{s/2} Λ(s, f)` is Tau Ceti's `CuspForm.frickeCompletedL`. Mathlib defines
`L(f, s) = Λ(s, f) · 2 / Γ_ℂ(s)` with `Γ_ℂ(s) = 2 (2π)^{-s} Γ(s)`, and `Γ(s) ≠ 0` for `Re s > 0`. -/
theorem completedL_L_eq_frickeCompletedL {N : ℕ} [NeZero N] {k : ℤ} (hk : 0 < k)
    (f : Newform N k) {s : ℂ} (hs : 0 < s.re) :
    completedL N (ModularForm.L hk f.toCuspForm) s =
      CuspForm.frickeCompletedL f.toCuspForm (N.toPNat (NeZero.pos N)) s := by
  rw [CuspForm.frickeCompletedL_eq_cpow_mul_Λ f.toCuspForm _ hk s,
    show ((N.toPNat (NeZero.pos N) : ℕ+) : ℕ) = N from rfl]
  have hΓ : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hs
  have hpi0 : (2 * Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)
  have hpi : (2 * Real.pi : ℂ) ^ (-s) ≠ 0 :=
    fun h => hpi0 ((Complex.cpow_eq_zero_iff _ _).mp h).1
  simp only [completedL, ModularForm.L, Complex.Gammaℂ_def]
  field_simp

/-- **Hecke's functional equation in the `completedL` convention** (PROVED): for a newform `f` of
positive weight `k` and trivial nebentypus,
`Λ_N(k - s) = i^k ε_N(f) Λ_N(s)` for `0 < Re s < k`, with
`Λ_N(s) = N^{s/2} (2π)^{-s} Γ(s) L(f, s)` (`completedL`) and `L(f, s)` Mathlib's `ModularForm.L`.
This is Tau Ceti's `Newform.frickeCompletedL_sub_eq` transported by
`completedL_L_eq_frickeCompletedL` at `s` and at `k - s`, both of real part `> 0` on the strip. -/
theorem newform_functional_equation {N : ℕ} [NeZero N] {k : ℤ} (hk : 0 < k) (f : Newform N k)
    (hχ : f.χ = 1) : ∀ s : ℂ, 0 < s.re → s.re < k →
      completedL N (ModularForm.L hk f.toCuspForm) (k - s) =
        newformSign f hχ * completedL N (ModularForm.L hk f.toCuspForm) s := by
  intro s hs0 hsk
  have hks : 0 < ((k : ℂ) - s).re := by
    rw [Complex.sub_re, Complex.intCast_re]
    linarith
  rw [completedL_L_eq_frickeCompletedL hk f hks, completedL_L_eq_frickeCompletedL hk f hs0]
  exact f.frickeCompletedL_sub_eq hχ hk s

/-- **Hecke's functional equation in weight `2`** (PROVED): `newform_functional_equation` at
`k = 2`, with the strip written `0 < Re s < 2`. -/
theorem newform_functional_equation_two {N : ℕ} [NeZero N] (f : Newform N 2) (hχ : f.χ = 1) :
    ∀ s : ℂ, 0 < s.re → s.re < 2 →
      completedL N (ModularForm.L two_pos f.toCuspForm) (2 - s) =
        newformSign f hχ * completedL N (ModularForm.L two_pos f.toCuspForm) s := by
  intro s hs0 hs2
  have h := newform_functional_equation two_pos f hχ s hs0 (by exact_mod_cast hs2)
  simpa using h

/-- **`L(f, s)` is the entire continuation of `∑ a_n(f) n^{-s}`** (PROVED): Mathlib's
`ModularForm.L` is entire (`CuspForm.differentiable_L`) and equals `LSeries (nfCoeff f)` on
`Re s > k/2 + 1` (Tau Ceti's `CuspForm.LSeries_qExpansion_coeff_eq`, whose width factor
`h^{-s}` is `1` since `Γ₁(N)` has width `1` at `∞`). -/
theorem isEntireContinuation_L {N : ℕ} [NeZero N] {k : ℤ} (hk : 0 < k) (f : Newform N k) :
    IsEntireContinuation (nfCoeff f) ((k : ℝ) / 2 + 1) (ModularForm.L hk f.toCuspForm) := by
  refine ⟨CuspForm.differentiable_L hk f.toCuspForm, fun s hs => ?_⟩
  have h := CuspForm.LSeries_qExpansion_coeff_eq hk f.toCuspForm hs
  rw [strictWidthInfty_Gamma1, Complex.ofReal_one, Complex.one_cpow, one_mul] at h
  exact h.symm

/-! ### Modularity in the tree's vocabulary -/

/-- **A newform of `E` makes `E` modular in the tree's sense** (PROVED): the newform has trivial
nebentypus, so Tau Ceti's `cuspFormCharSpaceOneEquiv` re-reads it as a weight-2 cusp form on
`Γ₀(N)` with the same underlying function, hence the same `q`-expansion, whose coefficients are
those of `L(E, s)`. -/
theorem isModular_of_isNewformOf {E : WeierstrassCurve ℚ} {N : ℕ} [NeZero N] {f : Newform N 2}
    (hf : IsNewformOf E f) : PoleS12.IsModular E := by
  have hmem : f.toCuspForm ∈ cuspFormCharSpace 2 (1 : (ZMod N)ˣ →* ℂˣ) := by
    have h := f.mem_charSpace
    rwa [hf.1] at h
  refine ⟨N, NeZero.pos N, TauCeti.cuspFormCharSpaceOneEquiv N 2 ⟨f.toCuspForm, hmem⟩,
    fun n hn => ?_⟩
  rw [TauCeti.coe_cuspFormCharSpaceOneEquiv_apply]
  exact hf.2 n hn

/-- **`ModularNewform` implies the tree's `BCDTThmA`** (PROVED): by `isModular_of_isNewformOf`. -/
theorem bcdtThmA_of_modularNewform (h : ModularNewform) : PoleS12.BCDTThmA := by
  intro E hE
  obtain ⟨N, _, f, hf⟩ := h E hE
  exact isModular_of_isNewformOf hf

/-! ### Moving an entire continuation to `Re s > 3/2` -/

/-- **The identity-theorem step** (PROVED): if `F` is entire and equals `LSeries a` on
`Re s > σ₀`, and `∑ aₙ n^{-s}` converges absolutely on `Re s > 3/2`, then `F` equals
`LSeries a` on all of `Re s > 3/2`. The abscissa of absolute convergence is `≤ 3/2`, so
`LSeries a` is analytic on the half-plane `Re s > 3/2`, which is convex hence preconnected, and the
two analytic functions agree near the point `max σ₀ (3/2) + 1` of it. -/
theorem eqOn_LSeries_of_forall_summable {a : ℕ → ℂ} {σ₀ : ℝ} {F : ℂ → ℂ}
    (hF : Differentiable ℂ F) (hFa : ∀ s : ℂ, σ₀ < s.re → F s = LSeries a s)
    (ha : ∀ s : ℂ, 3 / 2 < s.re → LSeriesSummable a s) :
    ∀ s : ℂ, 3 / 2 < s.re → F s = LSeries a s := by
  have habs : LSeries.abscissaOfAbsConv a ≤ ((3 / 2 : ℝ) : EReal) :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy =>
      ha y (by rw [Complex.ofReal_re]; exact hy)
  have hLa : AnalyticOnNhd ℂ (LSeries a) {s : ℂ | 3 / 2 < s.re} :=
    (LSeries_analyticOnNhd a).mono fun s hs => lt_of_le_of_lt habs (EReal.coe_lt_coe_iff.mpr hs)
  have hFan : AnalyticOnNhd ℂ F {s : ℂ | 3 / 2 < s.re} := fun s _ => hF.analyticAt s
  have hU : IsPreconnected {s : ℂ | 3 / 2 < s.re} := (convex_halfSpace_re_gt (3 / 2)).isPreconnected
  set m : ℝ := max σ₀ (3 / 2)
  have hz : ((m + 1 : ℝ) : ℂ) ∈ {s : ℂ | 3 / 2 < s.re} := by
    show (3 / 2 : ℝ) < ((m + 1 : ℝ) : ℂ).re
    rw [Complex.ofReal_re]
    linarith [le_max_right σ₀ (3 / 2)]
  have hev : F =ᶠ[nhds ((m + 1 : ℝ) : ℂ)] LSeries a := by
    have hopen : IsOpen {s : ℂ | m < s.re} := isOpen_lt continuous_const Complex.continuous_re
    have hmem : ((m + 1 : ℝ) : ℂ) ∈ {s : ℂ | m < s.re} := by
      show m < ((m + 1 : ℝ) : ℂ).re
      rw [Complex.ofReal_re]
      linarith
    filter_upwards [hopen.mem_nhds hmem] with s hs
    exact hFa s (lt_of_le_of_lt (le_max_left σ₀ (3 / 2)) hs)
  exact fun s hs => hFan.eqOn_of_preconnected_of_eventuallyEq hLa hU hz hev hs

/-! ### `L(f, s)` is the continuation of `L(E, s)` -/

/-- **`L(f, s)` continues `L(E, s)`** (PROVED): if `f` is the newform of `E`, Mathlib's
`ModularForm.L` of `f` is an entire continuation of `L(E, s)` from `Re s > 3/2`
(`IsLContinuation`). It equals `LSeries (nfCoeff f)` on `Re s > 2` (`isEntireContinuation_L`),
which is `LSeries (lcoeff E)` because the coefficients agree for `n ≥ 1` and `LSeries` ignores the
index `0`; `HasseConvergence` and the identity theorem (`eqOn_LSeries_of_forall_summable`) extend
the equality to `Re s > 3/2`. -/
theorem isLContinuation_L_of_isNewformOf (hH : HasseConvergence) {E : WeierstrassCurve ℚ}
    [E.IsElliptic] {N : ℕ} [NeZero N] {f : Newform N 2} (hf : IsNewformOf E f) :
    IsLContinuation E (ModularForm.L two_pos f.toCuspForm) := by
  have hEnt := isEntireContinuation_L two_pos f
  have hLS : ∀ s : ℂ, LSeries (nfCoeff f) s = LSeries (lcoeff E) s := fun s =>
    LSeries_congr (fun {n} hn => hf.2 n (Nat.pos_of_ne_zero hn)) s
  exact isLContinuation_iff.mpr ⟨hEnt.1, eqOn_LSeries_of_forall_summable hEnt.1
    (fun s hs => (hEnt.2 s hs).trans (hLS s)) (hH E inferInstance)⟩

/-- **Every continuation of `L(E, s)` is `L(f, s)`** (PROVED): if `f` is the newform of `E`, any
entire continuation `F` of `L(E, s)` from `Re s > 3/2` is Mathlib's `ModularForm.L` of `f`. On
`Re s > 2` both equal `LSeries (nfCoeff f)`, and Tau Ceti's
`CuspForm.eq_strictWidthInfty_cpow_mul_L` (the identity theorem; width `1` for `Γ₁(N)`)
identifies them everywhere. No convergence hypothesis is needed. -/
theorem eq_L_of_isLContinuation {E : WeierstrassCurve ℚ} {N : ℕ} [NeZero N] {f : Newform N 2}
    (hf : IsNewformOf E f) {F : ℂ → ℂ} (hF : IsLContinuation E F) :
    F = ModularForm.L two_pos f.toCuspForm := by
  have hF' := isLContinuation_iff.mp hF
  have h := CuspForm.eq_strictWidthInfty_cpow_mul_L f.toCuspForm two_pos hF'.1 (fun {s} hs => by
    rw [strictWidthInfty_Gamma1, hF'.2 s (by push_cast at hs; linarith)]
    exact LSeries_congr (fun {n} hn => (hf.2 n (Nat.pos_of_ne_zero hn)).symm) s)
  simpa [strictWidthInfty_Gamma1] using h

/-- **`ord_{s=1} L(E, s)` is the analytic rank of the newform of `E`** (PROVED):
`AnalyticRank E n` holds if and only if Tau Ceti's `Newform.analyticRank f = n`, the order of
vanishing of `ModularForm.L` of `f` at the central point `k/2 = 1`. Every continuation of
`L(E, s)` is `L(f, s)` (`eq_L_of_isLContinuation`), `L(f, s)` is one
(`isLContinuation_L_of_isNewformOf`), and its order at `1` is finite
(`Newform.analyticOrderAt_L_ne_top`). -/
theorem analyticRank_iff_newformAnalyticRank (hH : HasseConvergence) {E : WeierstrassCurve ℚ}
    [E.IsElliptic] {N : ℕ} [NeZero N] {f : Newform N 2} (hf : IsNewformOf E f) (n : ℕ) :
    AnalyticRank E n ↔ f.analyticRank two_pos = n := by
  have hc : ((2 : ℤ) : ℂ) / 2 = 1 := by norm_num
  have hfin := f.analyticOrderAt_L_ne_top two_pos 1
  rw [Newform.analyticRank_def, hc]
  constructor
  · rintro ⟨F, hFd, hFL, hord⟩
    rw [eq_L_of_isLContinuation hf ⟨hFd, hFL⟩] at hord
    rw [analyticOrderNatAt, hord, ENat.toNat_natCast]
  · intro h
    have hcont := isLContinuation_L_of_isNewformOf hH hf
    refine ⟨_, hcont.1, hcont.2, ?_⟩
    rw [← h, Nat.cast_analyticOrderNatAt hfin]

/-- **Analytic rank one of `E` is analytic rank one of its newform** (PROVED): the tree's
`Manuscript.AnalyticRankOne E` holds exactly when Tau Ceti's `Newform.analyticRank f = 1`
(`analyticRank_one_iff` and `analyticRank_iff_newformAnalyticRank`). -/
theorem analyticRankOne_iff_newformAnalyticRank (hH : HasseConvergence)
    {E : WeierstrassCurve ℚ} [E.IsElliptic] {N : ℕ} [NeZero N] {f : Newform N 2}
    (hf : IsNewformOf E f) : AnalyticRankOne E ↔ f.analyticRank two_pos = 1 :=
  (analyticRank_one_iff E).symm.trans (analyticRank_iff_newformAnalyticRank hH hf 1)

/-! ### The functional equation of `L(E, s)` and the root number -/

/-- **The functional equation of `L(E, s)` from the newform of `E`** (PROVED): if `f` is the
newform of `E` (level `N`), then `RootNumberAt E N w` holds with `w` the sign
`i^2 ε_N(f) = -ε_N(f)` of `f`. The entire continuation is Mathlib's `ModularForm.L` of `f`
(`isLContinuation_L_of_isNewformOf`: it equals `LSeries (nfCoeff f) = LSeries (lcoeff E)` on
`Re s > 2`, and `HasseConvergence` with the identity theorem extends this to `Re s > 3/2`); the
functional equation is `newform_functional_equation` at `k = 2`, and `w = ±1` is
`newformSign_eq_one_or_neg_one`. -/
theorem rootNumberAt_of_isNewformOf (hH : HasseConvergence) {E : WeierstrassCurve ℚ}
    [E.IsElliptic] {N : ℕ} [NeZero N] {f : Newform N 2} (hf : IsNewformOf E f) :
    ∃ w : ℤ, (w : ℂ) = newformSign f hf.1 ∧ RootNumberAt E N w := by
  have hcont := isLContinuation_L_of_isNewformOf hH hf
  have hFE := newform_functional_equation_two f hf.1
  obtain ⟨w, hw⟩ : ∃ w : ℤ, (w : ℂ) = newformSign f hf.1 := by
    rcases newformSign_eq_one_or_neg_one f hf.1 with h1 | h1
    · exact ⟨1, by rw [h1, Int.cast_one]⟩
    · exact ⟨-1, by rw [h1, Int.cast_neg, Int.cast_one]⟩
  refine ⟨w, hw, NeZero.pos N, ModularForm.L two_pos f.toCuspForm, hcont, fun s hs0 hs2 => ?_⟩
  rw [hFE s hs0 hs2, hw]

/-- **The root number of `E` is the sign of its newform** (PROVED): `RootNumber E w` for the sign
`w` of the newform of `E` (`rootNumberAt_of_isNewformOf`, forgetting the level). -/
theorem rootNumber_of_isNewformOf (hH : HasseConvergence) {E : WeierstrassCurve ℚ}
    [E.IsElliptic] {N : ℕ} [NeZero N] {f : Newform N 2} (hf : IsNewformOf E f) :
    ∃ w : ℤ, (w : ℂ) = newformSign f hf.1 ∧ RootNumber E w := by
  obtain ⟨w, hw, hN⟩ := rootNumberAt_of_isNewformOf hH hf
  exact ⟨w, hw, rootNumber_iff_exists_rootNumberAt.mpr ⟨N, hN⟩⟩

/-- **Every elliptic curve over `ℚ` has a root number** (PROVED): from `ModularNewform` (a newform
`f` of `E`) and `HasseConvergence`, `RootNumber E w` holds for the sign `w` of `f`
(`rootNumber_of_isNewformOf`). -/
theorem exists_rootNumber (hM : ModularNewform) (hH : HasseConvergence)
    {E : WeierstrassCurve ℚ} (hE : E.IsElliptic) : ∃ w : ℤ, RootNumber E w := by
  obtain ⟨N, _, f, hf⟩ := hM E hE
  obtain ⟨w, -, hw⟩ := rootNumber_of_isNewformOf hH hf
  exact ⟨w, hw⟩

/-! ### Uniqueness of the level and of the sign -/

/-- **Nonvanishing on both sides of the centre** (PROVED): an entire function `F ≢ 0` has some
real `t ∈ (0, 1)` with `F(1 - t) ≠ 0` and `F(1 + t) ≠ 0`. Otherwise every punctured
neighbourhood of `1` would contain zeros, so (isolated zeros) `F` would vanish near `1`, hence
everywhere (identity theorem on `ℂ`). -/
theorem exists_ne_zero_pair {F : ℂ → ℂ} (hF : Differentiable ℂ F) (hF0 : F ≠ 0) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ F (1 - t) ≠ 0 ∧ F (1 + t) ≠ 0 := by
  rcases (hF.analyticAt 1).eventually_eq_zero_or_eventually_ne_zero with h | h
  · have hFa : AnalyticOnNhd ℂ F Set.univ := Complex.analyticOnNhd_univ_iff_differentiable.mpr hF
    refine absurd (funext fun z => ?_) hF0
    exact hFa.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ 1) h
      (Set.mem_univ z)
  · rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at h
    obtain ⟨ε, hε, hball⟩ := h
    have ht0 : 0 < min (ε / 2) (1 / 2) := lt_min (half_pos hε) (by norm_num)
    have htε : min (ε / 2) (1 / 2) < ε := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε)
    have ht1 : min (ε / 2) (1 / 2) < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
    set t := min (ε / 2) (1 / 2)
    have hnorm : ‖(t : ℂ)‖ = t := by rw [Complex.norm_real, Real.norm_of_nonneg ht0.le]
    have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
    refine ⟨t, ht0, ht1, hball ?_ ?_, hball ?_ ?_⟩
    · rw [Complex.dist_eq, show (1 - (t : ℂ)) - 1 = -(t : ℂ) by ring, norm_neg, hnorm]
      exact htε
    · exact Set.mem_compl_singleton_iff.mpr fun h1 => htc (by linear_combination -h1)
    · rw [Complex.dist_eq, show (1 + (t : ℂ)) - 1 = (t : ℂ) by ring, hnorm]
      exact htε
    · exact Set.mem_compl_singleton_iff.mpr fun h1 => htc (by linear_combination h1)

/-- The completed function split as `Λ_N(s) = N^{s/2} · ((2π)^{-s} Γ(s) F(s))` (PROVED). -/
theorem completedL_eq_mul (N : ℕ) (F : ℂ → ℂ) (s : ℂ) :
    completedL N F s =
      (N : ℂ) ^ (s / 2) * ((2 * Real.pi : ℂ) ^ (-s) * Complex.Gamma s * F s) := by
  unfold completedL
  ring

/-- **A nonzero entire function has at most one level and one sign** (PROVED). If `F ≢ 0` is
entire and `Λ_N(2 - s) = w Λ_N(s)`, `Λ_{N'}(2 - s) = w' Λ_{N'}(s)` on the strip `0 < Re s < 2`
(`Λ_N = completedL N F`), then `N = N'` and `w = w'`. Take real `t ∈ (0, 1)` with
`F(1 ± t) ≠ 0` (`exists_ne_zero_pair`). Applying each equation at `1 - t` and `1 + t` gives
`w² = w'² = 1`; dividing the two equations at `1 - t` gives
`w N'^{(1+t)/2} N^{(1-t)/2} = w' N^{(1+t)/2} N'^{(1-t)/2}` with positive real powers, so `w = w'`
(signs) and then `t log N' = t log N`, i.e. `N = N'`. -/
theorem level_sign_unique {F : ℂ → ℂ} (hF : Differentiable ℂ F) (hF0 : F ≠ 0) {N N' : ℕ}
    (hN : 0 < N) (hN' : 0 < N') {w w' : ℂ}
    (h1 : ∀ s : ℂ, 0 < s.re → s.re < 2 → completedL N F (2 - s) = w * completedL N F s)
    (h2 : ∀ s : ℂ, 0 < s.re → s.re < 2 → completedL N' F (2 - s) = w' * completedL N' F s) :
    N = N' ∧ w = w' := by
  obtain ⟨t, ht0, ht1, hFm, hFp⟩ := exists_ne_zero_pair hF hF0
  have hre1 : (1 - (t : ℂ)).re = 1 - t := by simp
  have hre2 : (1 + (t : ℂ)).re = 1 + t := by simp
  have hs0 : 0 < (1 - (t : ℂ)).re := by rw [hre1]; linarith
  have hs2 : (1 - (t : ℂ)).re < 2 := by rw [hre1]; linarith
  have hr0 : 0 < (1 + (t : ℂ)).re := by rw [hre2]; linarith
  have hr2 : (1 + (t : ℂ)).re < 2 := by rw [hre2]; linarith
  have e1 := h1 _ hs0 hs2
  have e2 := h1 _ hr0 hr2
  have e1' := h2 _ hs0 hs2
  have e2' := h2 _ hr0 hr2
  rw [show 2 - (1 - (t : ℂ)) = 1 + t by ring] at e1 e1'
  rw [show 2 - (1 + (t : ℂ)) = 1 - t by ring] at e2 e2'
  -- the squares of the signs
  have hQ : completedL N F (1 + t) ≠ 0 := mul_ne_zero (completedL_factor_ne_zero hN hr0) hFp
  have hQ' : completedL N' F (1 + t) ≠ 0 := mul_ne_zero (completedL_factor_ne_zero hN' hr0) hFp
  have hww : w * w = 1 := by
    have h : (w * w - 1) * completedL N F (1 + t) = 0 := by linear_combination -e1 - w * e2
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hQ)
  have hww' : w' * w' = 1 := by
    have h : (w' * w' - 1) * completedL N' F (1 + t) = 0 := by
      linear_combination -e1' - w' * e2'
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hQ')
  -- the level factors are positive reals
  have hpi0 : (2 * Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)
  have hv : (2 * (Real.pi : ℂ)) ^ (-(1 - (t : ℂ))) * Complex.Gamma (1 - t) * F (1 - t) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero ?_ (Complex.Gamma_ne_zero_of_re_pos hs0)) hFm
    exact fun h => hpi0 ((Complex.cpow_eq_zero_iff _ _).mp h).1
  simp only [completedL_eq_mul] at e1 e1'
  generalize (2 * (Real.pi : ℂ)) ^ (-(1 + (t : ℂ))) * Complex.Gamma (1 + t) * F (1 + t) = u
    at e1 e1'
  generalize (2 * (Real.pi : ℂ)) ^ (-(1 - (t : ℂ))) * Complex.Gamma (1 - t) * F (1 - t) = v
    at e1 e1' hv
  have hcpow : ∀ (M : ℕ) (x : ℝ), (M : ℂ) ^ (x : ℂ) = (((M : ℝ) ^ x : ℝ) : ℂ) := fun M x => by
    rw [Complex.ofReal_cpow (Nat.cast_nonneg M), Complex.ofReal_natCast]
  rw [show (1 + (t : ℂ)) / 2 = (((1 + t) / 2 : ℝ) : ℂ) by push_cast; ring,
    show (1 - (t : ℂ)) / 2 = (((1 - t) / 2 : ℝ) : ℂ) by push_cast; ring, hcpow, hcpow] at e1 e1'
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hN'r : (0 : ℝ) < N' := Nat.cast_pos.mpr hN'
  have hα := Real.rpow_pos_of_pos hNr ((1 + t) / 2)
  have hβ := Real.rpow_pos_of_pos hNr ((1 - t) / 2)
  have hα' := Real.rpow_pos_of_pos hN'r ((1 + t) / 2)
  have hβ' := Real.rpow_pos_of_pos hN'r ((1 - t) / 2)
  have hrel : w * ((((N' : ℝ) ^ ((1 + t) / 2) * (N : ℝ) ^ ((1 - t) / 2) : ℝ)) : ℂ) =
      w' * ((((N : ℝ) ^ ((1 + t) / 2) * (N' : ℝ) ^ ((1 - t) / 2) : ℝ)) : ℂ) := by
    have h : (w * ((((N' : ℝ) ^ ((1 + t) / 2) * (N : ℝ) ^ ((1 - t) / 2) : ℝ)) : ℂ) -
        w' * ((((N : ℝ) ^ ((1 + t) / 2) * (N' : ℝ) ^ ((1 - t) / 2) : ℝ)) : ℂ)) * v = 0 := by
      push_cast
      linear_combination (((N : ℝ) ^ ((1 + t) / 2) : ℝ) : ℂ) * e1' -
        (((N' : ℝ) ^ ((1 + t) / 2) : ℝ) : ℂ) * e1
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hv)
  have hpos1 := mul_pos hα' hβ
  have hpos2 := mul_pos hα hβ'
  -- the signs agree
  have hwe : w = w' := by
    rcases mul_self_eq_one_iff.mp hww with rfl | rfl <;>
      rcases mul_self_eq_one_iff.mp hww' with rfl | rfl
    · rfl
    · exfalso
      have h : (((N' : ℝ) ^ ((1 + t) / 2) * (N : ℝ) ^ ((1 - t) / 2) : ℝ) : ℂ) =
          (((-((N : ℝ) ^ ((1 + t) / 2) * (N' : ℝ) ^ ((1 - t) / 2))) : ℝ) : ℂ) := by
        rw [Complex.ofReal_neg]
        linear_combination hrel
      have h' := Complex.ofReal_injective h
      linarith
    · exfalso
      have h : (((N' : ℝ) ^ ((1 + t) / 2) * (N : ℝ) ^ ((1 - t) / 2) : ℝ) : ℂ) =
          (((-((N : ℝ) ^ ((1 + t) / 2) * (N' : ℝ) ^ ((1 - t) / 2))) : ℝ) : ℂ) := by
        rw [Complex.ofReal_neg]
        linear_combination -hrel
      have h' := Complex.ofReal_injective h
      linarith
    · rfl
  -- the levels agree
  have hw0 : w ≠ 0 := by
    rintro rfl
    simp at hww
  rw [← hwe] at hrel
  have hreal := Complex.ofReal_injective (mul_left_cancel₀ hw0 hrel)
  have hlog := congrArg Real.log hreal
  rw [Real.log_mul hα'.ne' hβ.ne', Real.log_mul hα.ne' hβ'.ne'] at hlog
  simp only [Real.log_rpow hNr, Real.log_rpow hN'r] at hlog
  have hlogeq : Real.log N' = Real.log N := by
    have h : t * (Real.log N' - Real.log N) = 0 := by linear_combination hlog
    have := (mul_eq_zero.mp h).resolve_left ht0.ne'
    linarith
  have hNN : (N' : ℝ) = N :=
    Real.log_injOn_pos (Set.mem_Ioi.mpr hN'r) (Set.mem_Ioi.mpr hNr) hlogeq
  exact ⟨by exact_mod_cast hNN.symm, hwe⟩

/-- **The level and the sign of any functional equation of `L(E, s)` are those of the newform of
`E`** (PROVED): if `f : Newform M 2` is the newform of `E` and `RootNumberAt E N w`, then `N = M`
and `w = i^2 ε_M(f)`. The continuation in `RootNumberAt` is `L(f, s)` (`eq_L_of_isLContinuation`),
which is not identically zero (`Newform.L_ne_zero`: `a₁ = 1`) and satisfies the functional
equation of level `M` with the sign of `f` (`newform_functional_equation_two`); conclude by
`level_sign_unique`. No convergence hypothesis is needed. -/
theorem eq_level_and_sign_of_rootNumberAt {E : WeierstrassCurve ℚ} {M : ℕ} [NeZero M]
    {f : Newform M 2} (hf : IsNewformOf E f) {N : ℕ} {w : ℤ} (h : RootNumberAt E N w) :
    N = M ∧ (w : ℂ) = newformSign f hf.1 := by
  obtain ⟨hN, F, hF, hFE⟩ := h
  rw [eq_L_of_isLContinuation hf hF] at hFE
  exact level_sign_unique (CuspForm.differentiable_L two_pos f.toCuspForm) (f.L_ne_zero two_pos)
    hN (NeZero.pos M) hFE (newform_functional_equation_two f hf.1)

/-- An integer equal to the sign of a newform is `1` or `-1` (PROVED). -/
theorem int_eq_one_or_neg_one_of_cast_eq_newformSign {M : ℕ} [NeZero M] {k : ℤ}
    {f : Newform M k} {hχ : f.χ = 1} {w : ℤ} (hw : (w : ℂ) = newformSign f hχ) :
    w = 1 ∨ w = -1 := by
  rcases newformSign_eq_one_or_neg_one f hχ with h | h
  · left
    exact_mod_cast hw.trans h
  · right
    exact_mod_cast hw.trans h

/-- **Uniqueness of the level and of the root number** (PROVED): under `ModularNewform`, any two
functional equations of `L(E, s)` (`RootNumberAt`) have the same level and the same sign
(`eq_level_and_sign_of_rootNumberAt` for the newform of `E`). -/
theorem rootNumberAt_unique (hM : ModularNewform) {E : WeierstrassCurve ℚ} (hE : E.IsElliptic)
    {N N' : ℕ} {w w' : ℤ} (h : RootNumberAt E N w) (h' : RootNumberAt E N' w') :
    N = N' ∧ w = w' := by
  obtain ⟨M, _, f, hf⟩ := hM E hE
  obtain ⟨hN, hw⟩ := eq_level_and_sign_of_rootNumberAt hf h
  obtain ⟨hN', hw'⟩ := eq_level_and_sign_of_rootNumberAt hf h'
  exact ⟨hN.trans hN'.symm, by exact_mod_cast hw.trans hw'.symm⟩

/-- **The root number is unique** (PROVED): under `ModularNewform`, `RootNumber E w` and
`RootNumber E w'` force `w = w'` (`rootNumberAt_unique`). -/
theorem rootNumber_unique (hM : ModularNewform) {E : WeierstrassCurve ℚ} (hE : E.IsElliptic)
    {w w' : ℤ} (h : RootNumber E w) (h' : RootNumber E w') : w = w' := by
  obtain ⟨N, hN⟩ := rootNumber_iff_exists_rootNumberAt.mp h
  obtain ⟨N', hN'⟩ := rootNumber_iff_exists_rootNumberAt.mp h'
  exact (rootNumberAt_unique hM hE hN hN').2

/-- **A root number is `±1`** (PROVED): under `ModularNewform`, `RootNumber E w` forces
`w = 1 ∨ w = -1`, since `w` is the sign of the newform of `E`
(`eq_level_and_sign_of_rootNumberAt`, `newformSign_eq_one_or_neg_one`). -/
theorem rootNumber_eq_one_or_neg_one (hM : ModularNewform) {E : WeierstrassCurve ℚ}
    (hE : E.IsElliptic) {w : ℤ} (h : RootNumber E w) : w = 1 ∨ w = -1 := by
  obtain ⟨M, _, f, hf⟩ := hM E hE
  obtain ⟨N, hN⟩ := rootNumber_iff_exists_rootNumberAt.mp h
  exact int_eq_one_or_neg_one_of_cast_eq_newformSign (eq_level_and_sign_of_rootNumberAt hf hN).2

/-! ### Quadratic twists -/

/-- **A fundamental discriminant is nonzero** (PROVED): `0 ≢ 1 (mod 4)`, and `0 = 4m` forces
`m = 0 ≢ 2, 3 (mod 4)`. -/
theorem IsFundamentalDiscriminant.ne_zero {D : ℤ} (hD : IsFundamentalDiscriminant D) : D ≠ 0 := by
  rintro rfl
  rcases hD with ⟨-, ⟨h, -⟩ | ⟨m, hm, hm4, -⟩⟩ <;> omega

/-- **An entire continuation of `L(s, f, χ_D)` continues `L(E^{(D)}, s)`** (PROVED): if `f` is the
newform of `E` (level `N`), `D` is a fundamental discriminant prime to `N`, and `F` is an entire
continuation of `∑ χ_D(n) a_n(f) n^{-s}` from any half-plane `Re s > σ₀`, then `F` is an entire
continuation of `L(E^{(D)}, s)` from `Re s > 3/2` (`IsLContinuation (qtwist E D) F`). By
`IsNewformOf` and `TwistDictionary` the twisted coefficients of `f` are those of `E^{(D)}` for
`n ≥ 1`, so the two Dirichlet series are the same function; `E^{(D)}` is elliptic since `D ≠ 0`,
so `HasseConvergence` applies to it, and the identity theorem
(`eqOn_LSeries_of_forall_summable`) moves the equality from `Re s > σ₀` to `Re s > 3/2`. -/
theorem isLContinuation_qtwist (hT : TwistDictionary) (hH : HasseConvergence)
    {E : WeierstrassCurve ℚ} [E.IsElliptic] {N : ℕ} [NeZero N] {f : Newform N 2}
    (hf : IsNewformOf E f) {D : ℤ} (hD : IsFundamentalDiscriminant D) (hDN : IsCoprime D (N : ℤ))
    {σ₀ : ℝ} {F : ℂ → ℂ} (hF : IsEntireContinuation (twistCoeff (nfCoeff f) D) σ₀ F) :
    IsLContinuation (qtwist E D) F := by
  have hD0 : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne_zero
  have : (qtwist E D).IsElliptic := qtwist_isElliptic hD0
  have hcoef : ∀ {n : ℕ}, n ≠ 0 → twistCoeff (nfCoeff f) D n = lcoeff (qtwist E D) n := by
    intro n hn
    rw [hT E inferInstance N f hf D hD hDN n (Nat.pos_of_ne_zero hn)]
    simp only [twistCoeff, hf.2 n (Nat.pos_of_ne_zero hn)]
  exact isLContinuation_iff.mpr ⟨hF.1, eqOn_LSeries_of_forall_summable hF.1
    (fun s hs => (hF.2 s hs).trans (LSeries_congr hcoef s)) (hH _ inferInstance)⟩

/-! ### Hoffstein–Luo for elliptic curves -/

/-- **Hoffstein–Luo for an elliptic curve, from the print** (PROVED): `HoffsteinLuoTheorem` (the
print, for newforms) with `ModularNewform`, `TwistDictionary` and `HasseConvergence` gives
`HoffsteinLuoCurve`. For `A` elliptic, take its newform `f` (weight `2`, trivial nebentypus); each
discriminant `d` supplied by the print for `f` and `S` is prime to the level and has an entire
continuation `F` of `L(s, f, χ_d)` with `F(1) ≠ 0`; by `isLContinuation_qtwist`, `F` continues
`L(A^{(d)}, s)`, so `ord_{s=1} L(A^{(d)}, s) = 0` (`analyticRank_zero_iff`). The print's infinite
set is contained in the curve form's set. -/
theorem hoffsteinLuoCurve_of (hHL : HoffsteinLuoTheorem) (hM : ModularNewform)
    (hT : TwistDictionary) (hH : HasseConvergence) : HoffsteinLuoCurve := by
  intro A hA S hS
  obtain ⟨N, _, f, hf⟩ := hM A hA
  refine (hHL N 2 f hf.1 le_rfl S hS).mono ?_
  rintro d ⟨hd, hodd, hdN, hω, hsplit, F, hF, hF1⟩
  have hc : ((2 : ℤ) : ℂ) / 2 = 1 := by norm_num
  rw [hc] at hF1
  exact ⟨hd, hodd, hω, hsplit,
    analyticRank_zero_iff.mpr ⟨F, isLContinuation_qtwist hT hH hf hd hdN hF, hF1⟩⟩

/-! ### The twisted functional equation for elliptic curves -/

/-- **The twisted functional equation for an elliptic curve, from the print** (PROVED):
`TwistedFunctionalEquation` (Hecke's functional equation of `L(s, f, χ_D)` for newforms) with
`ModularNewform`, `TwistDictionary` and `HasseConvergence` gives `TwistedRootNumberCurve`. If
`RootNumberAt A N w`, then `N` is the level of the newform `f` of `A` and `w` its sign
(`eq_level_and_sign_of_rootNumberAt`); the print gives an entire continuation `F` of
`L(s, f, χ_D)` with `Λ_{D²N}(2 - s) = w χ_D(-N) Λ_{D²N}(s)` on the strip, and `F` continues
`L(A^{(D)}, s)` (`isLContinuation_qtwist`). -/
theorem twistedRootNumberCurve_of (hTFE : TwistedFunctionalEquation) (hM : ModularNewform)
    (hT : TwistDictionary) (hH : HasseConvergence) : TwistedRootNumberCurve := by
  intro A hA N w hAw D hD hDN
  obtain ⟨M, _, f, hf⟩ := hM A hA
  obtain ⟨hNM, hw⟩ := eq_level_and_sign_of_rootNumberAt hf hAw
  rw [hNM] at hDN ⊢
  obtain ⟨F, hF, hFE⟩ := hTFE M 2 f hf.1 two_pos D hD hDN
  refine ⟨Nat.mul_pos (pow_pos (Int.natAbs_pos.mpr hD.ne_zero) 2) (NeZero.pos M), F,
    isLContinuation_qtwist hT hH hf hD hDN hF, fun s hs0 hs2 => ?_⟩
  have h := hFE s hs0 (by exact_mod_cast hs2)
  rw [show ((2 : ℤ) : ℂ) = 2 by norm_num] at h
  rw [Int.cast_mul, hw]
  exact h

/-! ### Bump–Friedberg–Hoffstein for elliptic curves -/

/-- **A prime dividing `D` is ramified** (PROVED): for a prime `p` with `p ∣ D`, the Kronecker
symbol `(D/p)` is `0`: at `p = 2` because `D` is even, at odd `p` because the Jacobi symbol
`J(D | p)` vanishes when `gcd(D, p) ≠ 1`. -/
theorem kronecker_eq_zero_of_dvd {D : ℤ} {p : ℕ} (hp : p.Prime) (hpD : (p : ℤ) ∣ D) :
    kronecker D p = 0 := by
  by_cases hp2 : p = 2
  · subst hp2
    have h2 : D % 2 = 0 := Int.emod_eq_zero_of_dvd hpD
    simp only [kronecker, Nat.Prime.factorization_self Nat.prime_two, pow_one,
      Nat.div_self (show 0 < 2 by norm_num), jacobiSym.one_right, mul_one, kroneckerTwo, h2,
      ite_true]
  · have hf : p.factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd fun h2 =>
      hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2).symm
    simp only [kronecker, hf, pow_zero, one_mul, Nat.div_one]
    refine jacobiSym.eq_zero_iff.mpr ⟨hp.ne_zero, fun hg => hp.one_lt.ne' ?_⟩
    have hdvd := Int.dvd_gcd hpD (dvd_refl (p : ℤ))
    rw [hg] at hdvd
    exact Nat.dvd_one.mp hdvd

/-- **Splitting at every prime of `M` makes `D` prime to `M`** (PROVED): if `(D/p) = 1` for every
prime `p ∣ M`, then `gcd(D, M) = 1` (`kronecker_eq_zero_of_dvd`). -/
theorem isCoprime_of_forall_kronecker_eq_one {D : ℤ} {M : ℕ}
    (h : ∀ p : ℕ, p.Prime → p ∣ M → kronecker D p = 1) : IsCoprime D (M : ℤ) := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  show Nat.gcd D.natAbs M = 1
  refine Nat.coprime_of_dvd fun p hp hpD hpM => ?_
  have h1 := h p hp hpM
  rw [kronecker_eq_zero_of_dvd hp (Int.natCast_dvd.mpr hpD)] at h1
  exact absurd h1 (by norm_num)

/-- **Bump–Friedberg–Hoffstein for an elliptic curve, from the print** (PROVED): `BFHTheorem`
(clauses (i) and (ii) for newforms) with `ModularNewform`, `TwistDictionary` and
`HasseConvergence` gives `BFHCurve`. If `RootNumberAt A N w`, then `N` is the level of the newform
`f` of `A` and `w = ±1` its sign (`eq_level_and_sign_of_rootNumberAt`), so the hypothesis on `S`
is the print's and the print's sign conditions are `wD < 0` resp. `wD > 0`. Each `D` it supplies
splits at every prime of `S ⊇ {p ∣ N}`, hence is prime to `N`
(`isCoprime_of_forall_kronecker_eq_one`), so its `L(s, f, χ_D)` continues `L(A^{(D)}, s)`
(`isLContinuation_qtwist`): a simple zero at `s = 1` is `ord_{s=1} L(A^{(D)}, s) = 1`, a nonzero
value is `ord_{s=1} L(A^{(D)}, s) = 0`. -/
theorem bfhCurve_of (hB : BFHTheorem) (hM : ModularNewform) (hT : TwistDictionary)
    (hH : HasseConvergence) : BFHCurve := by
  intro A hA N w hAw S hS hSN
  obtain ⟨M, _, f, hf⟩ := hM A hA
  obtain ⟨hNM, hw⟩ := eq_level_and_sign_of_rootNumberAt hf hAw
  rw [hNM] at hSN
  have hcop : ∀ D : ℤ, (∀ p ∈ S, kronecker D p = 1) → IsCoprime D (M : ℤ) := fun D hD =>
    isCoprime_of_forall_kronecker_eq_one fun p hp hpM => hD p (hSN p hp hpM)
  have hc : ((2 : ℤ) : ℂ) / 2 = 1 := by norm_num
  obtain ⟨⟨D₁, hD₁, hs₁, hs₁', hsp₁, F₁, hF₁, hord₁⟩, ⟨D₂, hD₂, hs₂, hs₂', hsp₂, F₂, hF₂, hval₂⟩⟩ :=
    hB M 2 f hf.1 two_pos even_two S hS hSN
  rw [hc] at hord₁ hval₂
  have hw1 := int_eq_one_or_neg_one_of_cast_eq_newformSign hw
  refine ⟨⟨D₁, hD₁, ?_, hsp₁, ?_⟩, ⟨D₂, hD₂, ?_, hsp₂, ?_⟩⟩
  · rcases hw1 with rfl | rfl
    · have := hs₁ (by rw [← hw, Int.cast_one])
      linarith
    · have := hs₁' (by rw [← hw, Int.cast_neg, Int.cast_one])
      linarith
  · have hcont := isLContinuation_qtwist hT hH hf hD₁ (hcop D₁ hsp₁) hF₁
    exact ⟨F₁, hcont.1, hcont.2, by rw [Nat.cast_one]; exact hord₁⟩
  · rcases hw1 with rfl | rfl
    · have := hs₂ (by rw [← hw, Int.cast_one])
      linarith
    · have := hs₂' (by rw [← hw, Int.cast_neg, Int.cast_one])
      linarith
  · exact analyticRank_zero_iff.mpr
      ⟨F₂, isLContinuation_qtwist hT hH hf hD₂ (hcop D₂ hsp₂) hF₂, hval₂⟩

end ZInQ.Manuscript.RC.PrintsAnalytic
